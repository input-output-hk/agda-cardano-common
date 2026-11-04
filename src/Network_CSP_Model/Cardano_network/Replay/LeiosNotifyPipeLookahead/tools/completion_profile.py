#!/usr/bin/env python3
"""Phase-separated profiles of unchanged pinned drivers and a diagnostic counter getter.

Baseline binaries contain unmodified pinned peer/Core/driver/limits sources.
Diagnostic binaries append a copy of the fixed-sender entry point with a getter;
those samples are reported separately and are not baseline performance evidence.
"""
import argparse
import difflib
import importlib.util
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / "src/csp-ptree.agda-lib").is_file())


def helpers():
    spec = importlib.util.spec_from_file_location("history_helpers", HERE / "completion_history.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def diagnostic_driver(path):
    """Keep original function bodies, adding one copied entry point and an export."""
    original = path.read_text()
    name = "runLookaheadFixedSenderPeerWithDriver"
    diagnostic = "runLookaheadFixedSenderPeerWithCounters"
    marker = name + "\n  ::"
    assert original.count(marker) == 1 and original.count("  , " + name + "\n") == 1
    function = original[original.index(marker):]
    assert function.endswith("        Right a -> return a\n")
    copied = function.replace(name, diagnostic)
    signature = "  => Driver ps pr dstate m\n"
    assert copied.count(signature) == 1
    copied = copied.replace(signature, "  => (STM m (Natural, Natural) -> m ())\n  -> Driver ps pr dstate m\n")
    copied = copied.replace(diagnostic + " driver@", diagnostic + " exposeCounters driver@")
    creation = "    doneVar <- newTVarIO 0\n"
    assert copied.count(creation) == 1
    copied = copied.replace(creation, creation + "    exposeCounters ((,) <$> readTVar sendVar <*> readTVar doneVar)\n")
    patched = original.replace("  , " + name + "\n", "  , " + name + "\n  , " + diagnostic + "\n")
    patched += "\n-- Diagnostic entry point: expose a getter once, without per-job instrumentation.\n" + copied
    # The original functions and counter-update code must remain byte-identical.
    assert patched.replace("  , " + diagnostic + "\n", "").split("\n-- Diagnostic entry point:")[0] == original
    path.write_text(patched)
    return "".join(difflib.unified_diff(original.splitlines(True), patched.splitlines(True),
                                        fromfile="pinned/Driver.hs", tofile="diagnostic/Driver.hs"))


def build(args, out, optimization, mode, h):
    """Use the original export/build path and record the diagnostic delta separately."""
    fixture = h.load_fixture()
    prepare_original = fixture.prepare
    provenance = {}

    def prepare(arguments, destination):
        src, typed, network = prepare_original(arguments, destination)
        path = typed / "src/Network/TypedProtocol/Driver.hs"
        provenance["original_driver_sha256"] = h.file_hash(path)
        if mode == "diagnostic":
            delta = diagnostic_driver(path)
            (destination / "diagnostic-driver.patch").write_text(delta)
        provenance["compiled_driver_sha256"] = h.file_hash(path)
        return src, typed, network

    def command(argv, log, cwd=None, timeout=300):
        is_compiler = str(argv[0]) == "ghc"
        if is_compiler:
            argv = [optimization if x == "-O0" else x for x in argv]
            if mode == "diagnostic":
                argv += ["-DCOMPLETION_DIAGNOSTIC"]
        stats = h.bounded_command(argv, log, cwd=cwd, timeout=timeout)
        if is_compiler:
            (out / "ghc-command.json").write_text(json.dumps(stats["argv"], indent=2) + "\n")
        return stats

    fixture.prepare, fixture.command = prepare, command
    out.mkdir(parents=True, exist_ok=False)
    version = fixture.build(args, out, main_source=HERE / "CompletionProfile.hs", executable="profile")
    if mode == "baseline":
        assert provenance["original_driver_sha256"] == provenance["compiled_driver_sha256"]
    provenance.update(compiler=version, optimization=optimization, mode=mode,
                      command_sha256=h.file_hash(out / "ghc-command.json"),
                      exported_source_hashes_sha256=h.file_hash(out / "source-hashes.json"))
    if mode == "diagnostic":
        provenance["diagnostic_patch_sha256"] = h.file_hash(out / "diagnostic-driver.patch")
    return provenance


def validate(path, exchanges, depth, mode, h):
    values, builds, passed = {}, [], 0
    for line in path.read_text().splitlines():
        parts = line.split("\t")
        if parts == ["PASS"]:
            passed += 1
        elif len(parts) == 2 and parts[0] == "BUILD":
            builds.append(parts[1])
        else:
            h.require(len(parts) == 3 and parts[0] == "M" and parts[1] not in values, "invalid profile field")
            values[parts[1]] = int(parts[2])
    h.require(builds == [mode] and passed == 1, "missing or wrong build/outcome")
    h.require(values["exchanges"] == exchanges and values["depth"] == depth, "wrong profile configuration")
    for key in ["request_sends", "request_receives", "reply_sends", "reply_receives", "handled"]:
        h.require(values[key] == exchanges, "incomplete exchange history")
    h.require(values["free_credits"] == 0 and values["shutdown_ns"] > 0, "invalid completion")
    h.require(values["allocated_post_bytes"] >= values["allocated_pre_bytes"] and
              values["shutdown_allocated_bytes"] == values["allocated_post_bytes"] - values["allocated_pre_bytes"], "allocation delta mismatch")
    h.require(values["pre_gc_generation"] == 1 and values["post_gc_generation"] == 1 and
              values["post_major_gcs"] > values["pre_major_gcs"] >= 1, "major-GC checkpoint missing")
    h.require(values["max_live_bytes"] >= max(values["pre_live_bytes"], values["post_live_bytes"]), "invalid heap sample")
    private = {k: v for k, v in values.items() if k.startswith("private_")}
    if mode == "diagnostic":
        h.require(private == {"private_pre_waiting": 0, "private_pre_completed": exchanges,
                              "private_post_waiting": 0, "private_post_completed": 0}, "private counters did not drain")
    else:
        h.require(not private, "private probes in baseline")
    return values


def summarize(runs):
    result = []
    keys = sorted({(r["optimization"], r["mode"], r["capabilities"], r["exchanges"], r["depth"]) for r in runs})
    for opt, mode, caps, n, depth in keys:
        samples = [r["measurements"] for r in runs if
                   (r["optimization"], r["mode"], r["capabilities"], r["exchanges"], r["depth"]) == (opt, mode, caps, n, depth)]
        row = {"optimization": opt, "mode": mode, "capabilities": caps, "exchanges": n,
               "depth": depth, "samples": len(samples)}
        for field in ["shutdown_ns", "pre_live_bytes", "post_live_bytes", "shutdown_allocated_bytes", "allocated_post_bytes"]:
            xs = [sample[field] for sample in samples]
            row[field] = {"min": min(xs), "median": statistics.median(xs), "max": max(xs)}
        result.append(row)
    return result


def negative_controls(report, out, h):
    """Reject corrupted timing/GC/private-counter evidence from real samples."""
    baseline = next(r for r in report["runs"] if r["mode"] == "baseline")
    diagnostic = next(r for r in report["runs"] if r["mode"] == "diagnostic")
    results = []
    for name, sample, field, replacement in [
        ("negative-time", baseline, "shutdown_ns", -1),
        ("missing-major-gc", baseline, "pre_gc_generation", 0),
        ("bad-allocation-delta", baseline, "shutdown_allocated_bytes", -1),
        ("bad-private-completed", diagnostic, "private_pre_completed", diagnostic["exchanges"] + 1),
    ]:
        data = (out / (sample["name"] + ".tsv")).read_text()
        prefix = "M\t" + field + "\t"
        mutated = "\n".join(prefix + str(replacement) if line.startswith(prefix) else line
                            for line in data.splitlines()) + "\n"
        h.require(mutated != data, "negative control did not mutate a sample")
        path = out / ("negative-" + name + ".tsv")
        path.write_text(mutated)
        try:
            validate(path, sample["exchanges"], sample["depth"], sample["mode"], h)
        except ValueError as error:
            results.append({"name": name, "fixture_validation_rejected": True, "reason": str(error),
                            "capture_sha256": h.file_hash(path)})
        else:
            raise ValueError(f"negative control accepted: {name}")
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--consensus", type=Path, required=True)
    parser.add_argument("--typed-protocols", type=Path, required=True)
    parser.add_argument("--network-archive", type=Path, required=True)
    parser.add_argument("--package-db", type=Path, default=Path.home() / ".cabal/store/ghc-9.6.7/package.db")
    parser.add_argument("--build-packages", type=Path, default=HERE / "build-packages.json")
    parser.add_argument("--counts", nargs="+", type=int, default=[0, 1000, 10000, 100000])
    parser.add_argument("--optimizations", nargs="+", choices=["O0", "O2"], default=["O0", "O2"])
    parser.add_argument("--capabilities", nargs="+", type=int, choices=[1, 2], default=[1, 2])
    parser.add_argument("--depths", nargs="+", type=int, choices=[1, 1000], default=[1000])
    parser.add_argument("--repeat", type=int, default=5)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    h = helpers()
    out = args.out.resolve()
    h.require(not out.is_relative_to(ROOT), "artifacts must stay outside repository")
    h.require(args.repeat > 0 and args.counts and all(0 <= n <= 1000000 for n in args.counts), "invalid history sizes")
    for values in [args.counts, args.optimizations, args.capabilities, args.depths]:
        h.require(len(values) == len(set(values)), "duplicate sweep value")
    out.mkdir(parents=True, exist_ok=False)
    paths = [Path(__file__), HERE / "CompletionProfile.hs", HERE / "completion_history.py", HERE / "run.py", args.build_packages]
    report = {"scope": "T5.1.2 quiet controlled-fixture measurements; separate baseline and diagnostic builds",
              "system": {"uname": list(platform.uname()), "cpu_count": os.cpu_count(),
                         "GHCRTS": os.environ.get("GHCRTS"), "load_average_before": os.getloadavg(),
                         "cpu_model": next((line.split(":", 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')), 'unknown')},
              "source_hashes": {str(p.resolve().relative_to(ROOT)) if p.resolve().is_relative_to(ROOT) else str(p.resolve()): h.file_hash(p) for p in paths},
              "timing_boundary": "release of final checkDone gate through successful return of both limits-driver calls; logging and explicit major GCs excluded",
              "allocation_boundary": "allocated_bytes delta between pre-Quit major GC and post-driver major GC; includes fixed controller/Async/GC bookkeeping",
              "live_heap": "gcdetails_live_bytes at explicit pre-Quit and post-driver major GCs; whole fixture, not object attribution",
              "diagnostic": "extra entry point exposes original sendVar/doneVar getter once; no per-flush observer; diagnostic precondition waits for all n retirements",
              "baseline": "pinned sources unchanged; readiness observes replies/handlers and may leave the last sender retirement pending",
              "stats_reference": "https://downloads.haskell.org/ghc/9.6.7/docs/libraries/base-4.18.3.0/GHC-Stats.html",
              "builds": [], "runs": [], "complete": False}
    for optimization in args.optimizations:
        binaries = {}
        for mode in ["baseline", "diagnostic"]:
            build_out = out / f"{mode}-{optimization}"
            report["builds"].append(build(args, build_out, "-" + optimization, mode, h))
            binaries[mode] = build_out / "profile"
        for caps in args.capabilities:
            for depth in args.depths:
                for n in args.counts:
                    for repeat in range(args.repeat):
                        # Alternate ordering to avoid putting every diagnostic run later.
                        modes = ["baseline", "diagnostic"] if repeat % 2 == 0 else ["diagnostic", "baseline"]
                        for mode in modes:
                            name = f"{optimization}-N{caps}-d{depth}-n{n}-r{repeat}-{mode}"
                            log = out / (name + ".tsv")
                            resources = h.bounded_command([binaries[mode], n, depth, "+RTS", f"-N{caps}",
                                                           "-T", "-M256M", "-K64M", "-RTS"], log, timeout=150)
                            values = validate(log, n, depth, mode, h)
                            report["runs"].append({"name": name, "optimization": "-" + optimization, "mode": mode,
                                                   "capabilities": caps, "depth": depth, "exchanges": n, "repeat": repeat,
                                                   "measurements": values, "resources": resources, "capture_sha256": h.file_hash(log)})
                            (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
                    print(f"{optimization} N{caps} depth={depth} n={n}: quiet baseline/diagnostic passed", flush=True)
    report["summary"] = summarize(report["runs"])
    report["negative_controls"] = negative_controls(report, out, h)
    report["system"]["load_average_after"] = os.getloadavg()
    report["complete"] = True
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"report: {out / 'report.json'}", flush=True)


if __name__ == "__main__":
    main()
