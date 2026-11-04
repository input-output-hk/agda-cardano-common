#!/usr/bin/env python3
"""Run bounded low-occupancy history experiments against the pinned Haskell peers.

Counts and streamed wire captures are T5.1.1 evidence. This is neither a replay
rejection procedure nor an allocation/residency/latency benchmark (T5.1.2).
"""
import argparse
import ctypes
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / "src/csp-ptree.agda-lib").is_file())


def file_hash(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def load_fixture():
    spec = importlib.util.spec_from_file_location("controlled_fixture", HERE / "run.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def bounded_command(args, log, cwd=None, timeout=300):
    """Cap this process group and its lifetime; resource failures are inconclusive."""
    argv = list(map(str, args))
    if argv[0] == "ghc":
        argv += ["+RTS", "-M2G", "-RTS"]
    parent = os.getpid()

    def lifetime():
        if ctypes.CDLL(None).prctl(1, signal.SIGKILL, 0, 0, 0) != 0 or os.getppid() != parent:
            os._exit(125)

    started, peak, failure = time.monotonic(), 0, None
    with Path(log).open("w") as stream:
        proc = subprocess.Popen(argv, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT,
                                stdin=subprocess.DEVNULL, start_new_session=True, preexec_fn=lifetime)
        try:
            while proc.poll() is None:
                try:
                    rows = Path(f"/proc/{proc.pid}/status").read_text().splitlines()
                    rss = int(next(row for row in rows if row.startswith("VmRSS:")).split()[1])
                    peak = max(peak, rss)
                except (OSError, StopIteration):
                    pass
                if peak > 3 * 1024 * 1024:
                    failure = "RSS budget exceeded"
                elif time.monotonic() - started > timeout:
                    failure = "timeout"
                if failure:
                    os.killpg(proc.pid, signal.SIGKILL)
                    break
                time.sleep(0.1)
            code = proc.wait()
        finally:
            if proc.poll() is None:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
    stats = {"argv": argv, "exit_code": code, "seconds": round(time.monotonic() - started, 3),
             "peak_sampled_rss_kib": peak or None, "rss_limit_kib": 3 * 1024 * 1024,
             "budget_failure": failure}
    if code and "Heap exhausted" in Path(log).read_text():
        stats["budget_failure"] = "heap budget exceeded"
    Path(str(log) + ".resources.json").write_text(json.dumps(stats, indent=2) + "\n")
    if code or failure:
        raise RuntimeError(f"inconclusive build/experiment failure ({code}): see {log}")
    return stats


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


def validate(path, total, depth, observed):
    """Check complete endpoint streams, payloads, observer counts and control bounds."""
    phases, counts, hashes, ended, passed, rows = {}, {}, {}, set(), 0, 0
    for actor in ["client", "server"]:
        for kind in ["Send", "Recv"]:
            counts[actor, kind] = 0
            hashes[actor, kind] = hashlib.sha256()
    with Path(path).open() as stream:
        for line in stream:
            parts = line.rstrip("\n").split("\t")
            if parts == ["PASS"]:
                passed += 1
            elif parts[0] == "S" and len(parts) == 4:
                _, phase, key, value = parts
                require(key not in phases.setdefault(phase, {}), "duplicate snapshot field")
                phases[phase][key] = int(value)
            else:
                require(len(parts) == 5 and parts[0] == "W", "unrecognized fixture output")
                _, index, actor, kind, payload = parts
                key = actor, kind
                require(int(index) == rows and key in counts and key not in ended, "invalid wire index or post-final row")
                n = counts[key]
                request_stream = key in [("client", "Send"), ("server", "Recv")]
                if n < total:
                    expected = "RequestNext" if request_stream else f"Offer:{n+1}:{n+1}:53"
                    require(payload == expected, "wrong packet order, count or exact offer fields")
                else:
                    require(n == total and payload == ("Quit" if request_stream else "Done"), "unexpected final packet")
                    ended.add(key)
                counts[key] += 1
                hashes[key].update((payload + "\n").encode())
                rows += 1
    require(passed == 1 and rows == 4 * total + 4 and len(ended) == 4, "incomplete session")
    final = phases.get("final", {})
    for key in ["request_sends", "request_receives", "reply_sends", "reply_receives", "handled"]:
        require(final.get(key) == total, f"bad final {key}")
    require(final.get("free_credits") == 0, "credits did not return to zero")
    if observed:
        require(set(phases) == {"client-before-quit", "server-recv-quit", "final"}, "missing checkpoint")
        before, server = phases["client-before-quit"], phases["server-recv-quit"]
        bound = 1 if depth == 1 else 2
        require(final["peak_before_quit"] <= bound and final["peak_overall"] <= bound + 1, "client work exceeded small-occupancy bound")
        require(total == 0 or final["peak_before_quit"] >= 1, "nonempty history with no receiver work")
        for phase in [before, server]:
            require(phase["registered_jobs"] == total and phase["flush_entered"] == 0 and phase["flush_returned"] == 0,
                    "pre-Quit registration/flush history mismatch")
        for key in ["registered_jobs", "flush_entered", "flush_returned"]:
            require(final[key] == total, f"bad final {key}")
        marker = 1 if before["client_outstanding"] else 0
        require(final["client_jobs"] == total + marker and final["client_results"] == total + marker
                and final["client_outstanding"] == 0, "client receiver/marker accounting mismatch")
    else:
        require(set(phases) == {"final"}, "peer observation leaked into wire-only control")
        require(all(final[k] == 0 for k in ["registered_jobs", "flush_entered", "flush_returned", "client_jobs", "client_results"]),
                "unexpected peer observer counters in wire-only control")
    return {"wire_rows": rows, "snapshots": phases,
            "endpoint_stream_sha256": {f"{a}-{k}": h.hexdigest() for (a, k), h in hashes.items()}}


def negative_controls(report, out):
    """Mutate a real capture to check that validation cannot accept missing evidence."""
    source = next((r for r in report["runs"] if r["mode"] == "observed" and r["exchanges"] > 0), None)
    if source is None:
        return []
    data = (out / (source["name"] + ".tsv")).read_text()
    lines = data.splitlines(keepends=True)
    mutations = {
        "missing-pass": "".join(line for line in lines if line != "PASS\n"),
        "changed-offer-size": data.replace("Offer:1:1:53", "Offer:1:1:54", 1),
        "missing-done": "".join(line for line in lines if not (line.startswith("W\t") and line.endswith("\tserver\tSend\tDone\n"))),
        "pre-quit-flush": data.replace("S\tserver-recv-quit\tflush_returned\t0\n", "S\tserver-recv-quit\tflush_returned\t1\n", 1),
        "oversized-client-work": "".join("S\tfinal\tpeak_before_quit\t1001\n" if line.startswith("S\tfinal\tpeak_before_quit\t") else line for line in lines),
    }
    results = []
    for name, mutated in mutations.items():
        require(mutated != data, f"negative control {name} did not change the capture")
        path = out / ("negative-" + name + ".tsv")
        path.write_text(mutated)
        try:
            validate(path, source["exchanges"], source["depth"], True)
        except ValueError as error:
            results.append({"name": name, "fixture_validation_rejected": True, "reason": str(error),
                            "capture_sha256": file_hash(path)})
        else:
            raise ValueError(f"negative control {name} was accepted")
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--consensus", type=Path, required=True)
    parser.add_argument("--typed-protocols", type=Path, required=True)
    parser.add_argument("--network-archive", type=Path, required=True)
    parser.add_argument("--package-db", type=Path, default=Path.home() / ".cabal/store/ghc-9.6.7/package.db")
    parser.add_argument("--build-packages", type=Path, default=HERE / "build-packages.json")
    parser.add_argument("--counts", nargs="+", type=int, default=[0, 1, 10, 100, 1000, 10000])
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    require(not out.is_relative_to(ROOT), "artifacts must remain outside the repository")
    require(args.repeat > 0 and args.counts and all(0 <= n <= 1000000 for n in args.counts), "invalid experiment sizes")
    require(len(set(args.counts)) == len(args.counts), "duplicate experiment size")
    out.mkdir(parents=True, exist_ok=False)
    fixture = load_fixture()
    fixture.command = bounded_command
    compiler = fixture.build(args, out, main_source=HERE / "CompletionHistory.hs", executable="completion-history")
    report = {"scope": "T5.1.1 controlled counts; no timing/residency benchmark or new Agda certificate",
              "consensus": fixture.CONSENSUS, "typed_protocols": fixture.TYPED, "network": fixture.NETWORK,
              "compiler": compiler, "optimization": "-O0", "observations": "peer constructor wrappers plus original limits-driver wire hooks",
              "private_doneVar_sampled": False, "callback": "controlled handler/send gate; constant depth 1 or 1000, explicit eligible offers",
              "source_hashes": {str(p.resolve().relative_to(ROOT)) if p.resolve().is_relative_to(ROOT) else str(p.resolve()): file_hash(p) for p in
                                [Path(__file__), HERE / "CompletionHistory.hs", HERE / "run.py", args.build_packages]},
              "runs": [], "complete": False}
    for depth in [1, 1000]:
        for capabilities in [1, 2]:
            for total in args.counts:
                for repeat in range(args.repeat):
                    projections = {}
                    for mode in ["observed", "wire-only"]:
                        name = f"d{depth}-N{capabilities}-n{total}-r{repeat}-{mode}"
                        raw = out / (name + ".tsv")
                        resources = bounded_command([out / "completion-history", total, depth, mode,
                                                     "+RTS", f"-N{capabilities}", "-M256M", "-K64M", "-RTS"], raw, timeout=150)
                        checked = validate(raw, total, depth, mode == "observed")
                        projections[mode] = checked["endpoint_stream_sha256"]
                        report["runs"].append({"name": name, "depth": depth, "capabilities": capabilities,
                                               "exchanges": total, "mode": mode, "repeat": repeat,
                                               "capture_sha256": file_hash(raw),
                                               "resources": resources, **checked})
                        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
                    require(projections["observed"] == projections["wire-only"], "wire-only control differs at endpoint-stream projection")
                print(f"depth={depth} N{capabilities} exchanges={total}: observed/control checks passed", flush=True)
    report["negative_controls"] = negative_controls(report, out)
    report["observed_vs_wire_only_endpoint_streams_equal"] = True
    report["complete"] = True
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"report: {out / 'report.json'}", flush=True)


if __name__ == "__main__":
    main()
