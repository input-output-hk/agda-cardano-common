#!/usr/bin/env python3
"""Build pinned peers/drivers in isolation and check controlled fixture histories.

No installation, checkout mutation, whole-node conformance claim, or arbitrary-log
decision procedure. Generated sources, binaries and logs go to --out (default /tmp).
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile

HERE = Path(__file__).resolve().parent
# The Agda library marker anchors all paths to the repository root.
ROOT = next(parent for parent in HERE.parents
            if (parent / "src/csp-ptree.agda-lib").is_file())
CONSENSUS = "2416493bfdbe93b761b3a4bb1ccf2b4a913e5e4b"
TYPED = "9b4627221ae5d649f2303c6926a8dba3f9934658"
NETWORK = "2f1c154f248659b89523d5679ca532f442e7ed2a"
ARCHIVE_SHA = "1ba2548f87248d2561d544d09f75e5856464d7936501737a71396ffba8054db3"
EXPORTER = "Cardano_network/Replay/LeiosNotifyPipeLookahead/ExportFixtures.agda"
NODE_TESTS = "Cardano_network/Replay/LeiosNotifyPipeLookahead/NodeDriverTests.agda"
SHIM = """-- Import-only shim; implementations come from the unchanged pinned module.
module Ouroboros.Consensus.Util.IOLike
  (StrictTVar, newTVarIO, readTVar, writeTVar, modifyTVar) where
import Ouroboros.Consensus.Util.NormalForm.StrictTVar
"""
CASES = {"idle-quit", "cancel-blocked-next", "delayed-send-prefix",
         "selected-normal", "before-quit-flag", "excessive", "terminate-at-capacity",
         "arrived-before-publication"}
MODEL_CASES = {"idle-quit", "cancel-blocked-next", "delayed-send-prefix", "selected-normal"}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def command(args, log, cwd=None, timeout=300):
    with log.open("w") as stream:
        result = subprocess.run([str(x) for x in args], cwd=cwd, stdout=stream,
                                stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}): {args[0]}; see {log}")


def git_bytes(repo, revision, path):
    return subprocess.check_output(["git", "-C", str(repo), "show", f"{revision}:{path}"])


def export_git(repo, revision, paths, target):
    data = subprocess.check_output(["git", "-C", str(repo), "archive", revision, *paths])
    with tarfile.open(fileobj=io.BytesIO(data)) as archive:
        archive.extractall(target, filter="data")


def prepare(args, out):
    src = out / "src"
    src.mkdir()
    base = "ouroboros-consensus/src/ouroboros-consensus/"
    for name in ["LeiosDemoOnlyTestNotify.hs", "Ouroboros/Consensus/Util/NormalForm/StrictTVar.hs",
                 "Ouroboros/Consensus/Util/NormalForm/Invariant.hs"]:
        destination = src / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(git_bytes(args.consensus, CONSENSUS, base + name))
    (src / "Ouroboros/Consensus/Util/IOLike.hs").write_text(SHIM)
    typed = out / "typed"
    export_git(args.typed_protocols, TYPED, ["typed-protocols/src", "typed-protocols/cborg"], typed)
    data = args.network_archive.read_bytes()
    if digest(data) != ARCHIVE_SHA:
        raise ValueError("network archive differs from the locked pinned codeload archive")
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as archive:
        prefix = f"ouroboros-network-{NETWORK}/"
        needed = ["network-mux/src/", "ouroboros-network/framework/lib/", "ouroboros-network/api/lib/"]
        members = [member for member in archive.getmembers()
                   if any(member.name.startswith(prefix + directory) for directory in needed)]
        archive.extractall(out / "network", members=members, filter="data")
    network = out / "network" / f"ouroboros-network-{NETWORK}"
    pinned = json.loads((ROOT / "src/Cardano_network/LeiosNotifyPipeLookahead/sources.json").read_text())
    checks = {"consensus-peer": src / "LeiosDemoOnlyTestNotify.hs",
              "lookahead-driver": typed / "typed-protocols/src/Network/TypedProtocol/Driver.hs",
              "runtime-counter": typed / "typed-protocols/src/Network/TypedProtocol/Core.hs",
              "network-limits": network / "ouroboros-network/framework/lib/Ouroboros/Network/Driver/Limits.hs"}
    for lock in pinned:
        if lock["source"] in checks:
            if digest(checks[lock["source"]].read_bytes()) != lock["sha256"]:
                raise ValueError(f"pinned source hash mismatch: {lock['source']}")
    return src, typed / "typed-protocols", network


def build(args, out, *, main_source=None, executable="schedules"):
    src, typed, network = prepare(args, out)
    # hsc2hs needs the same network headers as the selected GHC package.
    includes = subprocess.check_output(["ghc-pkg", f"--package-db={args.package_db}",
                                        "field", "network", "include-dirs"], text=True)
    headers = [Path(line.split(":", 1)[1].strip()) for line in includes.splitlines()
               if line.startswith("include-dirs:")]
    header = next(p for p in headers if (p / "HsNet.h").is_file())
    generated = src / "Network/Mux/TCPInfo/Linux.hs"
    generated.parent.mkdir(parents=True)
    command(["hsc2hs", network / "network-mux/src/Network/Mux/TCPInfo/Linux.hsc",
             "-I" + str(header), "-o", generated], out / "hsc2hs.log")
    settings = json.loads(args.build_packages.read_text())
    version = subprocess.check_output(["ghc", "--numeric-version"], text=True).strip()
    if version != settings["compiler"]:
        raise ValueError(f"compiler {version} differs from package settings {settings['compiler']}")
    includes = [src, typed / "src", typed / "cborg", network / "ouroboros-network/framework/lib",
                network / "ouroboros-network/api/lib", network / "network-mux/src"]
    # GHC2021 serves typed-protocols; DeepSubsumption retains the Haskell2010
    # higher-rank subsumption used by the original consensus module.
    ghc = ["ghc", "--make", "-O0", "-threaded", "-rtsopts", "-XGHC2021", "-XDeepSubsumption",
           "-XLambdaCase", "-XDataKinds", "-XGADTs", "-package-db", str(args.package_db),
           "-hide-all-packages", *settings["package_flags"],
           *("-i" + str(p) for p in includes), "-outputdir", str(out / "build"),
           "-o", str(out / executable), str(main_source or HERE / "Main.hs")]
    (out / "ghc-command.json").write_text(json.dumps(ghc, indent=2) + "\n")
    command(ghc, out / "build.log")
    with (out / "package-database.txt").open("w") as stream:
        subprocess.run(["ghc-pkg", f"--package-db={args.package_db}", "dump"], stdout=stream, check=True)
    # Record every source compiled locally, including the explicit shim and generated binding.
    files = [p for directory in [src, typed, network] for p in directory.rglob("*.hs")]
    manifest = {str(p.relative_to(out)): digest(p.read_bytes()) for p in files}
    (out / "source-hashes.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    return version


def model_rows(args, out):
    command(["agda", "--safe", EXPORTER], out / "agda-safe.log", cwd=ROOT / "src")
    path = json.dumps(str(ROOT / "src" / EXPORTER))
    commands = (f"IOTCM {path} None Direct (Cmd_load {path} [])\n"
                f'IOTCM {path} None Direct (Cmd_compute_toplevel DefaultCompute "rendered")\n')
    (out / "agda-commands.txt").write_text(commands)
    process = subprocess.run(["agda", "--safe", "--interaction-json"], input=commands,
                             capture_output=True, text=True, cwd=ROOT / "src", timeout=180)
    (out / "agda-normalization.jsonl").write_text(process.stdout)
    (out / "agda-normalization.stderr").write_text(process.stderr)
    require(process.returncode == 0, "Agda normalization process failed")
    normal_forms = []
    checked = False
    for line in process.stdout.splitlines():
        line = line.removeprefix("JSON> ").strip()
        if not line:
            continue
        response = json.loads(line)
        if response.get("kind") == "Status":
            checked = response["status"].get("checked", False)
        info = response.get("info", {})
        require(info.get("kind") != "Error", "Agda reported an interaction error")
        if info.get("kind") == "NormalForm":
            require(info.get("computeMode") == "DefaultCompute", "unexpected normalization mode")
            normal_forms.append(json.loads(info["expr"]))
    require(checked and len(normal_forms) == 1, "missing checked Agda normal form")
    result = normal_forms[0]
    (out / "model.tsv").write_text(result)
    expected = {}
    for line in result.splitlines():
        name, actor, kind, payload = line.split("\t")
        expected.setdefault(name, []).append((actor, kind, payload))
    if set(expected) != MODEL_CASES:
        raise ValueError("exported model fixture set changed")
    return expected


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


def parse(text):
    cases, passed = {}, set()
    for line in text.splitlines():
        parts = line.split("\t")
        if len(parts) == 2 and parts[1] == "PASS":
            require(parts[0] not in passed, "duplicate PASS")
            passed.add(parts[0])
            continue
        require(len(parts) == 6, f"unrecognized harness output: {line}")
        name, index, actor, kind, payload, thread = parts
        rows = cases.setdefault(name, [])
        require(int(index) == len(rows), f"missing/reordered source coordinate in {name}")
        rows.append((actor, kind, payload, thread))
    require(set(cases) == passed == CASES, "missing or additional experiment/PASS")
    return cases


def validate(cases, expected):
    summary = {}
    for name, rows in cases.items():
        wire = [r[:3] for r in rows if r[1] in {"Send", "Recv"}]
        if name in expected:
            require(wire == expected[name], f"{name}: actual wire rows differ from checked Agda witness")
        def positions(actor, kind, payload):
            return [i for i, row in enumerate(rows) if row[:3] == (actor, kind, payload)]
        def position(actor, kind, payload):
            result = positions(actor, kind, payload)
            require(len(result) == 1, f"{name}: expected one {actor}/{kind}/{payload}")
            return result[0]
        free = {"cancel-blocked-next": "1", "excessive": "1000", "terminate-at-capacity": "1000",
                "arrived-before-publication": "999"}.get(name, "0")
        position("controller", "FinalCredit", free)
        handlers = [r for r in rows if r[1] == "Handler"]
        require(len(handlers) == (1 if name in {"delayed-send-prefix", "arrived-before-publication"} else 0),
                f"{name}: handler/drain mismatch")
        if name == "selected-normal":
            require(position("server", "Hook", "SelectedNormalBeforeCommit") <
                    position("server", "Recv", "Quit") <
                    position("server", "Hook", "QuitEffectCompleted") <
                    position("controller", "Release", "SelectedNormalCommit") <
                    position("server", "Send", "Offer:43:47:53"), "selected normal did not cross the true flag")
        if name == "before-quit-flag":
            require(len(wire) == 12, "two-request shutdown has wrong wire count")
            require(len(positions("client", "Send", "RequestNext")) == 2 and
                    len(positions("server", "Recv", "RequestNext")) == 2, "request multiplicity changed")
            begin = position("server", "Hook", "BeforeQuitEffect")
            end = position("server", "Hook", "QuitEffectCompleted")
            require(position("server", "Recv", "Quit") < begin < end, "Quit hook order changed")
            sends = [position("server", "Send", packet) for packet in ["Offer:43:47:53", "TxsOffer:59:61"]]
            receives = [position("client", "Recv", packet) for packet in ["Offer:43:47:53", "TxsOffer:59:61"]]
            require(begin < sends[0] < sends[1] < end and receives[0] < receives[1],
                    "normal replies did not remain FIFO inside the pre-flag interval")
            require(all("Canceled" != r[2] for r in wire), "unexpected cancellation")
            require(position("client", "Send", "Quit") < position("server", "Recv", "Quit") and
                    position("client", "Recv", "Done") < position("server", "Send", "Done"), "shutdown order changed")
        if name == "excessive":
            require(wire == [("server", "Recv", "RequestNext")] * 1001, "adversarial input changed")
            require(len(positions("server", "Callback", "Admitted")) == 1000, "wrong admission count")
            position("server", "Callback", "ExcessiveRequests")
            position("server", "Outcome", "ExcessiveRequestsException")
        elif name in {"terminate-at-capacity", "arrived-before-publication"}:
            require(len(wire) == 4004, f"{name}: full-pipe wire count changed")
            for actor, kind in [("client", "Send"), ("server", "Recv")]:
                require([r[2] for r in wire if r[:2] == (actor, kind)] == ["RequestNext"] * 1000 + ["Quit"],
                        f"{name}: capacity/request agency changed")
            normal = name == "arrived-before-publication"
            replies = (["Offer:43:47:53"] if normal else []) + ["Canceled"] * (999 if normal else 1000) + ["Done"]
            for actor, kind in [("server", "Send"), ("client", "Recv")]:
                require([r[2] for r in wire if r[:2] == (actor, kind)] == replies,
                        f"{name}: response FIFO/draining changed")
            if normal:
                require(position("client", "Hook", "ArrivedBeforePublication") <
                        position("controller", "Hook", "StopPendingPublication") and
                        position("client", "Hook", "BlockingCollectSelected") <
                        position("controller", "Input", "Terminate") <
                        position("controller", "Hook", "StopPendingPublication") <
                        position("client", "Send", "Quit"), "publication/termination barrier order changed")
            position("controller", "Outcome", "BothDone")
        else:
            position("controller", "Outcome", "InterruptedPrefix" if name == "delayed-send-prefix" else "BothDone")
        summary[name] = {"wire_rows": len(wire), "final_free_credits": int(free),
                         "agda_wire_witness_match": name in expected}
    return summary


def negative_controls(cases, expected):
    tested = []
    for mutation in ["drop-canceled", "change-offer-size", "receive-after-send"]:
        changed = {name: list(rows) for name, rows in cases.items()}
        if mutation == "drop-canceled":
            name = "cancel-blocked-next"
            changed[name] = [r for r in changed[name] if r[:3] != ("client", "Recv", "Canceled")]
        elif mutation == "change-offer-size":
            name = "selected-normal"
            changed[name] = [(a, k, "Offer:43:47:54" if p == "Offer:43:47:53" else p, t)
                             for a, k, p, t in changed[name]]
        else:
            name = "delayed-send-prefix"
            recv = next(i for i, r in enumerate(changed[name]) if r[:3] == ("server", "Recv", "RequestNext"))
            send = next(i for i, r in enumerate(changed[name]) if r[:3] == ("client", "Send", "RequestNext"))
            changed[name][recv], changed[name][send] = changed[name][send], changed[name][recv]
        try:
            validate(changed, expected)
        except ValueError:
            tested.append(mutation)
        else:
            raise ValueError(f"negative control escaped: {mutation}")
    return tested


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--consensus", type=Path, required=True, help="local git repository containing the pinned revision")
    parser.add_argument("--typed-protocols", type=Path, required=True, help="local git repository containing the pinned revision")
    parser.add_argument("--network-archive", type=Path, required=True, help="locked codeload tar.gz for network 2f1c154")
    parser.add_argument("--package-db", type=Path, default=Path.home() / ".cabal/store/ghc-9.6.7/package.db")
    parser.add_argument("--build-packages", type=Path, default=HERE / "build-packages.json")
    parser.add_argument("--repeat", type=int, default=5)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    require(args.repeat > 0, "repeat must be positive")
    out = args.out.resolve() if args.out else Path(tempfile.mkdtemp(prefix="leiosnotify-schedules-"))
    if args.out:
        out.mkdir(exist_ok=False, parents=True)
    require(not out.is_relative_to(ROOT), "generated artifacts must be outside the repository")
    print(f"artifacts: {out}", flush=True)
    version = build(args, out)
    expected = model_rows(args, out)
    report = {"consensus": CONSENSUS, "typed_protocols": TYPED, "network": NETWORK,
              "network_archive_sha256": ARCHIVE_SHA, "ghc": version,
              "agda": subprocess.check_output(["agda", "--version"], text=True).strip(),
              "codec": "codecLeiosNotifyId; in-memory AnyMessage; limits wrappers active",
              "scope": "controlled fixture evidence; no whole-node refinement or arbitrary-log decider",
              "fixture_sha256": digest((HERE / "Main.hs").read_bytes()),
              "runner_sha256": digest(Path(__file__).read_bytes()),
              "node_tests_sha256": digest((ROOT / "src" / NODE_TESTS).read_bytes()),
              "exporter_sha256": digest((ROOT / "src" / EXPORTER).read_bytes()), "runs": []}
    for capabilities in [1, 2]:
        for repeat in range(args.repeat):
            label = f"N{capabilities}-{repeat}"
            raw = out / f"{label}.tsv"
            command([out / "schedules", "+RTS", f"-N{capabilities}", "-RTS"], raw, timeout=75)
            cases = parse(raw.read_text())
            report["runs"].append({"label": label, "cases": validate(cases, expected),
                                   "negative_controls": negative_controls(cases, expected)})
            print(f"{label}: eight schedules passed; four Agda wire histories matched", flush=True)
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"report: {out / 'report.json'}")


if __name__ == "__main__":
    main()
