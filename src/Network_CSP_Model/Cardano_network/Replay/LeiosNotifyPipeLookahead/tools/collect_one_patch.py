#!/usr/bin/env python3
"""Package/check the minimal T6.3.2 proposal against the exact tested candidate body.

No upstream checkout is changed. Source identity and git apply/reverse checks are
not a fresh GHC build, Haskell refinement proof or production rollout decision.
"""
import argparse
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / "src/csp-ptree.agda-lib").is_file())
BUNDLE = HERE / "patches/collect-one"
UPSTREAM = "ouroboros-consensus/src/ouroboros-consensus/LeiosDemoOnlyTestNotify.hs"
PIN = "2416493bfdbe93b761b3a4bb1ccf2b4a913e5e4b"
ENTRY = "leiosNotifyServerPeerLookahead"
EXPERIMENTAL = ENTRY + "CollectOne"
END = "data ExnLeiosNotifyExcessiveRequests"
APPENDED = "\n-- Separate CollectOne design candidate; original entry point is unchanged.\n"
OLD_COMMENT = (
    "  -- StBusy with @n@ deferred sends outstanding: hand this reply off to the\n"
    "  -- responder and look ahead to the next request (or done) in one step.\n"
)
NEW_COMMENT = (
    "  -- StBusy with @n@ old registered sends: collect at most one completion,\n"
    "  -- then register the current reply and look ahead to the next command.\n"
)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def digest(data):
    return hashlib.sha256(data.encode()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def command(argv, cwd=None):
    result = subprocess.run(list(map(str, argv)), cwd=cwd, capture_output=True,
                            text=True, timeout=30, check=True)
    return result.stdout


def function(source, name):
    start = source.index(name + " ::")
    end = source.index(END, start)
    return start, end, source[start:end]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--consensus", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path,
                        help="new small artifact directory outside the repository")
    parser.add_argument("--write-bundle", action="store_true",
                        help="write the owned review patch and compact validation record")
    args = parser.parse_args()
    out = args.out.resolve()
    require(not out.is_relative_to(ROOT), "apply-check artifacts must remain outside the repository")
    out.mkdir(parents=True, exist_ok=False)

    record_path = HERE / "results-t631-20261104.json"
    evidence = json.loads(record_path.read_text())
    source_bytes = subprocess.check_output(
        ["git", "-C", str(args.consensus), "show", PIN + ":" + UPSTREAM], timeout=30)
    source = source_bytes.decode()
    pin = next(p for p in evidence["source_pins"] if p["source"] == "consensus-peer")
    require(pin["revision"] == PIN and hashlib.sha256(source_bytes).hexdigest() == pin["sha256"],
            "upstream source differs from the tested pin")

    # Run the unchanged experimental generator on a scratch source, then verify
    # the complete generated peer file against every recorded candidate build.
    generator = HERE / "collect_one_design.py"
    key = str(generator.relative_to(ROOT))
    require(sha(generator) == evidence["source_hashes"][key], "experimental generator changed since T6.3.1")
    spec = importlib.util.spec_from_file_location("tested_collect_one_design", generator)
    design = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(design)
    experimental_path = out / "experimental-peer.hs"
    experimental_path.write_bytes(source_bytes)
    design.candidate(experimental_path)
    experimental_file = experimental_path.read_text()
    expected_hashes = {b["compiled_peer_sha256"] for b in evidence["builds"] if b["variant"] == "collect-one"}
    require(len(expected_hashes) == 1 and sha(experimental_path) in expected_hashes,
            "generated peer is not the exact T6.3.1 compiled candidate source")
    require(experimental_file.count(APPENDED) == 1, "candidate append boundary changed")
    experimental_body = experimental_file.split(APPENDED, 1)[1]
    require(experimental_body.startswith(EXPERIMENTAL + " ::") and experimental_body.count(EXPERIMENTAL) == 2,
            "unexpected experimental entry-point occurrences")

    # Make a production-shaped proposal at the existing entry point. Only one
    # recorded comment changes; reversing it and the name gives exact source equality.
    start, end, original_body = function(source, ENTRY)
    proposed_body = experimental_body.replace(EXPERIMENTAL, ENTRY)
    require(proposed_body.count(OLD_COMMENT) == 1, "busy comment boundary changed")
    proposed_body = proposed_body.replace(OLD_COMMENT, NEW_COMMENT)
    normalized = proposed_body.replace(NEW_COMMENT, OLD_COMMENT).replace(ENTRY, EXPERIMENTAL)
    require(normalized == experimental_body, "proposed function differs from tested candidate code")
    proposed = source[:start] + proposed_body + source[end:]
    require(proposed[:start] == source[:start] and proposed[start + len(proposed_body):] == source[end:],
            "proposal changes source outside the selected function")
    require(EXPERIMENTAL not in proposed, "proposal adds a public candidate entry point")
    patch = "".join(difflib.unified_diff(
        source.splitlines(True), proposed.splitlines(True),
        fromfile="a/" + UPSTREAM, tofile="b/" + UPSTREAM))
    patch_path = out / "collect-one.patch"
    patch_path.write_text(patch)

    # Apply and reverse in an isolated source tree; git never writes the user's index.
    tree = out / "apply-tree"
    target = tree / UPSTREAM
    target.parent.mkdir(parents=True)
    target.write_bytes(source_bytes)
    command(["git", "apply", "--check", patch_path], cwd=tree)
    command(["git", "apply", patch_path], cwd=tree)
    require(target.read_text() == proposed, "git-applied source differs from proposed source")
    command(["git", "apply", "--reverse", "--check", patch_path], cwd=tree)
    command(["git", "apply", "--reverse", patch_path], cwd=tree)
    require(target.read_bytes() == source_bytes, "reverse application did not recover the pin")
    numstat = command(["git", "apply", "--numstat", patch_path], cwd=tree).strip().split("\t")
    require(len(numstat) == 3 and numstat[2] == UPSTREAM, "proposal touches another path")

    report = {
        "date": "2026-11-05",
        "task": "T6.3.2 minimal review proposal; not applied to an upstream checkout or published",
        "repository_checkpoint": command(["git", "rev-parse", "HEAD"], cwd=ROOT).strip(),
        "upstream_revision": PIN,
        "upstream_path": UPSTREAM,
        "original_peer_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "proposed_peer_sha256": digest(proposed),
        "patch_sha256": digest(patch),
        "patch_changes": {"files": 1, "added_lines": int(numstat[0]), "removed_lines": int(numstat[1])},
        "function": ENTRY,
        "experimental_function": EXPERIMENTAL,
        "experimental_file_sha256": sha(experimental_path),
        "recorded_candidate_builds_compared": sum(b["variant"] == "collect-one" for b in evidence["builds"]),
        "experimental_function_sha256": digest(experimental_body),
        "normalized_proposed_function_sha256": digest(normalized),
        "normalization": {
            "entry_point": "rename existing entry-point identifier to the experimental entry-point identifier (two occurrences)",
            "comment": {"proposed": NEW_COMMENT, "experimental": OLD_COMMENT},
            "other_ignored_changes": [],
            "exact_equal": True,
        },
        "checks": {
            "pinned_source_hash": True,
            "unchanged_experimental_generator_hash": True,
            "complete_experimental_file_matches_recorded_compiled_source": True,
            "exact_function_identity_after_recorded_renaming_and_comment_reversal": True,
            "all_other_source_bytes_unchanged": True,
            "git_apply_check": True,
            "git_applied_source_equals_proposal": True,
            "git_reverse_check": True,
            "git_reverse_recovers_original_bytes": True,
        },
        "inputs": {
            str(Path(__file__).resolve().relative_to(ROOT)): sha(Path(__file__)),
            str(generator.relative_to(ROOT)): sha(generator),
            str(record_path.relative_to(ROOT)): sha(record_path),
        },
        "artifacts": {"directory": str(out), "patch": str(patch_path), "proposed_peer": str(out / "proposed-peer.hs")},
        "validation_limits": [
            "No new GHC/Agda build or runtime experiment: source correspondence to the already-compiled/tested body is checked mechanically.",
            "This exact source comparison is not a formal proof of Haskell semantics, compiler preservation or exception timing.",
            "Earlier model and controlled-runtime theorem/measurement scopes remain unchanged.",
            "No upstream working tree, source pin, public export, client, driver, callback or wire format changes in this repository.",
            "The proposed in-place patch would change the existing upstream function if a reviewer later applies it.",
        ],
    }
    (out / "proposed-peer.hs").write_text(proposed)
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    if args.write_bundle:
        BUNDLE.mkdir(parents=True, exist_ok=True)
        (BUNDLE / "collect-one.patch").write_text(patch)
        (BUNDLE / "validation-20261105.json").write_text(json.dumps(report, indent=2) + "\n")
    else:
        require((BUNDLE / "collect-one.patch").read_text() == patch, "bundled patch differs from canonical proposal")
    print(json.dumps({"patch_changes": report["patch_changes"], "patch_sha256": report["patch_sha256"],
                      "source_identity_and_apply_checks": "passed", "report": str(out / "report.json")}, indent=2))


if __name__ == "__main__":
    main()
