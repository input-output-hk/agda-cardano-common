#!/usr/bin/env python3
"""Check repository Agda roots serially with the replay runner's resource limits."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
# The Agda library marker anchors all paths to the repository root.
ROOT = next(parent for parent in HERE.parents
            if (parent / "src/csp-ptree.agda-lib").is_file())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+", help="Agda module paths relative to src/")
    parser.add_argument("--out", required=True, type=Path, help="artifact directory outside the repository")
    args = parser.parse_args()
    out = args.out.resolve()
    if out.is_relative_to(ROOT):
        parser.error("checking artifacts must stay outside the repository")
    modules = [(ROOT / "src" / name).resolve() for name in args.modules]
    if any(not path.is_relative_to(ROOT / "src") or path.suffix != ".agda" or not path.is_file()
           for path in modules):
        parser.error("each module must be an existing .agda file under src/")
    spec = importlib.util.spec_from_file_location("bounded_certificates", HERE / "certify.py")
    runner = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runner)
    out.mkdir(parents=True, exist_ok=True)
    sources = [Path(__file__), HERE / "certify.py", *modules]
    report = {
        "agda": subprocess.check_output(["agda", "--version"], text=True).strip(),
        "mode": "--safe; serial; heap 2G; sampled RSS 3 GiB; timeout 900 seconds",
        "source_hashes": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sources},
        "checks": [],
    }
    for path in modules:
        name = str(path.relative_to(ROOT / "src"))
        log = out / (name.replace("/", "__") + ".log")
        stats = runner.bounded_agda(["--safe", "-i", ROOT / "src", path], log)
        report["checks"].append({"module": name, "log": str(log), **stats})
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"{name}: exit {stats['exit_code']}, sampled RSS {stats['peak_sampled_rss_kib'] / 1024:.1f} MiB",
              flush=True)
        if stats["exit_code"]:
            raise SystemExit(f"check did not complete successfully; see {log}; no later root was started")


if __name__ == "__main__":
    main()
