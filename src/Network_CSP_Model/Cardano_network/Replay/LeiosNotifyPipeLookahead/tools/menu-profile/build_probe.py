#!/usr/bin/env python3
"""Compile only MenuProbeMain with separate bounded Agda and GHC heaps."""
import argparse
import ctypes
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
TOOLS=HERE.parent
ROOT=next(path for path in HERE.parents if (path/'src/csp-ptree.agda-lib').is_file())


def sha(path):
    """Retain exact source, generated Haskell, executable and log identities."""
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    """Use a new disk-backed directory; no production executable is rebuilt."""
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--stage',choices=('all','agda','ghc'),default='all')
    args=parser.parse_args();out=args.out.resolve()
    if not out.is_relative_to(Path('/var/tmp')):
        parser.error('--out must be below disk-backed /var/tmp')
    if args.stage=='ghc':
        if not out.is_dir() or not (out/'agda-report.json').is_file():
            parser.error('GHC resume requires a completed Agda-stage directory')
    else:
        if out.exists():parser.error('new generation requires a new directory')
        out.mkdir(parents=True)
    paths=[Path(__file__).resolve(),TOOLS/'certify.py',
           TOOLS.parent/'MenuProbe.agda',TOOLS.parent/'MenuProbeTests.agda',TOOLS.parent/'MenuProbeMain.agda',
           TOOLS.parent/'DriverDecide.agda',TOOLS.parent/'ReadyGateOrder.agda',TOOLS.parent/'CostProbe.agda',TOOLS.parent/'LookaheadMain.agda',TOOLS.parent/'LookaheadReport.agda',
           TOOLS.parent/'Wire/PairedAdapter.agda']
    before={str(path.relative_to(ROOT)):sha(path) for path in paths}
    if args.stage=='ghc':
        if before!=json.loads((out/'source-before.json').read_text()):
            parser.error('build sources changed between generation and GHC')
        if json.loads((out/'agda-report.json').read_text())['exit_code']:
            parser.error('Agda generation did not complete successfully')
        generated_now={str(path.relative_to(out/'generated')):sha(path)
                       for path in sorted((out/'generated').rglob('*.hs'))}
        if generated_now!=json.loads((out/'generation-haskell-sha256.json').read_text()):
            parser.error('generated Haskell changed after Agda generation')
    else:
        (out/'source-before.json').write_text(json.dumps(before,indent=2)+'\n')
    spec=importlib.util.spec_from_file_location('menu_probe_bounded_agda',TOOLS/'certify.py')
    bounded=importlib.util.module_from_spec(spec);spec.loader.exec_module(bounded)
    agda=['--compile','--ghc-dont-call-ghc','-i',str(ROOT/'src'),
        '--compile-dir='+str(out/'generated'),'--ghc-flag=-O0',
        '--ghc-flag=-threaded','--ghc-flag=-rtsopts',str(TOOLS.parent/'MenuProbeMain.agda')]
    actual_agda=['agda','-l','standard-library','-l','standard-library-classes',
                 *agda,'+RTS','-M2G','-s','-RTS']
    if args.stage!='ghc':
        (out/'agda-command.json').write_text(json.dumps(actual_agda,indent=2)+'\n')
        stats=bounded.bounded_agda(agda,out/'agda.log',timeout=900)
        (out/'agda-report.json').write_text(json.dumps(stats,indent=2)+'\n')
        print('Agda diagnostic codegen:',stats,flush=True)
        if stats['exit_code']:return stats['exit_code']
        generated_now={str(path.relative_to(out/'generated')):sha(path)
                       for path in sorted((out/'generated').rglob('*.hs'))}
        (out/'generation-haskell-sha256.json').write_text(json.dumps(generated_now,indent=2)+'\n')
        (out/'source-after-generation.json').write_text(json.dumps(
            {str(path.relative_to(ROOT)):sha(path) for path in paths},indent=2)+'\n')
        if args.stage=='agda':
            print('Generation complete; inspect generated sharing before --stage ghc.',flush=True)
            return 0
    command=shlex.split(next(line.split('NOT calling: ',1)[1] for line in
        (out/'agda.log').read_text().splitlines() if 'NOT calling: ' in line))
    command += ['+RTS','-M2G','-s','-RTS']
    (out/'ghc-command.json').write_text(json.dumps(command,indent=2)+'\n')
    started,peak,failure=time.monotonic(),0,None;parent=os.getpid()
    def lifetime():
        if ctypes.CDLL(None).prctl(1,signal.SIGKILL,0,0,0)!=0 or os.getppid()!=parent:
            os._exit(125)
    with (out/'ghc.log').open('w') as log:
        process=subprocess.Popen(command,cwd=ROOT,stdin=subprocess.DEVNULL,
            stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=lifetime)
        try:
            while process.poll() is None:
                try:
                    status=Path('/proc/'+str(process.pid)+'/status').read_text()
                    peak=max(peak,int(next(line for line in status.splitlines() if line.startswith('VmRSS:')).split()[1]))
                except (OSError,StopIteration):pass
                if peak>3*1024*1024:failure='sampled RSS limit'
                elif time.monotonic()-started>600:failure='timeout'
                if failure:
                    os.killpg(process.pid,signal.SIGKILL);break
                time.sleep(0.1)
            code=process.wait()
        finally:
            if process.poll() is None:
                os.killpg(process.pid,signal.SIGKILL);process.wait()
    stats=dict(exit_code=code,seconds=round(time.monotonic()-started,3),
        peak_sampled_rss_kib=peak,heap_limit='2G',rss_limit_kib=3*1024*1024,
        timeout_seconds=600,budget_failure=failure)
    (out/'ghc-report.json').write_text(json.dumps(stats,indent=2)+'\n')
    print('GHC diagnostic build:',stats,flush=True)
    if code:return code
    after={str(path.relative_to(ROOT)):sha(path) for path in paths}
    (out/'source-after.json').write_text(json.dumps(after,indent=2)+'\n')
    generated={str(path.relative_to(out/'generated')):sha(path)
               for path in sorted((out/'generated').rglob('*.hs'))}
    (out/'generated-haskell-sha256.json').write_text(json.dumps(generated,indent=2)+'\n')
    binary=out/'generated/MenuProbeMain'
    result=dict(binary=str(binary),binary_sha256=sha(binary),sources_unchanged=before==after,
                generated_haskell_modules=len(generated),generated_manifest_sha256=sha(out/'generated-haskell-sha256.json'))
    (out/'build-result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)
    return 0 if before==after else 1


if __name__=='__main__':raise SystemExit(main())
