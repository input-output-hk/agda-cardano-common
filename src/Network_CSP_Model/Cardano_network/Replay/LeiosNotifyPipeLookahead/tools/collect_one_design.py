#!/usr/bin/env python3
"""T6.1.1 type/constructor design probe, separate from baseline and runtime validation."""
import argparse
import difflib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p/'src/csp-ptree.agda-lib').is_file())


def helpers():
    spec=importlib.util.spec_from_file_location('history_helpers',HERE/'completion_history.py')
    h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h);return h


def candidate(path):
    """Append a separately named copy; only its busy loop changes and all originals stay intact."""
    original=path.read_text();name='leiosNotifyServerPeerLookahead';new=name+'CollectOne'
    start=original.index(name+' ::');end=original.index('data ExnLeiosNotifyExcessiveRequests',start)
    body=original[start:end].replace(name,new)
    sig=body[body.index('  busy ::'):body.index('  busy quitVar n =')]
    old='  busy quitVar n =\n    AwaitLookahead'
    hnew=('  busy quitVar n = case n of\n'
          '    Zero -> awaitNext quitVar Zero\n'
          '    Succ previous ->\n'
          '      FlushSender (Just $ awaitNext quitVar n) (awaitNext quitVar previous)\n\n'
          '  -- Poll only old registered jobs, then register the current request exactly once.\n'
          +sig.replace('busy ::','awaitNext ::')+'  awaitNext quitVar n =\n    AwaitLookahead')
    assert body.count(old)==1;body=body.replace(old,hnew)
    export='  , '+name+'\n';assert original.count(export)==1
    patched=original.replace(export,export+'  , '+new+'\n')
    patched+='\n-- Separate CollectOne design candidate; original entry point is unchanged.\n'+body
    assert patched.replace('  , '+new+'\n','').split('\n-- Separate CollectOne design candidate;')[0]==original
    path.write_text(patched)
    return ''.join(difflib.unified_diff(original.splitlines(True),patched.splitlines(True),fromfile='pinned/Peer.hs',tofile='candidate/Peer.hs'))


def budget_checks():
    """Finite sanity checks of a conditional derivation; this is not a universal Agda proof."""
    tested=0
    for bound in range(9):
        for n in range(bound+2):
            for completed in range(n+1):
                unfinished=n-completed
                if unfinished>bound:continue
                hit=int(completed>0)
                after_poll=n-hit
                after_register=after_poll+1
                assert after_register<=bound+1
                if hit:assert after_register==n
                else:assert n==unfinished and after_register==unfinished+1
                tested+=1
    # Omitting a ready flush allows history to grow with zero unfinished work.
    assert 1+1>0+1
    return {'bounds_enumerated':[0,8],'admissible_poll_register_cases':tested,
            'no_collection_counterexample':{'B':0,'old_registered':1,'completed':1,'unfinished':0,'after_register':2,'claimed_limit':1},
            'universal_proof':'not performed; derivation retains unfinished<=B as an explicit premise'}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--consensus',type=Path,required=True);ap.add_argument('--typed-protocols',type=Path,required=True)
    ap.add_argument('--network-archive',type=Path,required=True)
    ap.add_argument('--package-db',type=Path,default=Path.home()/'.cabal/store/ghc-9.6.7/package.db')
    ap.add_argument('--build-packages',type=Path,default=HERE/'build-packages.json')
    ap.add_argument('--out',type=Path,required=True);args=ap.parse_args();h=helpers();f=h.load_fixture();out=args.out.resolve()
    h.require(not out.is_relative_to(ROOT),'artifacts must stay outside repository');out.mkdir(parents=True,exist_ok=False)
    original_prepare=f.prepare;provenance={}
    def prepare(arguments,destination):
        src,typed,network=original_prepare(arguments,destination)
        peer=src/'LeiosDemoOnlyTestNotify.hs';provenance['original_peer_sha256']=h.file_hash(peer)
        (out/'candidate.patch').write_text(candidate(peer));provenance['candidate_peer_sha256']=h.file_hash(peer)
        return src,typed,network
    def command(argv,log,cwd=None,timeout=300):
        stats=h.bounded_command(argv,log,cwd=cwd,timeout=timeout)
        if str(argv[0])=='ghc':(out/'ghc-command.json').write_text(json.dumps(stats['argv'],indent=2)+'\n')
        return stats
    f.prepare,f.command=prepare,command
    compiler=f.build(args,out,main_source=HERE/'CollectOneProbe.hs',executable='collect-one-probe')
    log=out/'probe.tsv';resources=h.bounded_command([out/'collect-one-probe','+RTS','-M256M','-K64M','-RTS'],log,timeout=20)
    rows=log.read_text().splitlines();h.require(rows[-1:] == ['PASS'] and len(rows)==9,'incomplete constructor probe')
    cases=[]
    for line in rows[:-1]:
        name,*values=line.split('\t');v=list(map(int,values));h.require(len(v)==5 and v[0]==v[2]+v[4],'bad constructor accounting')
        cases.append(dict(zip(['name','requests','polls','hits','misses','shutdown_flushes'],[name,*v])))
    sources=[Path(__file__),HERE/'CollectOneProbe.hs',HERE/'run.py',HERE/'completion_history.py',args.build_packages]
    report={'scope':'T6.1.1 separate candidate design/type feasibility, no actual driver run, protocol proof or runtime improvement claim',
            'compiler':compiler,'optimization':'-O0','sources':{str(p.resolve().relative_to(ROOT)) if p.resolve().is_relative_to(ROOT) else str(p.resolve()):h.file_hash(p) for p in sources},
            'build':provenance,'candidate_patch_sha256':h.file_hash(out/'candidate.patch'),'effective_command_sha256':h.file_hash(out/'ghc-command.json'),
            'probe_cases':cases,'probe_resources':resources,'budget_sanity_checks':budget_checks(),'complete':True}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('report:',out/'report.json',flush=True)


if __name__=='__main__':main()
