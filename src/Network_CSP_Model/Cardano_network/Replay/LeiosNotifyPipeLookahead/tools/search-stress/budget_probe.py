#!/usr/bin/env python3
"""Matched diagnostic probes after two positive two-second budget crossings.

This preserves the original 83-case comparison. Three repetitions alternate
baseline/candidate order, using exact frozen fixture bytes and larger explicit
limits. These sampled measurements are not universal causal cost guarantees.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import statistics
import sys
import time

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('stress_probe_harness',HERE/'search_stress.py')
STRESS=importlib.util.module_from_spec(spec)
spec.loader.exec_module(STRESS)
COST,ROOT=STRESS.COST,STRESS.ROOT
SHA={'baseline':'d7bf4b88247a87a535d3e1639603c90c69b09a0a138a808c4fb8932de4726938',
     'candidate':'045b3a6ccdd86db4fc1b1629597dbf8cbea40e2e767d96b3e05ec5e4e332b022'}
NAMES=('positive_pipeline_repeated_002048','positive_delayed-send_repeated_004096')


def fixtures():
    """Bind the two original inputs to the frozen inventory, without editing it."""
    inventory=json.loads((HERE/'inventory-20261105.json').read_text())
    expected={case['name']:case for case in inventory['cases']}
    generated={case['name']:case for case in STRESS.cases()}
    result=[]
    for name in NAMES:
        case=generated[name]
        assert hashlib.sha256(case['input'].encode()).hexdigest()==expected[name]['fixture_sha256']
        assert case['args']==expected[name]['args'] and case['expected']=='accepted-prefix'
        result.append(case)
    return result


def plan():
    """Balance first-executable order across the six fixture/repetition pairs."""
    result=[]
    for index,case in enumerate(fixtures()):
        for repetition in range(3):
            order=('baseline','candidate') if (index+repetition)%2==0 else ('candidate','baseline')
            for position,label in enumerate(order):
                result.append(dict(name=case['name'],repetition=repetition+1,
                    executable=label,order=position+1,first_executable=order[0]))
    return result


def selftest():
    """Check exact fixture identities and alternating order without model processes."""
    steps=plan()
    assert len(steps)==12
    first=[step['first_executable'] for step in steps if step['order']==1]
    assert first.count('baseline')==first.count('candidate')==3
    assert len({(step['name'],step['repetition'],step['executable']) for step in steps})==12
    return dict(selftest='passed',fixtures=len(NAMES),planned_runs=12,
        repetitions=3,first_executable_counts=dict(baseline=3,candidate=3),checker_processes_launched=0)


def main():
    """Run only the requested twelve bounded processes and retain every outcome."""
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-binary',type=Path)
    parser.add_argument('--candidate-binary',type=Path)
    parser.add_argument('--out',type=Path)
    parser.add_argument('--selftest',action='store_true')
    args=parser.parse_args()
    if args.selftest:
        print(json.dumps(selftest(),indent=2));return 0
    if not args.baseline_binary or not args.candidate_binary or not args.out:
        parser.error('both explicit binaries and --out are required')
    binaries=dict(baseline=args.baseline_binary.resolve(),candidate=args.candidate_binary.resolve())
    for label,path in binaries.items():
        if not path.is_file() or not os.access(path,os.X_OK) or COST.sha256(path)!=SHA[label]:
            parser.error(label+' executable missing or hash mismatch')
    out=args.out.resolve()
    if out.exists() or out.is_relative_to(ROOT):
        parser.error('--out must be a new directory outside the repository')
    out.mkdir(parents=True);(out/'fixtures').mkdir()
    data={case['name']:case for case in fixtures()}
    for name,case in data.items():
        (out/'fixtures'/(name+'.txt')).write_text(case['input'])
    sources=[Path(__file__).resolve(),HERE/'search_stress.py',HERE/'inventory-20261105.json',
             STRESS.TOOLS/'replay_cost.py',STRESS.TOOLS/'test_lookahead_cli.py']
    hashes={str(path.relative_to(ROOT)):COST.sha256(path) for path in sources}
    report=dict(schema='lookahead-search-budget-probe-v1',started_at_utc=datetime.now(timezone.utc).isoformat(),
        limits=dict(seconds_per_case=5,total_seconds=60,heap='512M',sampled_group_rss_kib=3*1024*1024,output_bytes=65536),
        binaries={label:dict(path=str(path),sha256=SHA[label]) for label,path in binaries.items()},
        source_sha256=hashes,pure_selftest=selftest(),cases=[],
        scope='Separate matched diagnostics; original 83-case reports, limits and expectations are unchanged.',
        limitations=['Three repetitions on one host are sampled operational observations, not a universal runtime or causal theorem.',
            '512M limits the RTS heap; whole process-group RSS has a separate sampled 3GiB ceiling.',
            'Passing a five-second probe does not retroactively complete a two-second timed-out run.'])
    started,halt=time.monotonic(),False
    for step in plan():
        case=data[step['name']];fixture=out/'fixtures'/(step['name']+'.txt')
        name=step['name']+'_r'+str(step['repetition'])+'_'+step['executable']
        row=dict(step,fixture=str(fixture),fixture_sha256=COST.sha256(fixture),expected='accepted-prefix')
        if halt:
            row.update(status='not-run',inconclusive_reason='unexpected-completed-result')
        elif 60-(time.monotonic()-started)<5:
            row.update(status='not-run',inconclusive_reason='total-budget-before-full-case')
        else:
            argv=[str(binaries[step['executable']]),*[str(fixture) if value=='{input}' else value for value in case['args']],
                  '+RTS','-M512M','-s','-RTS']
            row.update(COST.measure(argv,out,name,timeout=5,rss_limit_kib=3*1024*1024,output_limit=65536))
            if row['status'] not in ('accepted-prefix','inconclusive'):
                halt=True
        report['cases'].append(row)
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(name,row['status'],row.get('seconds'),flush=True)
    report['seconds']=round(time.monotonic()-started,6)
    report['all_expected']=all(row['status']=='accepted-prefix' for row in report['cases'])
    report['unexpected_completed_results']=[row for row in report['cases'] if row['status'] not in ('accepted-prefix','inconclusive','not-run')]
    report['binaries_unchanged']=all(COST.sha256(path)==SHA[label] for label,path in binaries.items())
    report['sources_unchanged']=all(COST.sha256(ROOT/path)==sha for path,sha in hashes.items())
    report['summary']=[]
    for name in NAMES:
        means={}
        for label in ('baseline','candidate'):
            rows=[row for row in report['cases'] if row['name']==name and row['executable']==label]
            times=[row['seconds'] for row in rows if row['status']=='accepted-prefix']
            means[label]=statistics.mean(times) if times else None
            report['summary'].append(dict(name=name,executable=label,completed=len(times),
                seconds=times,mean_seconds=means[label],median_seconds=statistics.median(times) if times else None))
        if means['baseline'] and means['candidate']:
            report['summary'].append(dict(name=name,candidate_to_baseline_mean_ratio=means['candidate']/means['baseline']))
    report['completed_at_utc']=datetime.now(timezone.utc).isoformat()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(report=str(out/'report.json'),all_expected=report['all_expected'],summary=report['summary']),indent=2))
    return 0 if report['all_expected'] and report['binaries_unchanged'] and report['sources_unchanged'] else 1


if __name__=='__main__':
    raise SystemExit(main())
