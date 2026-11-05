#!/usr/bin/env python3
"""Measure actual diagnostic production stages and the unchanged paired CLI.

All timings include process startup and parsing. Diagnostic modes additionally
share explicit field forcing. No subtraction is an exact internal CPU/heap
attribution, and a precondition pass is never protocol acceptance.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
TOOLS=HERE.parent
spec=importlib.util.spec_from_file_location('profile_cost',TOOLS/'replay_cost.py')
COST=importlib.util.module_from_spec(spec);spec.loader.exec_module(COST)
ROOT,CLI=COST.ROOT,COST.CLI
MODES=('decode-only','prechecks-only','backend-only','public-decide','paired-cli')
EXPECTED={'decode-only':('decode-complete',0),'prechecks-only':('preconditions-passed',0),
          'backend-only':('backend-accepted',0),'public-decide':('complete-accepted',0),
          'paired-cli':('accepted-prefix',0)}
TAG_CODES={'decode-complete':0,'preconditions-passed':0,'preconditions-failed':1,
           'backend-accepted':0,'backend-rejected':1,'complete-accepted':0,'complete-rejected':1}
READY=re.compile(r'client-events=(\d+);server-events=(\d+);forcing-sum=(\d+)')
CLI_SHA256='c8f9ce34ca59b4e150570cedb55e068601f736d3eb192934d492dda711d0af82'


def fixtures():
    """Freeze positive construction and explicit parser/phase controls before any executable run."""
    result=[]
    for family in ('serial','pipeline'):
        for payloads,sizes in [('repeated',(64,128,256,512,1024,2048)),('distinct',(64,128,256,512))]:
            for count in sizes:
                data=COST.workload(family,count,payloads)
                result.append(dict(name=family+'_'+payloads+'_'+format(count,'06d'),family=family,
                    payloads=payloads,count=count,input=COST.case_text(data,'paired'),
                    expected=dict(EXPECTED),review_basis=data['expectation_basis'],
                    known_positive=True))
    result += [dict(name='late_parser_error',input=CLI.pair_text(
        [(11,'Send RequestNext'),(12,'Recv Votes invalid')],[]),
        expected={mode:('invalid-input',2) for mode in MODES},known_positive=False,
        expected_detail='paired input line 5: expected client <increasing-source-line> <protocol-event>'),
        dict(name='phase_invalid_done',input=CLI.pair_text([(11,'Recv Done')],[]),
            expected={'decode-only':('decode-complete',0),'prechecks-only':('preconditions-failed',1),
                'public-decide':('complete-rejected',1),'paired-cli':('protocol-rejected',1)},
            known_positive=False)]
    return result


def diagnostic_outcome(mode,measurement,stdout):
    """Recognize completed diagnostic tags without overriding any resource/IO failure."""
    if mode=='paired-cli':
        return measurement['status'],measurement['inconclusive_reason'],None
    if measurement['inconclusive_reason'] not in (None,'missing-or-unknown-status-tag'):
        return 'inconclusive',measurement['inconclusive_reason'],None
    lines=stdout.splitlines()
    if lines and lines[0]=='invalid-input':
        return ('invalid-input',None,None) if measurement['exit_code']==2 else ('inconclusive','diagnostic-exit-mismatch',None)
    if len(lines)<3 or lines[0]!='typed-input-ready' or not READY.fullmatch(lines[1]):
        return 'inconclusive','diagnostic-ready-output-mismatch',None
    tag=lines[2]
    allowed={'decode-only':{'decode-complete'},'prechecks-only':{'preconditions-passed','preconditions-failed'},
             'backend-only':{'backend-accepted','backend-rejected'},'public-decide':{'complete-accepted','complete-rejected'}}
    if tag not in allowed[mode] or measurement['exit_code']!=TAG_CODES.get(tag):
        return 'inconclusive','diagnostic-stage-or-exit-mismatch',None
    return tag,None,dict(zip(('client_events','server_events','forcing_sum'),map(int,READY.fullmatch(lines[1]).groups())))


def rts_allocations(stderr):
    """Retain actual completed RTS statistics; absent statistics remain unknown."""
    result={}
    for name,label in [('allocated_bytes','bytes allocated in the heap'),('copied_bytes','bytes copied during GC'),
                       ('maximum_residency_bytes','bytes maximum residency')]:
        match=re.search(r'([\d,]+)\s+'+re.escape(label),stderr)
        result[name]=int(match.group(1).replace(',','')) if match else None
    return result


def selftest():
    """Check source fixtures and classification controls without launching model processes."""
    generated=fixtures()
    assert len(generated)==22 and sum(row['known_positive'] for row in generated)==20
    assert len({hashlib.sha256(row['input'].encode()).hexdigest() for row in generated})==22
    ready='typed-input-ready\nclient-events=2;server-events=2;forcing-sum=123\n'
    base=dict(status='inconclusive',inconclusive_reason='missing-or-unknown-status-tag',exit_code=0)
    for mode,(tag,code) in EXPECTED.items():
        if mode=='paired-cli':continue
        status,reason,summary=diagnostic_outcome(mode,dict(base,exit_code=code),ready+tag+'\n')
        assert status==tag and reason is None and summary['forcing_sum']==123
    assert diagnostic_outcome('prechecks-only',dict(base,exit_code=1),ready+'preconditions-failed\n')[0]=='preconditions-failed'
    assert diagnostic_outcome('backend-only',base,ready+'preconditions-passed\n')[0]=='inconclusive'
    assert diagnostic_outcome('prechecks-only',dict(base,inconclusive_reason='timeout'),ready+'preconditions-passed\n')[0]=='inconclusive'
    assert diagnostic_outcome('prechecks-only',dict(base,inconclusive_reason='runtime-resource-failure'),ready+'preconditions-passed\n')[0]=='inconclusive'
    assert diagnostic_outcome('decode-only',dict(base,exit_code=2),'invalid-input\nerror\n')[0]=='invalid-input'
    assert rts_allocations('  1,234 bytes allocated in the heap\n  9 bytes maximum residency')['allocated_bytes']==1234
    assert rts_allocations('')['allocated_bytes'] is None
    assert EXPECTED['prechecks-only'][0]!='accepted-prefix'
    return dict(selftest='passed',positive_inputs=20,controls=2,planned_mode_cases=110,
        backend_skipped_on_guard_fail_control=True,precondition_pass_is_not_acceptance=True,
        checker_processes_launched=0)


def main():
    """Run actual stages serially under fixed budgets, preserving every timeout and skip."""
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--probe-binary',type=Path)
    parser.add_argument('--probe-sha256')
    parser.add_argument('--paired-binary',type=Path)
    parser.add_argument('--out',type=Path)
    parser.add_argument('--selftest',action='store_true')
    args=parser.parse_args()
    if args.selftest:
        if args.probe_binary or args.paired_binary or args.out:parser.error('pure selftest does not launch binaries')
        print(json.dumps(selftest(),indent=2));return 0
    if not args.probe_binary or not args.probe_sha256 or not args.paired_binary or not args.out:
        parser.error('both explicit binaries, --probe-sha256 and --out are required')
    probe,paired,out=args.probe_binary.resolve(),args.paired_binary.resolve(),args.out.resolve()
    for path,want in [(probe,args.probe_sha256),(paired,CLI_SHA256)]:
        if not path.is_file() or not os.access(path,os.X_OK) or COST.sha256(path)!=want:parser.error('binary missing or hash mismatch')
    if out.exists() or out.is_relative_to(ROOT):parser.error('--out must be new and outside repository')
    out.mkdir(parents=True);(out/'fixtures').mkdir()
    sources=[Path(__file__).resolve(),TOOLS/'replay_cost.py',TOOLS/'test_lookahead_cli.py',
        TOOLS.parent/'CostProbe.agda',TOOLS.parent/'CostProbeTests.agda',TOOLS.parent/'CostProbeMain.agda',
        TOOLS.parent/'DriverDecide.agda',TOOLS.parent/'Wire/PairedAdapter.agda']
    hashes={str(path.relative_to(ROOT)):COST.sha256(path) for path in sources}
    report=dict(schema='lookahead-cost-stage-profile-v1',started_at_utc=datetime.now(timezone.utc).isoformat(),
        probe_binary=dict(path=str(probe),sha256=args.probe_sha256),paired_binary=dict(path=str(paired),sha256=CLI_SHA256),
        source_sha256=hashes,selftest=selftest(),limits=dict(seconds_per_case=2,total_seconds=90,
            heap='512M',sampled_group_rss_kib=3*1024*1024,output_bytes=65536),cases=[],
        caveats=['Every process includes startup, input parsing and reporting; no exact additive stage subtraction is claimed.',
            'All diagnostic modes additionally execute the same full structural payload forcing output before their selected stage.',
            'The forcing sum can collide and is not an identity hash; exact fixture SHA-256 identifies input bytes.',
            'The ordinary paired CLI has no added forcing pass, so it is an end-to-end contextual comparison.',
            'Precondition success is not acceptance. Backend/public modes retain the unchanged unrestricted SourceTrace proposition.',
            'RTS allocation statistics are only retained when emitted; killed/incomplete runs can have unknown allocation counts.',
            'Current source snapshots are not the compiled executable provenance; separate build records bind the probe functions.'])
    started,blocked=time.monotonic(),set()
    # Controls run first; every positive backend follows its actual measured guard pass.
    generated=fixtures();ordered=generated[-2:]+generated[:-2]
    unexpected=False
    for fixture_case in ordered:
        fixture=out/'fixtures'/(fixture_case['name']+'.txt');fixture.write_text(fixture_case['input'])
        guard_pass=False;ready_summary=None
        for mode in MODES:
            name=fixture_case['name']+'_'+mode
            expected=fixture_case['expected'].get(mode)
            row=dict(name=name,fixture_name=fixture_case['name'],mode=mode,fixture=str(fixture),
                fixture_sha256=COST.sha256(fixture),expected=None if expected is None else expected[0],
                known_positive=fixture_case['known_positive'])
            series=(fixture_case.get('family'),fixture_case.get('payloads'),mode)
            if expected is None:
                row.update(status='not-run',inconclusive_reason='backend-reserved-for-guard-pass-positives')
            elif mode=='backend-only' and fixture_case['known_positive'] and not guard_pass:
                row.update(status='not-run',inconclusive_reason='actual-preconditions-not-observed-passed')
            elif series in blocked and fixture_case['known_positive']:
                row.update(status='not-run',inconclusive_reason='earlier-series-inconclusive')
            elif 90-(time.monotonic()-started)<2:
                row.update(status='not-run',inconclusive_reason='total-budget-before-full-case')
            elif unexpected:
                row.update(status='not-run',inconclusive_reason='unexpected-completed-result')
            else:
                binary=paired if mode=='paired-cli' else probe
                argv=(COST.arguments(binary,'paired',fixture,'512M') if mode=='paired-cli' else
                    [str(binary),'--stage',mode,str(fixture),'--next-contract','node-next','--observation','driver-log','--assume-fresh','+RTS','-M512M','-s','-RTS'])
                measured=COST.measure(argv,out,name,timeout=2,rss_limit_kib=3*1024*1024,output_limit=65536)
                stdout=Path(measured['logs']['stdout']['path']).read_text();stderr=Path(measured['logs']['stderr']['path']).read_text()
                status,reason,summary=diagnostic_outcome(mode,measured,stdout)
                row.update(measured);row.update(status=status,inconclusive_reason=reason,
                    legacy_classifier=dict(status=measured['status'],reason=measured['inconclusive_reason']),
                    rts=rts_allocations(stderr),ready_summary=summary)
                if summary is not None:
                    if ready_summary is None:ready_summary=summary
                    elif summary!=ready_summary:row.update(status='inconclusive',inconclusive_reason='forcing-summary-mismatch')
                if fixture_case.get('expected_detail'):
                    row['expected_detail_present']=fixture_case['expected_detail'] in stdout
                if mode=='prechecks-only':guard_pass=row['status']=='preconditions-passed'
                if row['status']=='inconclusive' and fixture_case['known_positive']:blocked.add(series)
                elif row['status']!=expected[0]:unexpected=True
            row['expectation_met']=(expected is None and row['status']=='not-run') or (expected is not None and row['status']==expected[0] and row.get('expected_detail_present',True))
            if row.get('expected_detail_present') is False:unexpected=True
            row['source_verdict']=('accepted' if row['status'] in ('backend-accepted','complete-accepted','accepted-prefix') else
                'rejected' if row['status'] in ('backend-rejected','complete-rejected','protocol-rejected') else None)
            report['cases'].append(row);(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
            print(name,row['status'],row.get('seconds'),flush=True)
    report['seconds']=round(time.monotonic()-started,6)
    report['counts']=dict(Counter(row['status'] for row in report['cases']))
    report['all_expected']=all(row['expectation_met'] for row in report['cases'])
    report['unexpected_completed_results']=[row['name'] for row in report['cases'] if row['status'] not in ('inconclusive','not-run') and not row['expectation_met']]
    report['sources_unchanged']=all(COST.sha256(ROOT/path)==digest for path,digest in hashes.items())
    report['binaries_unchanged']=COST.sha256(probe)==args.probe_sha256 and COST.sha256(paired)==CLI_SHA256
    report['completed_at_utc']=datetime.now(timezone.utc).isoformat()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(report=str(out/'report.json'),counts=report['counts'],all_expected=report['all_expected']),indent=2))
    return 0 if report['all_expected'] and report['sources_unchanged'] and report['binaries_unchanged'] else 1


if __name__=='__main__':
    raise SystemExit(main())
