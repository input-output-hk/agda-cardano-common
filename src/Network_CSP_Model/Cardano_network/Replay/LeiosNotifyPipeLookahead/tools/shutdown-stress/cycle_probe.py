#!/usr/bin/env python3
"""Probe a source-reviewed ordering cycle separately from the frozen 83 cases.

All-five-guard pass and expected verdicts are review annotations, not kernel
theorems or branch instrumentation. An inconclusive n=3 skips n=4.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import time

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('shutdown_cycle_coordinator',HERE/'shutdown_stress.py')
COORDINATOR=importlib.util.module_from_spec(spec)
spec.loader.exec_module(COORDINATOR)
STRESS,COST,ROOT=COORDINATOR.STRESS,COORDINATOR.COST,COORDINATOR.ROOT
NORMAL='BlockOffer 43 23 31'


def cases():
    """Retain exact endpoint-local order and equal normal values in every occurrence."""
    result=[]
    for count in (2,3,4):
        client=['Recv '+NORMAL,'Send RequestNext']*count
        server=['Recv RequestNext']*count+['Send '+NORMAL]*count
        case=STRESS.PRECHECK.paired('ordering_cycle_'+str(count),client,server,
            'accepted-prefix' if count==2 else 'protocol-rejected',
            ('Source-reviewed feasible control: commit Reply1, record Client Receive1 and '
             'Client Send1, then Server Request Receive2 while Reply1 Send remains pending; '
             'finish Server Send1, commit Reply2, then finish the second endpoint hooks.'
             if count==2 else
             'Source-reviewed strict cycle: Server Request Receive3 precedes Server SendReply1; '
             'Request3 needs Client Request Send2; that client hook follows Client Reply Receive2; '
             'Reply2 needs Server SendReply1 to clear the sole pendingServerSend slot. '
             'This is a review argument, not a kernel refutation for the fixture.'),
            local_pass=True,packet_pass=True)
        packet=STRESS.packet_inventory(client,server)
        assert packet['common_packet_prefixes_equal'] and packet['pending_send_count_bounds']
        assert packet['client_reply_receives']==packet['server_request_receives']==count
        case.update(size=count,reviewed_reply_credit_pass=True,reviewed_shutdown_pass=True,
            reviewed_all_five_pass=True,packet_inventory=packet,
            proof_status='Source review only; no new Agda fixture theorem or runtime branch observation.',
            fixture_sha256=hashlib.sha256(case['input'].encode()).hexdigest())
        result.append(case)
    return result


def selftest():
    """Check the three literal constructions without running or simulating the model."""
    generated=cases()
    assert [case['size'] for case in generated]==[2,3,4]
    assert [case['expected'] for case in generated]==['accepted-prefix','protocol-rejected','protocol-rejected']
    assert len({case['fixture_sha256'] for case in generated})==3
    for case in generated:
        assert case['input'].count('Recv '+NORMAL+'\n')==case['size']
        assert case['input'].count('Send '+NORMAL+'\n')==case['size']
        assert 'Quit' not in case['input'] and 'Done' not in case['input']
    return dict(selftest='passed',cases=3,all_five_pass_is_source_review=True,
                expected_verdicts_are_source_review=True,checker_processes_launched=0)


def main():
    """Launch at most three serial bounded cases; retain every timeout and skip."""
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary',type=Path)
    parser.add_argument('--expected-sha256')
    parser.add_argument('--out',type=Path)
    parser.add_argument('--selftest',action='store_true')
    args=parser.parse_args()
    if args.selftest:
        if args.binary or args.out:parser.error('--selftest does not launch a binary')
        print(json.dumps(selftest(),indent=2));return 0
    if not args.binary or not args.expected_sha256 or not args.out:
        parser.error('--binary, --expected-sha256 and --out are required')
    binary,out=args.binary.resolve(),args.out.resolve()
    if not binary.is_file() or not os.access(binary,os.X_OK) or COST.sha256(binary)!=args.expected_sha256:
        parser.error('candidate executable missing or hash mismatch')
    if out.exists() or out.is_relative_to(ROOT):parser.error('--out must be new and outside repository')
    old=COORDINATOR.committed_old_evidence();pure=selftest()
    sources=[Path(__file__).resolve(),HERE/'shutdown_stress.py']
    hashes={str(path.relative_to(ROOT)):COST.sha256(path) for path in sources}
    out.mkdir(parents=True);(out/'fixtures').mkdir()
    report=dict(schema='lookahead-shutdown-ordering-cycle-probe-v1',
        started_at_utc=datetime.now(timezone.utc).isoformat(),binary=str(binary),
        binary_sha256=args.expected_sha256,source_sha256=hashes,old_evidence_sha256=old,
        pure_selftest=pure,limits=dict(seconds_per_case=2,total_seconds=6,heap='512M',
            sampled_group_rss_kib=3*1024*1024,output_bytes=65536),cases=[],
        scope='Three supplementary source-reviewed fixtures; frozen 83-case inventory is unchanged.',
        limitations=['All-five-pass and expected acceptance/rejection are source-review annotations, not new kernel theorems.',
            'No binary branch instrumentation is claimed; a completed result decides the model, while timeout is inconclusive.',
            'No logger/capture completeness, native Haskell refinement or deployed conformance follows.'])
    started,blocked_reason=time.monotonic(),None
    for case in cases():
        fixture=out/'fixtures'/(case['name']+'.txt');fixture.write_text(case['input'])
        row={key:value for key,value in case.items() if key not in ('input','args','contains')}
        row['fixture']=str(fixture)
        if blocked_reason:
            row.update(status='not-run',inconclusive_reason=blocked_reason)
        elif 6-(time.monotonic()-started)<2:
            row.update(status='not-run',inconclusive_reason='total-budget-before-full-case')
        else:
            argv=[str(binary),*[str(fixture) if value=='{input}' else value for value in case['args']],
                  '+RTS','-M512M','-s','-RTS']
            row.update(COST.measure(argv,out,case['name'],timeout=2,
                rss_limit_kib=3*1024*1024,output_limit=65536))
            if row['status']=='inconclusive':blocked_reason='earlier-series-inconclusive'
        row['expectation_met']=row['status']==case['expected']
        report['cases'].append(row)
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(case['name'],row['status'],row.get('seconds'),flush=True)
        if row['status'] not in (case['expected'],'inconclusive','not-run'):
            blocked_reason='unexpected-completed-result'
    report['seconds']=round(time.monotonic()-started,6)
    report['all_expected']=all(row['expectation_met'] for row in report['cases'])
    report['unexpected_completed_results']=[row['name'] for row in report['cases']
        if row['status'] not in ('inconclusive','not-run') and not row['expectation_met']]
    report['binary_unchanged']=COST.sha256(binary)==args.expected_sha256
    report['source_unchanged']=all(COST.sha256(ROOT/path)==digest for path,digest in hashes.items())
    report['old_evidence_unchanged']=all(COST.sha256(ROOT/path)==digest for path,digest in old.items())
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(report=str(out/'report.json'),all_expected=report['all_expected']),indent=2))
    return 0 if report['all_expected'] and report['binary_unchanged'] and report['source_unchanged'] and report['old_evidence_unchanged'] else 1


if __name__=='__main__':
    raise SystemExit(main())
