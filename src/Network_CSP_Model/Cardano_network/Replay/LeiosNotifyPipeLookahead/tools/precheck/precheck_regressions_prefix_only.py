#!/usr/bin/env python3
"""Regress necessary prechecks plus unchanged complete paired fallback on explicit binaries.

Prior-wave tools and fixture inventories are read-only. A passing necessary
guard is never itself classified as protocol acceptance. This runs synthetic
normalized fixtures, not capture acquisition or deployed conformance checks.
"""
import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
TOOLS = HERE.parent


def load(name, path):
    """Load existing fixture/measurement definitions without running their command entrypoints."""
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


COST = load('precheck_cost', TOOLS/'replay_cost.py')
CLI = COST.CLI
REJECTION = load('precheck_rejection', TOOLS/'rejection-cost/rejection_cost.py')
EXACT = load('precheck_exact', TOOLS/'basis-regressions/regressions.py')
FOLLOWUP = load('precheck_followup', TOOLS/'search-order/followup_search.py')
ROOT = COST.ROOT
BASELINE_SHA256 = '7c3ab336c11ef53de9b2feb4905a50b67d99e98834b976fe58cf21be4c837401'
REJECTION_RECORD = TOOLS/'rejection-cost/result-rejection-cost-20261105.json'
POSITIVE_RECORD = TOOLS/'search-order/result-search-order-20261105.json'
SUITES = ('guards', 'rejection', 'positive', 'cli', 'exact')


def paired(name, client, server, expected, rationale, local_pass=None, packet_pass=None, contract='node-next'):
    """Guard expectations are mathematical review targets, not black-box branch instrumentation."""
    return {'name': name, 'input': CLI.pair_text(list(enumerate(client,11)),list(enumerate(server,17))),
            'args': ['--paired-notify-lookahead','{input}','--next-contract',contract,
                     '--observation','driver-log','--assume-fresh'],
            'expected': expected, 'contains': [], 'rationale': rationale,
            'reviewed_local_guard_pass': local_pass, 'reviewed_packet_guard_pass': packet_pass}


def guard_cases():
    """Protect Lead, exact common prefixes and counterexamples to sufficiency of the guards."""
    a = 'BlockOffer 43 23 31'
    votes = 'Votes 11:23,1f:37,11:23'
    cases = [
        paired('lead_both_send_hooks_pending',['Recv '+a],['Recv RequestNext'],'accepted-prefix',
               'Actual first request/reply commits permit both Receive hooks before both Send hooks.',True,True),
        paired('client_request_eof',['Send RequestNext'],[],'accepted-prefix',
               'One recorded request can precede every server record.',True,True),
        paired('server_receive_eof',[],['Recv RequestNext'],'accepted-prefix',
               'One physical unrecorded client Request is allowed by the pending sender slot.',True,True),
        paired('server_reply_client_eof',['Send RequestNext'],['Recv RequestNext','Send '+a],'accepted-prefix',
               'The server can record a reply whose client Receive is still absent at EOF.',True,True),
        paired('lead_request_recorded_reply_send_pending',['Recv '+a,'Send RequestNext'],['Recv RequestNext'],'accepted-prefix',
               'The client Send can finish after its early reply, while the server Send remains pending.',True,True),
        paired('both_directions_one_ahead',['Recv '+a,'Send RequestNext','Recv '+a],
               ['Recv RequestNext','Recv RequestNext','Send '+a],'accepted-prefix',
               'Handle/publish/collect reply1 after recording Request1; commit Request2, receive it on server, finish server Send1, then commit/receive reply2. Both second Sends remain pending.',True,True),
        paired('fallback_two_server_requests_no_client_send',[],['Recv RequestNext','Recv RequestNext'],'protocol-rejected',
               'Both local quotients and common-prefix guards pass. Conservation bounds unrecorded client commits by one pending Send, which cannot account for two recorded server receives.',True,True),
        paired('fallback_three_receives_one_send',['Send RequestNext'],['Recv RequestNext']*3,'protocol-rejected',
               'Both local quotients/common-prefix guards pass, but physical client commits are at most one recorded Send plus one pending hook; three receives are impossible.',True,True),
        paired('local_no_server_request',['Recv '+a],['Send '+a],'protocol-rejected',
               'Channel sequences match exactly, but initial server has zero request credit and cannot send a reply.',False,True),
        paired('local_done_without_quit',['Recv Done'],['Send Done'],'protocol-rejected',
               'Channel sequences match, but both source controls require a prior Quit record before Done.',False,True),
        paired('lead_cannot_quit',['Recv '+a,'Send Quit'],['Recv RequestNext','Send '+a,'Recv Quit'],'protocol-rejected',
               'A client Lead state must finish its pending Request Send before Quit; physical commit alone does not change its main continuation.',False,False),
    ]
    cases += [
        paired('node_normal_after_recorded_quit',
               ['Send RequestNext','Send Quit','Recv '+a,'Recv Done'],
               ['Recv RequestNext','Recv Quit','Send '+a,'Send Done'],'accepted-prefix',
               'Select the normal reply before quitFlag publication (possibly after recorded Quit while signalQuit still has flag=false); the chosen normal survives later flag publication. Client drains its actual response and dummy Quit marker before Done.',True,True),
        paired('generic_canceled_before_quit',['Send RequestNext','Recv Canceled'],
               ['Recv RequestNext','Send Canceled'],'accepted-prefix',
               'The generic server callback contract permits explicit Canceled before Quit; client successful Canceled handling is generic.',True,True,contract='generic-next'),
        paired('node_canceled_before_quit',['Send RequestNext','Recv Canceled'],
               ['Recv RequestNext','Send Canceled'],'protocol-rejected',
               'The same matching packet histories fail the node-next local server language: no recorded Quit means no flag publication, and node callbacks cannot return Canceled.',False,True),
    ]
    def late(name, last_client, last_server):
        return paired(name,
            ['Send RequestNext','Recv '+a,'Send RequestNext','Recv '+last_client,'Send Quit','Recv Done'],
            ['Recv RequestNext','Send '+a,'Recv RequestNext','Send '+last_server,'Recv Quit','Send Done'],
            'protocol-rejected','Both local traces are valid, but exact FIFO packets disagree after the first shared normal reply. Pending suffix hooks cannot repair this common-prefix mismatch.',True,False)
    cases += [late('common_prefix_hash_mismatch','BlockOffer 49 23 31',a),
              late('common_prefix_vote_duplicate_removed','Votes 11:23,1f:37',votes),
              late('common_prefix_vote_order_changed','Votes 1f:37,11:23,11:23',votes)]
    return cases


def generated_cases(selected):
    """Reuse complete prior matrices; hash-check every referenced fixture before any model run."""
    result = []
    def add(suite, case):
        case = dict(case)
        case['suite'] = suite
        case.setdefault('contains', [])
        result.append(case)
    if 'guards' in selected:
        for case in guard_cases(): add('guards',case)
    if 'rejection' in selected:
        reference=json.loads(REJECTION_RECORD.read_text())
        hashes={c['name']:c['fixture_sha256'] for c in reference['cases']}
        for case in REJECTION.controls()+list(REJECTION.series_cases([1,2,4,8,16,32,64])):
            text=REJECTION.fixture_text(case)
            assert hashlib.sha256(text.encode()).hexdigest()==hashes[case['name']]
            add('rejection',{'name':case['name'],'input':text,
                'args':['--paired-notify-lookahead','{input}','--next-contract','node-next','--observation','driver-log','--assume-fresh'],
                'expected':case['expected'],'series':case['series'],'rationale':case['rationale'],'reference_fixture_sha256':hashes[case['name']]})
    if 'positive' in selected:
        reference=json.loads(POSITIVE_RECORD.read_text())
        hashes={c['name']:c['fixture_sha256'] for c in reference['candidate_scale']['cases']}
        for mode in COST.MODES:
            for family in COST.FAMILIES:
                for n in [1,2,4,8,16,32,64]:
                    name=f'{mode}_{family}_repeated_{n:06d}'
                    text=COST.case_text(COST.workload(family,n),'paired' if mode=='paired' else mode)
                    assert hashlib.sha256(text.encode()).hexdigest()==hashes[name]
                    args=(['--paired-notify-lookahead','{input}'] if mode=='paired' else
                          ['--notify-lookahead','{input}','--role','client' if mode=='localclient' else 'server'])
                    add('positive',{'name':name,'input':text,'args':args+['--next-contract','node-next','--observation','driver-log','--assume-fresh'],
                        'expected':'accepted-prefix','series':mode+'_'+family,'reference_fixture_sha256':hashes[name]})
        hashes={c['name']:c['fixture_sha256'] for c in reference['candidate_followup']['cases']}
        for case in FOLLOWUP.cases():
            text=COST.case_text(case['data'],'paired')
            assert hashlib.sha256(text.encode()).hexdigest()==hashes[case['name']]
            add('positive',{'name':case['name'],'input':text,
                'args':['--paired-notify-lookahead','{input}','--next-contract','node-next','--observation','driver-log','--assume-fresh'],
                'expected':'accepted-prefix','series':'followup_'+case['series'][0]+'_'+case['series'][1]+'_'+case['series'][2],
                'reference_fixture_sha256':hashes[case['name']]})
    if 'cli' in selected:
        for case in CLI.fixtures(): add('cli',case)
    if 'exact' in selected:
        for case in EXACT.fixtures(): add('exact',case)
    assert len({(case['suite'],case['name']) for case in result})==len(result)
    return result


def selftest():
    """Check exact fixture inventories and guard controls without launching a checker."""
    cases=generated_cases(SUITES)
    counts=dict(Counter(c['suite'] for c in cases))
    assert counts=={'guards':17,'rejection':72,'positive':105,'cli':62,'exact':18},counts
    assert sum(c['expected']=='accepted-prefix' for c in guard_cases())==8
    for case in guard_cases():
        if case['name'].startswith('fallback_'):
            assert case['expected']=='protocol-rejected' and case['reviewed_local_guard_pass'] and case['reviewed_packet_guard_pass']
    return {'selftest':'passed','suite_cases':counts,'total_cases':len(cases),
            'prior_fixture_hashes_verified':177,'checker_processes_launched':0,
            'guard_pass_is_not_acceptance':True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary',type=Path)
    parser.add_argument('--expected-sha256')
    parser.add_argument('--out',type=Path)
    parser.add_argument('--suites',default=','.join(SUITES))
    parser.add_argument('--timeout',type=float,default=2)
    parser.add_argument('--total-timeout',type=float,default=180)
    parser.add_argument('--selftest',action='store_true')
    args=parser.parse_args()
    if args.selftest:
        if args.binary or args.out:parser.error('--selftest does not launch a binary')
        print(json.dumps(selftest(),indent=2));return
    if not args.binary or not args.out:parser.error('--binary and --out are required')
    selected=args.suites.split(',')
    if len(set(selected))!=len(selected) or not set(selected)<=set(SUITES):parser.error('unknown/duplicate suite')
    if not math.isfinite(args.timeout) or not 0<args.timeout<=15:parser.error('--timeout must be finite in (0,15]')
    if not math.isfinite(args.total_timeout) or not args.timeout<=args.total_timeout<=300:parser.error('--total-timeout must be finite in [--timeout,300]')
    binary,out=args.binary.resolve(),args.out.resolve()
    if not binary.is_file() or not os.access(binary,os.X_OK):parser.error('--binary must be an existing executable')
    binary_sha=COST.sha256(binary)
    if args.expected_sha256 and binary_sha!=args.expected_sha256:parser.error('binary hash mismatch')
    if out.exists() or out.is_relative_to(ROOT):parser.error('--out must be a new directory outside the repository')
    prepared=generated_cases(selected)
    out.mkdir(parents=True);(out/'fixtures').mkdir()
    sources=[Path(__file__),TOOLS/'replay_cost.py',TOOLS/'test_lookahead_cli.py',
             TOOLS/'rejection-cost/rejection_cost.py',TOOLS/'basis-regressions/regressions.py',
             TOOLS/'search-order/followup_search.py',REJECTION_RECORD,POSITIVE_RECORD]
    legacy=CLI.legacy_hashes()
    report={'schema':'lookahead-precheck-regressions-v1','started_at_utc':datetime.now(timezone.utc).isoformat(),
            'binary':str(binary),'binary_sha256':binary_sha,'baseline_unique_binary_sha256':BASELINE_SHA256,
            'source_sha256':{str(path.relative_to(ROOT)):COST.sha256(path) for path in sources},
            'limits':{'seconds_per_case':args.timeout,'total_seconds':args.total_timeout,'heap':'512M','sampled_group_rss_kib':3*1024*1024,'output_bytes':65536},
            'requested_suite_counts':dict(Counter(c['suite'] for c in prepared)), 'legacy_main':legacy,'cases':[],
            'scope':'Synthetic normalized regression inputs; necessity of prechecks is not sufficiency or a raw/deployed capture theorem.',
            'limitations':['Guard-pass annotations are source-level review targets, not instrumentation of the internal runtime branch.',
                'Root kernel gates establish precheck pass and fallback rejection for the two-server-requests/no-client-send counterexample.',
                'Time/resource failures remain inconclusive and block larger members of a rejection/positive series.',
                'No successful completion is inferred from EOF; one pending Send per direction is deliberately allowed.']}
    started,blocked=time.monotonic(),set()
    for case in prepared:
        label=case['suite']+'_'+case['name']
        fixture=out/'fixtures'/(label+'.txt')
        if case['input'] is not None:fixture.write_text(case['input'])
        row={key:value for key,value in case.items() if key not in ('input','args','contains')}
        row.update(fixture=str(fixture),fixture_sha256=COST.sha256(fixture) if fixture.is_file() else None)
        series=(case['suite'],case.get('series')) if case.get('series') else None
        if series and series in blocked:
            row.update(status='not-run',inconclusive_reason='earlier-series-inconclusive')
        elif args.total_timeout-(time.monotonic()-started)<args.timeout:
            row.update(status='not-run',inconclusive_reason='total-budget-before-full-case')
        else:
            argv=[str(binary),*[str(fixture) if arg=='{input}' else arg for arg in case['args']],'+RTS','-M512M','-s','-RTS']
            row.update(COST.measure(argv,out,label,timeout=args.timeout))
            text=Path(row['logs']['stdout']['path']).read_text()
            row['missing_expected_details']=[s for s in case['contains'] if s not in text]
            if row['status']=='inconclusive' and series:blocked.add(series)
        row['expectation_met']=row['status']==case['expected'] and not row.get('missing_expected_details')
        report['cases'].append(row)
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(label,row['status'],row.get('seconds'),flush=True)
    report['seconds']=round(time.monotonic()-started,6)
    report['counts']=dict(Counter(c['status'] for c in report['cases']))
    report['by_suite']={suite:dict(Counter(c['status'] for c in report['cases'] if c['suite']==suite)) for suite in selected}
    report['all_expected']=all(c['expectation_met'] for c in report['cases'])
    report['unexpected_completed_results']=[c['suite']+'/'+c['name'] for c in report['cases'] if c['status'] not in ('inconclusive','not-run') and not c['expectation_met']]
    report['binary_unchanged']=COST.sha256(binary)==binary_sha
    report['sources_unchanged']=all(COST.sha256(ROOT/path)==sha for path,sha in report['source_sha256'].items())
    legacy['after_sha256']=COST.sha256(CLI.LEGACY)
    legacy['unchanged']=legacy['head_sha256']==legacy['before_sha256']==legacy['after_sha256']
    report['completed_at_utc']=datetime.now(timezone.utc).isoformat()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'all_expected':report['all_expected'],'by_suite':report['by_suite'],'report':str(out/'report.json')},indent=2))
    raise SystemExit(0 if report['all_expected'] and report['binary_unchanged'] and report['sources_unchanged'] and legacy['unchanged'] else 1)


if __name__=='__main__':main()
