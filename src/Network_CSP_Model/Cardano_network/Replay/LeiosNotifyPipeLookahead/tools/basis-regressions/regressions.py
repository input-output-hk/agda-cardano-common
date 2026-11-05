#!/usr/bin/env python3
"""Independent exact-value regressions for whole-candidate basis deduplication.

Use immutable existing test_lookahead_cli execute/classify helpers. No checker
runs during --selftest; actual runs require an explicit binary and fresh output
directory outside the repository. Runtime outcome never determines expectation.
"""
import argparse
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
TOOLS = HERE.parent
ROOT = next(parent for parent in HERE.parents if (parent/'src/csp-ptree.agda-lib').is_file())
HELPER = TOOLS/'test_lookahead_cli.py'
spec = importlib.util.spec_from_file_location('immutable_lookahead_cli_tests', HELPER)
CLI = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CLI)


def fixtures():
    """Every positive has a source witness; negative payloads contradict exact packet conservation."""
    cases = []
    sample = 'Votes 11:23,1f:37,11:23'

    def paired(name, client, server, status, contract, reason, lemma):
        cases.append({'name': name + '_' + contract.replace('-', '_'),
            'input': CLI.pair_text([(101+2*i, row) for i,row in enumerate(client)],
                                   [(201+2*i, row) for i,row in enumerate(server)]),
            'args':['--paired-notify-lookahead','{input}','--next-contract',contract,
                    '--observation','driver-log','--assume-fresh'],
            'expected':status,'contains':[], 'model_justification':reason,'kernel_obligation':lemma})

    for contract in ['generic-next','node-next']:
        for label, packet in [('repeated_inner_duplicate_votes',sample),('representative_collision','Votes -')]:
            client=['Send RequestNext','Recv '+packet]*2
            server=['Recv RequestNext','Send '+packet]*2
            paired(label,client,server,'accepted-prefix',contract,
                'Two actual sequential round witnesses preserve all eight visible records; normal callbacks are allowed by either contract. Candidate deduplication does not remove log rows.',
                'DriverUniqueTests.Repeated.source / DriverUniqueTests.one-candidate')
        paired('delayed_both_receive_hooks',['Recv '+sample],['Recv RequestNext'],'accepted-prefix',contract,
            'One committed Request can be received before its client Send hook; one exact committed reply can be received before its server Send hook. Both logs may end with those hooks pending.',
            'DriverUniqueTests.computed-node-prefix/computed-generic-prefix (same parametric source race); DriverBasisExecutionTests.both-delayed')
        paired('delayed_hooks_recorded',['Recv '+sample,'Send RequestNext'],['Recv RequestNext','Send '+sample],
            'accepted-prefix',contract,
            'The explicit delayed-Send source schedule records both Receive hooks before their corresponding Sends and preserves the full ordered duplicate vote list.',
            'DriverUniqueTests.delayed-send / DriverDecideNativeTests.paired-source')
        paired('request_only_eof',['Send RequestNext'],[],'accepted-prefix',contract,
            'The first client Request can be committed and recorded while no server record has occurred. EOF is a finite prefix.',
            'DriverDecideTests.request-server-eof')
        paired('receive_only_eof',[],['Recv RequestNext'],'accepted-prefix',contract,
            'The server can decode and record the first committed Request before the delayed client Send record.',
            'DriverDecideTests.receive-before-client-send')
        paired('exact_inner_duplicate_votes',['Recv '+sample],['Recv RequestNext','Send '+sample],
            'accepted-prefix',contract,
            'The ordinary exact response matches the committed reply; the first client Send may still be pending.',
            'DriverUniqueTests.Repeated.round / DriverDecideNativeTests.source')
        paired('inner_duplicate_removed',['Recv Votes 11:23,1f:37'],['Recv RequestNext','Send '+sample],
            'protocol-rejected',contract,
            'For all three endpoint merges, server history begins with the unmodified Votes packet while client history begins with a different packet. Pending hooks cannot change the first packet-list equality.',
            'DriverUniqueTests.cannot-trim')
        paired('inner_vote_order_changed',['Recv Votes 1f:37,11:23,11:23'],['Recv RequestNext','Send '+sample],
            'protocol-rejected',contract,
            'The two payloads contain the same vote multiset but different ordered lists. Exact FIFO conservation excludes every merged source execution.',
            'DriverUniqueTests.cannot-reorder')
    return cases


def selftest():
    """Validate fixture invariants without invoking any checker or deriving expectations from results."""
    cases=fixtures()
    assert len(cases)==18 and len({case['name'] for case in cases})==18
    for case in cases:
        assert case['expected'] in ['accepted-prefix','protocol-rejected']
        assert case['model_justification'] and case['kernel_obligation']
        assert case['input'].startswith('pair LeiosNotifyP ')
        assert '--assume-fresh' in case['args'] and '--next-contract' in case['args']
        if 'repeated_inner_duplicate_votes' in case['name']:
            assert case['input'].count('Votes 11:23,1f:37,11:23')==4
            assert len(case['input'].splitlines())==11
        if 'representative_collision' in case['name']:
            assert case['input'].count('Votes -')==4
        if case['expected']=='protocol-rejected':
            assert len(case['input'].splitlines())==6
    assert CLI.classify(1,'','I/O failure')[0]=='inconclusive'
    assert CLI.classify(1,'protocol-rejected\n','heap exhausted')[0]=='inconclusive'
    return {'selftest':'passed','fixtures':len(cases),'checker_executed':False,
            'expectations':'Independent source witnesses/packet conservation, not observed checker behavior.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary',type=Path)
    parser.add_argument('--expect-sha256')
    parser.add_argument('--out',type=Path)
    parser.add_argument('--timeout',type=float,default=2)
    parser.add_argument('--selftest',action='store_true')
    args=parser.parse_args()
    if args.selftest:
        if args.binary or args.out or args.expect_sha256:
            parser.error('--selftest does not accept executable/output arguments')
        print(json.dumps(selftest(),indent=2));return
    if not args.binary or not args.out:
        parser.error('--binary and --out are required')
    binary,out=args.binary.resolve(),args.out.resolve()
    if not binary.is_file() or not os.access(binary,os.X_OK):
        parser.error('--binary must be an explicit executable')
    if out.is_relative_to(ROOT) or out.exists():
        parser.error('--out must be a new directory outside the repository')
    if not math.isfinite(args.timeout) or args.timeout<=0 or args.timeout>30:
        parser.error('--timeout must be positive and at most 30 seconds per case')
    initial=CLI.sha256(binary)
    if args.expect_sha256 and (not re.fullmatch('[0-9a-f]{64}',args.expect_sha256) or initial!=args.expect_sha256):
        parser.error('binary does not match the requested immutable SHA-256')
    out.mkdir(parents=True,exist_ok=False);(out/'fixtures').mkdir()
    helper_before=CLI.sha256(HELPER)
    report={'scope':'T3 exact-value/dedup regressions; runtime evidence is separate from kernel proofs',
            'binary':str(binary),'binary_sha256':initial,'helper_sha256':helper_before,
            'heap':'512M','timeout_seconds_per_case':args.timeout,'checks':[],
            'expected_cases':len(fixtures()),'selftest':selftest()}
    for case in fixtures():
        result=CLI.execute(binary,case,out,args.timeout)
        result.update(model_justification=case['model_justification'],kernel_obligation=case['kernel_obligation'])
        report['checks'].append(result)
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(case['name']+': '+result['actual'],flush=True)
        if result['actual']=='inconclusive':
            report['stopped_after_inconclusive']=case['name'];break
    report['binary_unchanged']=CLI.sha256(binary)==initial
    report['helper_unchanged']=CLI.sha256(HELPER)==helper_before
    report['complete']=len(report['checks'])==report['expected_cases']
    report['passed']=report['complete'] and all(item['passed'] for item in report['checks']) and report['binary_unchanged'] and report['helper_unchanged']
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    raise SystemExit(0 if report['passed'] else 4)


if __name__=='__main__':
    main()
