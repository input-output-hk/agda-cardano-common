#!/usr/bin/env python3
"""Compare a root-authorized one-import ordering change on immutable replay inputs.

No baseline executable is launched. Old 83/3/20 outcome records remain the
baseline; every expected outcome, flag and resource qualification is preserved.
"""
import argparse
from collections import Counter
from datetime import datetime,timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent;TOOLS=HERE.parent
def load(name,path):
    """Reuse committed producers and bounded monitors without their entrypoints."""
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
MICRO=load('menu_full_micro',HERE/'menu_profile.py')
STRESS=load('menu_full_stress',TOOLS/'search-stress/search_stress.py')
CYCLE=load('menu_full_cycle',TOOLS/'shutdown-stress/cycle_probe.py')
COST,ROOT=STRESS.COST,STRESS.ROOT
DD='src/Cardano_network/Replay/LeiosNotifyPipeLookahead/DriverDecide.agda'
OLD_IMPORT='import Cardano_network.LeiosNotifyPipeLookahead.DriverSearchOrder Notification notificationEq as Ordering'
NEW_IMPORT='import Cardano_network.Replay.LeiosNotifyPipeLookahead.ReadyGateOrder Notification notificationEq as Ordering'


def protect_production(allow_order_import):
    """Permit exactly the explicitly authorized import substitution, with every other old byte fixed."""
    records=subprocess.check_output(['git','-C',str(ROOT),'ls-tree','-rz','a1b7b948','--','src']).split(b'\0')
    result={};changed=[]
    for record in records:
        if not record:continue
        header,raw=record.split(b'\t',1)
        if not raw.endswith(b'.agda'):continue
        name=raw.decode();current=(ROOT/name).read_bytes()
        actual=hashlib.sha1(b'blob '+str(len(current)).encode()+b'\0'+current).hexdigest()
        expected_oid=header.decode().split()[2]
        if name==DD and allow_order_import:
            original=subprocess.check_output(['git','-C',str(ROOT),'show','a1b7b948:'+name]).decode()
            if original.count(OLD_IMPORT)!=1:raise ValueError('baseline import shape changed')
            expected=original.replace(OLD_IMPORT,NEW_IMPORT,1).encode()
            if current!=expected:raise ValueError('DriverDecide differs beyond the authorized one import')
            changed.append(name)
        elif actual!=expected_oid:raise ValueError('existing production/proof source changed: '+name)
        result[name]=hashlib.sha256(current).hexdigest()
    return dict(sha256=result,authorized_deltas=changed,delta_scope='Only one DriverDecide ordering import; current hashes do not establish executable build provenance.')


def positives():
    """Reuse the exact twenty ordinary paired-CLI inputs and prior expected statuses."""
    old=json.loads((TOOLS/'cost-profile/result-cost-profile-20261105.json').read_text())
    baseline={row['fixture_name']:row for row in old['runtime']['cases']
              if row['mode']=='paired-cli' and row['known_positive']}
    result=[]
    for data in MICRO.PROFILE.fixtures():
        if not data['known_positive']:continue
        row=dict(data);row['baseline']=baseline[row['name']]
        assert hashlib.sha256(row['input'].encode()).hexdigest()==row['baseline']['fixture_sha256']
        result.append(row)
    assert len(result)==20
    return result


def selftest():
    """Validate preserved input/flag baselines without calling historical production-ledger tests."""
    old=MICRO.protect_old();generated=STRESS.cases()
    frozen=json.loads((TOOLS/'search-stress/inventory-20261105.json').read_text())['cases']
    for row,expected in zip(generated,frozen,strict=True):
        assert row['name']==expected['name'] and hashlib.sha256(row['input'].encode()).hexdigest()==expected['fixture_sha256']
        assert row['args']==expected['args'] and row['expected']==expected['expected']
    crossing=compare_rows([dict(name='control',status='inconclusive')],
        [dict(name='control_paired-cli',fixture_name='control',status='accepted-prefix')])
    assert crossing['no_completed_verdict_disagreement'] and len(crossing['status_changes'])==1
    wrong=compare_rows([dict(name='control',status='protocol-rejected')],
        [dict(name='control',status='accepted-prefix')])
    assert not wrong['no_completed_verdict_disagreement']
    return dict(selftest='passed',stress_inputs=83,positive_inputs=len(positives()),cycle_inputs=3,
        protected_old_tools=len(old),baseline_model_runs=0,checker_processes_launched=0,
        historical_production_ledger_not_reasserted=True)


def compare_rows(current,baseline):
    """Keep every deadline crossing separate from completed verdict disagreements."""
    changes=[];disagreements=[]
    completed={'accepted-prefix','protocol-rejected','invalid-input'}
    for row,before in zip(current,baseline,strict=True):
        current_name=row.get('fixture_name',row.get('name'))
        old_name=before.get('fixture_name',before.get('name'))
        assert current_name==old_name,(current_name,old_name)
        if row['status']!=before['status']:
            changes.append(dict(name=current_name,baseline_status=before['status'],candidate_status=row['status'],
                baseline_seconds=before.get('seconds'),candidate_seconds=row.get('seconds')))
        if row['status'] in completed and before['status'] in completed and row['status']!=before['status']:
            disagreements.append(changes[-1])
    return dict(baseline_counts=dict(Counter(row['status'] for row in baseline)),
        candidate_counts=dict(Counter(row['status'] for row in current)),status_changes=changes,
        no_completed_verdict_disagreement=not disagreements,completed_verdict_disagreements=disagreements)


def main():
    """Run the existing full stress/cycle producers, then fixed positive paired CLI cases serially."""
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary',type=Path);parser.add_argument('--expected-sha256')
    parser.add_argument('--out',type=Path);parser.add_argument('--allow-order-import',action='store_true')
    parser.add_argument('--selftest',action='store_true');args=parser.parse_args()
    if args.selftest:
        if args.binary or args.out:parser.error('pure selftest does not launch models')
        print(json.dumps(selftest(),indent=2));return 0
    if not args.binary or not args.expected_sha256 or not args.out or not args.allow_order_import:
        parser.error('binary/hash/out and explicit root-authorized --allow-order-import are required')
    binary,out=args.binary.resolve(),args.out.resolve()
    if not binary.is_file() or not os.access(binary,os.X_OK) or COST.sha256(binary)!=args.expected_sha256:parser.error('binary missing or hash mismatch')
    if out.exists() or out.is_relative_to(ROOT):parser.error('--out must be new and outside repository')
    production=protect_production(True);old=MICRO.protect_old();pure=selftest()
    out.mkdir(parents=True)
    (out/'production-before.json').write_text(json.dumps(production,indent=2)+'\n')
    started=time.monotonic()
    stress_args=['--binary',str(binary),'--expected-sha256',args.expected_sha256,
        '--out',str(out/'stress83'),'--timeout','2','--total-timeout','180']
    stress_exit=STRESS.main(stress_args)
    stress_path=out/'stress83/report.json';stress=json.loads(stress_path.read_text())
    baseline83=json.loads((TOOLS/'shutdown-stress/result-shutdown-stress-20261105.json').read_text())
    for row,before,frozen in zip(stress['cases'],baseline83['cases'],json.loads((TOOLS/'search-stress/inventory-20261105.json').read_text())['cases'],strict=True):
        assert row['name']==before['name']==frozen['name']
        assert row['expected']==before['expected']==frozen['expected']
        assert row['fixture_sha256']==before['fixture_sha256']==frozen['fixture_sha256']
        if 'argv' in row:
            template=[str(row['fixture']) if value=='{input}' else value for value in frozen['args']]+['+RTS','-M512M','-s','-RTS']
            assert row['argv'][1:]==template
    cycle_args=['python3','-I','-B',str(TOOLS/'shutdown-stress/cycle_probe.py'),'--binary',str(binary),
        '--expected-sha256',args.expected_sha256,'--out',str(out/'cycle3')]
    saved_argv=sys.argv
    try:
        sys.argv=cycle_args[3:]
        cycle_exit=CYCLE.main()
    finally:
        sys.argv=saved_argv
    cycle_path=out/'cycle3/report.json';cycle=json.loads(cycle_path.read_text())
    cycle_before=json.loads((TOOLS/'shutdown-stress/result-ordering-cycle-20261105.json').read_text())
    for row,before in zip(cycle['cases'],cycle_before['cases'],strict=True):
        assert row['fixture_sha256']==before['fixture_sha256'] and row['expected']==before['expected']
    positive_dir=out/'positive20';positive_dir.mkdir();positive_rows=[];blocked=set();began=time.monotonic()
    for case in positives():
        name=case['name'];fixture=positive_dir/(name+'.txt');fixture.write_text(case['input'])
        row=dict(name=name,fixture_sha256=COST.sha256(fixture),expected='accepted-prefix',baseline_status=case['baseline']['status'])
        series=(case['family'],case['payloads'])
        if series in blocked:row.update(status='not-run',inconclusive_reason='earlier-series-inconclusive')
        elif 45-(time.monotonic()-began)<2:row.update(status='not-run',inconclusive_reason='total-budget-before-full-case')
        else:
            argv=COST.arguments(binary,'paired',fixture,'512M')
            row.update(COST.measure(argv,positive_dir,name,timeout=2,rss_limit_kib=3*1024*1024,output_limit=65536))
            before_argv=case['baseline']['argv']
            assert argv[1]==before_argv[1],name
            assert argv[2:]==[str(fixture),*before_argv[3:]],name
            if row['status']=='inconclusive':blocked.add(series)
        row['expectation_met']=row['status']=='accepted-prefix';positive_rows.append(row)
        (out/'positive20-progress.json').write_text(json.dumps(positive_rows,indent=2)+'\n')
        print('positive20',name,row['status'],row.get('seconds'),flush=True)
    result=dict(schema='lookahead-gated-full-replay-comparison-v1',recorded_at_utc=datetime.now(timezone.utc).isoformat(),
        binary=str(binary),binary_sha256=args.expected_sha256,pure_selftest=pure,
        baseline_binary_sha256='c8f9ce34ca59b4e150570cedb55e068601f736d3eb192934d492dda711d0af82',baseline_not_rerun=True,
        stress83=dict(harness_exit_code=stress_exit,full_report=str(stress_path),sha256=COST.sha256(stress_path),
            counts=stress['counts'],cases=stress['cases'],baseline_record=str(TOOLS/'shutdown-stress/result-shutdown-stress-20261105.json')),
        cycle3=dict(harness_exit_code=cycle_exit,full_report=str(cycle_path),sha256=COST.sha256(cycle_path),
            cases=cycle['cases'],baseline_record=str(TOOLS/'shutdown-stress/result-ordering-cycle-20261105.json')),
        positive20=dict(limits=dict(seconds_per_case=2,total_seconds=45,heap='512M',sampled_group_rss_kib=3*1024*1024),
            cases=positive_rows,counts=dict(Counter(row['status'] for row in positive_rows)),
            baseline_record=str(TOOLS/'cost-profile/result-cost-profile-20261105.json')),
        comparisons=dict(stress83=compare_rows(stress['cases'],baseline83['cases']),
            cycle3=compare_rows(cycle['cases'],cycle_before['cases']),
            positive20=compare_rows(positive_rows,[row['baseline'] for row in positives()])),
        exact_input_flags_expectations_verified=True,production_before=production,
        production_unchanged=all(COST.sha256(ROOT/path)==digest for path,digest in production['sha256'].items()),
        old_tools_before=old,old_tools_unchanged=all(COST.sha256(ROOT/path)==digest for path,digest in old.items()),
        binary_unchanged=COST.sha256(binary)==args.expected_sha256,seconds=round(time.monotonic()-started,6),
        qualifications=['Root owns the compiled source/build association; live source snapshots are not that provenance.',
            'Only one explicitly authorized ordering import differs from the old committed Agda tree.',
            'No old frozen production ledger is treated as current after that intentional import change.',
            'Timeouts and larger-series skips remain inconclusive; no expected verdict is relaxed.',
            'Historical and current elapsed totals include different launched subsets after timeouts, not universal speed guarantees.'])
    result['all_expected']=stress['all_expected'] and cycle['all_expected'] and all(row['expectation_met'] for row in positive_rows)
    path=out/'comparison.json';path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(comparison=str(path),all_expected=result['all_expected']),indent=2))
    return 0 if result['all_expected'] and result['production_unchanged'] and result['old_tools_unchanged'] and result['binary_unchanged'] else 1


if __name__=='__main__':raise SystemExit(main())
