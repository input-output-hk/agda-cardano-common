#!/usr/bin/env python3
"""Compare a shutdown-gated binary with the recorded immutable wave 9 stress run.

The old 83-case harness, fixture inventory and evidence remain unchanged.
No baseline executable is launched. Necessary guards are never treated as
sufficient acceptance tests, and every timeout/skip remains inconclusive.
"""
import argparse
from collections import Counter
import copy
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
TOOLS=HERE.parent
OLD=TOOLS/'search-stress'
BASELINE_COMMIT='ae0420d6'
BASELINE_BINARY_SHA256='045b3a6ccdd86db4fc1b1629597dbf8cbea40e2e767d96b3e05ec5e4e332b022'
HARNESS_SHA256='24138fe02f5a18346e909ef2165aabcf13ca33ca84c171c68ef562f6fe0d6dec'
INVENTORY_SHA256='d92decd4c946737bee4df5c151be8e5da578608cba227a879ba102fe3f5422d2'
BASELINE_RECORD_SHA256='3f1b20c56394c3edcb1f91d92eed7211a58ee4f69e7f84b04b7955a0349bfed9'
spec=importlib.util.spec_from_file_location('shutdown_stress_harness',OLD/'search_stress.py')
STRESS=importlib.util.module_from_spec(spec)
spec.loader.exec_module(STRESS)
ROOT,COST=STRESS.ROOT,STRESS.COST
FIXTURE_FIELDS=('name','series','category','family','payloads','size','expected',
    'review_basis','kernel_reference','reviewed_local_guard_pass',
    'reviewed_packet_guard_pass','reviewed_count_guard_pass','packet_inventory')
LIMITS=dict(seconds_per_case=2.0,total_seconds=180.0,heap='512M',
    sampled_group_rss_kib=3*1024*1024,output_bytes=65536,fixture_bytes=8*1024*1024)


def sha(path):
    """Use the existing streaming source/artifact hash implementation."""
    return COST.sha256(path)


def committed_old_evidence():
    """Freeze all old stress/precheck evidence and producers against their committed bytes."""
    paths=sorted((OLD).iterdir())+sorted((TOOLS/'precheck').iterdir())
    paths += [TOOLS/'replay_cost.py',TOOLS/'test_lookahead_cli.py',
        TOOLS/'rejection-cost/rejection_cost.py',TOOLS/'basis-regressions/regressions.py',
        TOOLS/'search-order/followup_search.py',STRESS.PRECHECK.REJECTION_RECORD,
        STRESS.PRECHECK.POSITIVE_RECORD,TOOLS/'results-replay-wave9-20261105.json']
    result={}
    for path in paths:
        if not path.is_file():
            raise ValueError('unexpected non-file in frozen evidence area: '+str(path))
        relative=str(path.relative_to(ROOT))
        blob=subprocess.check_output(['git','-C',str(ROOT),'show',BASELINE_COMMIT+':'+relative])
        digest=hashlib.sha256(blob).hexdigest()
        if sha(path)!=digest:
            raise ValueError('old evidence differs from committed bytes: '+relative)
        result[relative]=digest
    assert sha(OLD/'search_stress.py')==HARNESS_SHA256
    assert sha(OLD/'inventory-20261105.json')==INVENTORY_SHA256
    assert sha(OLD/'result-search-stress-credit-20261105.json')==BASELINE_RECORD_SHA256
    return result


def baseline_and_inventory():
    """Require the retained Credit result and exact fixture inventory without /tmp dependencies."""
    baseline=json.loads((OLD/'result-search-stress-credit-20261105.json').read_text())
    inventory=json.loads((OLD/'inventory-20261105.json').read_text())
    assert baseline['binary']['sha256']==BASELINE_BINARY_SHA256
    assert baseline['limits']==LIMITS
    assert len(baseline['cases'])==len(inventory['cases'])==83
    for row,frozen in zip(baseline['cases'],inventory['cases'],strict=True):
        for key in ('name','series','category','family','payloads','size','expected',
                    'fixture_sha256','fixture_bytes'):
            assert row[key]==frozen[key],(row['name'],key)
    for current,frozen in zip(STRESS.cases(),inventory['cases'],strict=True):
        for key in (*FIXTURE_FIELDS,'args'):
            assert current[key]==frozen[key],(current['name'],key)
        assert hashlib.sha256(current['input'].encode()).hexdigest()==frozen['fixture_sha256']
    return baseline,inventory


def validate_candidate(candidate,inventory):
    """Reject fixture, expectation or flag drift, including cases skipped by a resource ceiling."""
    if candidate['limits']!=LIMITS or len(candidate['cases'])!=83:
        raise ValueError('stress limits or case inventory changed')
    for row,frozen in zip(candidate['cases'],inventory['cases'],strict=True):
        for key in (*FIXTURE_FIELDS,'fixture_sha256','fixture_bytes'):
            if row.get(key)!=frozen[key]:
                raise ValueError('fixture/review drift: '+frozen['name']+' '+key)
        if 'argv' in row:
            expected=[str(row['fixture']) if value=='{input}' else value for value in frozen['args']]
            expected+=['+RTS','-M512M','-s','-RTS']
            if row['argv'][1:]!=expected:
                raise ValueError('checker flag drift: '+frozen['name'])
    return True


def comparison(baseline,candidate,inventory):
    """Compare completed outcomes while retaining inconclusive and unlaunched cases separately."""
    validate_candidate(candidate,inventory)
    completed={'accepted-prefix','protocol-rejected','invalid-input'}
    changes=[];disagreement=[]
    for before,after in zip(baseline['cases'],candidate['cases'],strict=True):
        if before['status']!=after['status']:
            changes.append(dict(name=before['name'],category=before['category'],
                fixture_sha256=before['fixture_sha256'],baseline=before['status'],
                candidate=after['status'],baseline_seconds=before.get('seconds'),
                candidate_seconds=after.get('seconds'),expected=after['expected'],
                expectation_met=after['expectation_met']))
            if before['status'] in completed and after['status'] in completed:
                disagreement.append(before['name'])
    rows=[]
    for row in candidate['cases']:
        keys=('name','series','category','family','payloads','size','expected','status',
            'expectation_met','fixture_sha256','fixture_bytes','seconds','inconclusive_reason',
            'exit_code','peak_sampled_group_rss_kib','gnu_time','argv','timing_sha256','logs')
        rows.append({key:row[key] for key in keys if key in row})
    return dict(same_83_fixture_hashes=True,same_77_unique_inputs=True,
        same_expected_outcomes=True,same_review_annotations=True,same_flags_and_limits=True,
        no_completed_verdict_disagreement=not disagreement,completed_verdict_disagreements=disagreement,
        changes=changes,newly_completed_expected=[row['name'] for row in changes
            if row['baseline'] not in completed and row['candidate'] in completed and row['expectation_met']],
        previously_completed_now_inconclusive=[row['name'] for row in changes
            if row['baseline'] in completed and row['candidate']=='inconclusive'],
        baseline=dict(binary_sha256=BASELINE_BINARY_SHA256,counts=baseline['outcome']['counts'],
            seconds=baseline['outcome']['seconds'],not_rerun=True),
        candidate=dict(binary_sha256=candidate['binary_sha256'],counts=candidate['counts'],
            seconds=candidate['seconds'],all_expected=candidate['all_expected'],
            unexpected_completed_results=candidate['unexpected_completed_results'],
            peak_sampled_group_rss_kib=max(row.get('peak_sampled_group_rss_kib') or 0 for row in rows)),
        cases=rows)


def selftest():
    """Check immutable evidence, all old pure controls and deliberate drift detection without binaries."""
    protected=committed_old_evidence();baseline,inventory=baseline_and_inventory()
    old=STRESS.selftest()
    # Construct a report-shaped pure control from the frozen inventory, not a model oracle.
    candidate=dict(limits=LIMITS,cases=[dict(row,status='not-run') for row in inventory['cases']])
    assert validate_candidate(candidate,inventory)
    checks=[]
    for field,value in [('fixture_sha256','0'*64),('expected','accepted-prefix'),
                        ('reviewed_local_guard_pass',False)]:
        changed=copy.deepcopy(candidate);changed['cases'][0][field]=value
        try:validate_candidate(changed,inventory)
        except ValueError:checks.append(field)
        else:raise AssertionError('undetected drift: '+field)
    changed=copy.deepcopy(candidate);changed['cases'][0].update(fixture='/tmp/fixture',
        argv=['/tmp/checker','--wrong-mode'])
    try:validate_candidate(changed,inventory)
    except ValueError:checks.append('checker flags')
    else:raise AssertionError('undetected flag drift')
    changed=copy.deepcopy(candidate);changed['limits']=dict(LIMITS,seconds_per_case=5)
    try:validate_candidate(changed,inventory)
    except ValueError:checks.append('limits')
    else:raise AssertionError('undetected limit drift')
    assert all(sha(ROOT/path)==digest for path,digest in protected.items())
    return dict(selftest='passed',protected_old_files=len(protected),named_cases=83,
        unique_fixture_hashes=77,drift_controls=checks,old_pure_controls=old,
        checker_processes_launched=0)


def main(argv=None):
    """Invoke the unchanged bounded stress harness once, then preserve the exact comparison."""
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary',type=Path)
    parser.add_argument('--expected-sha256')
    parser.add_argument('--out',type=Path)
    parser.add_argument('--selftest',action='store_true')
    args=parser.parse_args(argv)
    if args.selftest:
        if args.binary or args.out:
            parser.error('--selftest does not launch a model binary')
        print(json.dumps(selftest(),indent=2));return 0
    if not args.binary or not args.expected_sha256 or not args.out:
        parser.error('--binary, --expected-sha256 and --out are required')
    binary,out=args.binary.resolve(),args.out.resolve()
    if not binary.is_file() or not os.access(binary,os.X_OK) or sha(binary)!=args.expected_sha256:
        parser.error('candidate executable missing or hash mismatch')
    if out.exists() or out.is_relative_to(ROOT):
        parser.error('--out must be a new directory outside the repository')
    protected=committed_old_evidence();baseline,inventory=baseline_and_inventory()
    pure=selftest();out.mkdir(parents=True)
    own_sha=sha(Path(__file__))
    inner=['--binary',str(binary),'--expected-sha256',args.expected_sha256,
        '--out',str(out/'harness'),'--timeout','2','--total-timeout','180']
    code=STRESS.main(inner)
    candidate_path=out/'harness/report.json';candidate=json.loads(candidate_path.read_text())
    result=comparison(baseline,candidate,inventory)
    result.update(schema='lookahead-shutdown-stress-comparison-v1',
        recorded_at_utc=datetime.now(timezone.utc).isoformat(),coordinator_sha256=own_sha,
        coordinator_unchanged=sha(Path(__file__))==own_sha,old_evidence_sha256=protected,
        old_evidence_unchanged=all(sha(ROOT/path)==digest for path,digest in protected.items()),
        baseline_record=dict(path=str((OLD/'result-search-stress-credit-20261105.json').relative_to(ROOT)),
            sha256=BASELINE_RECORD_SHA256,committed_in=BASELINE_COMMIT),
        full_candidate_report=dict(path=str(candidate_path),sha256=sha(candidate_path)),
        harness_command=['python3','-I','-B',str((OLD/'search_stress.py').relative_to(ROOT)),*inner],
        harness_exit_code=code,limits=LIMITS,pure_selftest=pure,
        candidate_source_snapshot=candidate['source_sha256'],
        candidate_sources_unchanged=candidate['sources_unchanged'],
        candidate_binary_unchanged=candidate['binary_unchanged'],legacy_main=candidate['legacy_main'],
        observed_source_snapshot_role=candidate['observed_source_snapshot_role'],
        measured_binary_association='Explicit root-supplied candidate hash; coordinator integration record owns its compiled source/build association.',
        qualifications=['Necessary guards are not sufficient acceptance tests; no runtime branch instrumentation is claimed.',
            'Source-review annotations in the frozen inventory remain unchanged and are not new kernel fixture theorems.',
            'Every timeout and skipped larger-series case remains inconclusive; expectations are never relaxed.',
            'Historical wave 9 totals and current totals cover different actually launched subsets after timeouts.',
            '512M is the RTS heap ceiling; whole process-group RSS uses a separate sampled 3 GiB ceiling.',
            'This is synthetic normalized replay, not log acquisition, capture completeness or deployed conformance.'])
    path=out/'comparison.json';path.write_text(json.dumps(result,indent=2)+'\n')
    integrity=all(result[key] for key in ('coordinator_unchanged','old_evidence_unchanged',
        'candidate_sources_unchanged','candidate_binary_unchanged','no_completed_verdict_disagreement'))
    print(json.dumps(dict(comparison=str(path),candidate=result['candidate'],integrity=integrity),indent=2))
    return code if integrity else 2


if __name__=='__main__':
    raise SystemExit(main())
