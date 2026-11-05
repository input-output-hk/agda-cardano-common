#!/usr/bin/env python3
"""Recover the completed first comparison from its original artifacts; launch no models.

This one-run recovery explicitly preserves missing in-memory monitor fields as
null. The original captured host console supplies positive statuses and elapsed
times; original stdout/stderr and GNU time files supply independent artifacts.
"""
import hashlib
import importlib.util
import json
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('menu_recover_full',HERE/'full_replay.py')
FULL=importlib.util.module_from_spec(spec);spec.loader.exec_module(FULL)
COST=FULL.COST
OUT=Path('/tmp/leiosnotify-menu-full-replay-20261105')
BINARY=Path('/var/tmp/leiosnotify-wave12-cli-20261105/generated/LookaheadMain')
BINARY_SHA='867e1ab15b0d61d8ec1fe33dec3b645f3bf38d6216c30204e1bfcabc8d6f78d0'


def main():
    """Validate existing bytes, classify retained outputs and write an honest recovery record."""
    failure=json.loads((HERE/'full-coordination-failure-20261105.json').read_text())
    console={row['name']:row for row in failure['retained_host_console_positive20']}
    before=json.loads((OUT/'production-before.json').read_text())
    assert FULL.protect_production(True)==before
    assert COST.sha256(BINARY)==BINARY_SHA
    stress=json.loads((OUT/'stress83/report.json').read_text())
    cycle=json.loads((OUT/'cycle3/report.json').read_text())
    baseline83=json.loads((FULL.TOOLS/'shutdown-stress/result-shutdown-stress-20261105.json').read_text())
    baseline3=json.loads((FULL.TOOLS/'shutdown-stress/result-ordering-cycle-20261105.json').read_text())
    positives=[]
    for case in FULL.positives():
        name=case['name'];fixture=OUT/'positive20'/(name+'.txt')
        assert fixture.read_text()==case['input']
        artifacts={}
        for suffix in ('stdout','stderr','time'):
            path=OUT/'positive20'/(name+'.'+suffix)
            artifacts[suffix]=dict(path=str(path),sha256=COST.sha256(path),bytes=path.stat().st_size)
        stdout=(OUT/'positive20'/(name+'.stdout')).read_text()
        stderr=(OUT/'positive20'/(name+'.stderr')).read_text()
        assert console[name]['status']=='accepted-prefix'
        # Original accepted classification entails exit zero; this is recovered
        # from the captured monitor console, not an independently saved waitpid.
        status,reason=FULL.COST.CLI.classify(0,stdout,stderr)
        assert status=='accepted-prefix' and reason is None
        lines=(OUT/'positive20'/(name+'.time')).read_text().splitlines()
        assert len(lines)==4
        metrics=dict(child_peak_rss_kib=int(lines[-4]),gnu_elapsed_seconds=float(lines[-3]),
            user_seconds=float(lines[-2]),system_seconds=float(lines[-1]))
        argv=COST.arguments(BINARY,'paired',fixture,'512M')
        old=case['baseline'];assert argv[1]==old['argv'][1] and argv[2:]==[str(fixture),*old['argv'][3:]]
        positives.append(dict(name=name,fixture_sha256=COST.sha256(fixture),expected='accepted-prefix',
            baseline_status=old['status'],status=status,expectation_met=True,inconclusive_reason=None,
            seconds=console[name]['seconds'],exit_code=0,exit_code_basis='Original captured monitor accepted-prefix classification entails exit zero; original waitpid field was not checkpointed.',
            peak_sampled_group_rss_kib=None,gnu_time=metrics,logs=artifacts,
            argv=argv,rts=FULL.MICRO.PROFILE.rts_allocations(stderr),
            recovery=True,status_and_seconds_basis='Captured original host console retained in full-coordination-failure-20261105.json'))
    comparisons=dict(stress83=FULL.compare_rows(stress['cases'],baseline83['cases']),
        cycle3=FULL.compare_rows(cycle['cases'],baseline3['cases']),
        positive20=FULL.compare_rows(positives,[case['baseline'] for case in FULL.positives()]))
    for summary in comparisons.values():assert summary['no_completed_verdict_disagreement']
    old=FULL.MICRO.protect_old()
    result=dict(schema='lookahead-gated-full-replay-recovered-comparison-v1',
        original_coordinator_sha256=failure['original_source_sha256'],
        corrected_coordinator_sha256=COST.sha256(HERE/'full_replay.py'),
        recovery_script_sha256=COST.sha256(Path(__file__)),
        original_host_aggregation_failure=dict(record='full-coordination-failure-20261105.json',sha256=COST.sha256(HERE/'full-coordination-failure-20261105.json')),
        binary=str(BINARY),binary_sha256=BINARY_SHA,
        baseline_binary_sha256='c8f9ce34ca59b4e150570cedb55e068601f736d3eb192934d492dda711d0af82',baseline_not_rerun=True,
        measured_binary_association='Root owns the candidate compiled-source/build association; live source hashes alone do not establish that association.',
        pure_selftest=FULL.selftest(),
        stress83=dict(full_report=str(OUT/'stress83/report.json'),full_report_sha256=COST.sha256(OUT/'stress83/report.json'),
            seconds=stress['seconds'],counts=stress['counts'],all_expected=stress['all_expected'],cases=stress['cases']),
        cycle3=dict(full_report=str(OUT/'cycle3/report.json'),full_report_sha256=COST.sha256(OUT/'cycle3/report.json'),
            seconds=cycle['seconds'],all_expected=cycle['all_expected'],cases=cycle['cases']),
        positive20=dict(counts=dict(Counter(row['status'] for row in positives)),all_expected=True,cases=positives,
            limits=dict(seconds_per_case=2,total_seconds=45,heap='512M',sampled_group_rss_kib=3*1024*1024,output_bytes=65536)),
        comparisons=comparisons,
        baseline_records={str(path.relative_to(FULL.ROOT)):COST.sha256(path) for path in [FULL.TOOLS/'shutdown-stress/result-shutdown-stress-20261105.json',FULL.TOOLS/'shutdown-stress/result-ordering-cycle-20261105.json',FULL.TOOLS/'cost-profile/result-cost-profile-20261105.json']},
        production_before=before,production_preserved_to_recovery=True,old_selected_tools_sha256=old,
        exact_input_flags_expectations_verified=True,binary_unchanged=True,
        overall_seconds=None,recovered_without_model_reruns=True,model_processes_launched_by_recovery=0,
        all_expected=stress['all_expected'] and cycle['all_expected'],
        qualifications=[*failure['recovery_limits'],
            'All 95 launched model invocations (106 planned slots, 11 skipped) completed before host aggregation failed. The fixed coordinator was not rerun.',
            'Stress 83 and cycle 3 retain their original complete monitor reports; only positive 20 monitor rows required recovery.',
            'Historical and current observations include deadline variation; no universal speedup follows.',
            'Cumulative RTS allocation, GNU time child peak RSS and sampled group RSS are different metrics.',
            'Only the explicit one-import change is permitted among 1,031 baseline Agda files; 29 selected historical tool/evidence files are protected.'])
    target=HERE/'result-full-replay-20261105.json';target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(path=str(target),sha256=COST.sha256(target),comparisons=comparisons,
        stress_seconds=stress['seconds'],cycle_seconds=cycle['seconds']),indent=2))


if __name__=='__main__':main()
