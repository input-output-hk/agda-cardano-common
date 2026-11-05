#!/usr/bin/env python3
"""Compare fixed full closed-trace regressions and controls on two explicit binaries.

This reuses immutable wave-5 generation, resource guards and status classification.
A timeout remains inconclusive. The closed normal/cancellation cases retain both
Quit and Done; smaller EOF cases are separately named controls.
"""
import argparse
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
BASELINE_SHA256 = '59ad059459a312819372c826570aa1f3b3597f4309eaafc3adcc55d76d12f5d4'
SOURCES = (
    'src/Semantics/Replay/TwoListDecide.agda',
    'src/Semantics/Replay/Decide.agda',
    'src/Cardano_network/LeiosNotifyPipeLookahead/DriverBasisExecution.agda',
    'src/Cardano_network/LeiosNotifyPipeLookahead/ClientCallbackBasis.agda',
    'src/Cardano_network/LeiosNotifyPipeLookahead/DriverSearchOrder.agda',
    'src/Cardano_network/Replay/LeiosNotifyPipeLookahead/BasisAdequacy.agda',
    'src/Cardano_network/LeiosNotifyPipeLookahead/DriverModel.agda',
    'src/Cardano_network/LeiosNotifyPipeLookahead/Model.agda',
    'src/Cardano_network/LeiosNotifyPipeLookahead/ClientModel.agda',
    'src/Cardano_network/Replay/LeiosNotifyPipeLookahead/DriverDecide.agda',
    'src/Cardano_network/Replay/LeiosNotifyPipeLookahead/LookaheadReport.agda',
    'src/Cardano_network/Replay/LeiosNotifyPipeLookahead/LookaheadMain.agda',
)


def cost_module():
    """Load existing bounded measurement without changing its code or launching a checker."""
    path = TOOLS / 'replay_cost.py'
    spec = importlib.util.spec_from_file_location('search_order_cost', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


COST = cost_module()
ROOT = COST.ROOT


def cases():
    """Separate full closed positives from intentionally unfinished prefixes and negative controls."""
    def pair(name, data, expected='accepted-prefix', kind='closed-positive', aliases=()):
        return {'name': name, 'expected': expected, 'kind': kind,
                'client': data['client'], 'server': data['server'], 'aliases': list(aliases),
                'text': COST.case_text(data, 'paired')}

    normal = COST.workload('serial', 1)
    pipeline = COST.workload('pipeline', 1)
    assert COST.case_text(normal, 'paired') == COST.case_text(pipeline, 'paired')
    return [
        pair('normalclosed1_pipeline1', normal,
             aliases=('paired_serial_repeated_000001', 'paired_pipeline_repeated_000001')),
        pair('cancel4', COST.workload('cancel-drain', 4)),
        pair('delayedclosed1', COST.workload('delayed-send', 1)),
        pair('eof_client_request', {'client': ['Send RequestNext'], 'server': []}, kind='eof-positive'),
        pair('eof_server_receive', {'client': [], 'server': ['Recv RequestNext']}, kind='eof-positive'),
        pair('eof_both_receives_pending_sends',
             {'client': ['Recv BlockOffer 43 23 31'], 'server': ['Recv RequestNext']}, kind='eof-positive'),
        pair('reject_unmatched_reply', {'client': ['Recv Canceled'], 'server': []},
             expected='protocol-rejected', kind='negative-control'),
        pair('reject_done_without_quit', {'client': ['Recv Done'], 'server': ['Send Done']},
             expected='protocol-rejected', kind='negative-control'),
        pair('reject_exact_payload_mismatch',
             {'client': ['Recv BlockOffer 49 23 31'],
              'server': ['Recv RequestNext', 'Send BlockOffer 43 23 31']},
             expected='protocol-rejected', kind='negative-control'),
        pair('invalid_client_agency', {'client': ['Recv Quit'], 'server': []},
             expected='invalid-input', kind='invalid-control'),
    ]


def source_hashes():
    """Record observed checkout bytes without asserting that they attest either executable build."""
    selected = {name: COST.sha256(ROOT / name) for name in SOURCES}
    for path in [Path(__file__), TOOLS / 'replay_cost.py', TOOLS / 'test_lookahead_cli.py']:
        selected[str(path.relative_to(ROOT))] = COST.sha256(path)
    return selected


def generated_hashes(binary):
    """Retain relevant generated Haskell identities when present beside the supplied binary."""
    directory = binary.parent / 'MAlonzo/Code'
    selected = list((directory / 'Semantics/Replay').glob('*.hs'))
    selected += [directory / ('Cardano_network/LeiosNotifyPipeLookahead/' + name)
                 for name in ['DriverBasisExecution.hs', 'ClientCallbackBasis.hs', 'DriverSearchOrder.hs']]
    return {str(path): COST.sha256(path) for path in sorted(selected) if path.is_file()}


def selftest():
    """Check closure, exact aliasing and explicit expectations without launching any checker."""
    prepared = cases()
    assert len({case['name'] for case in prepared}) == len(prepared)
    for case in prepared:
        if case['kind'] == 'closed-positive':
            assert case['client'].count('Send Quit') == case['server'].count('Recv Quit') == 1
            assert case['client'][-1] == 'Recv Done' and case['server'][-1] == 'Send Done'
            assert [row[5:] for row in case['client'] if row.startswith('Recv ')] == [
                row[5:] for row in case['server'] if row.startswith('Send ')]
    assert prepared[1]['client'].count('Recv Canceled') == 4
    assert prepared[1]['server'].count('Send Canceled') == 4
    assert sum(case['expected'] == 'protocol-rejected' for case in prepared) == 3
    return {'selftest': 'passed', 'fixtures': len(prepared), 'checker_processes_launched': 0,
            'normal_pipeline_one_byte_identical': True, 'primary_closed_traces_keep_quit_done': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path)
    parser.add_argument('--candidate', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--timeout', type=float, default=5.0)
    parser.add_argument('--total-timeout', type=float, default=90.0)
    parser.add_argument('--selftest', action='store_true')
    args = parser.parse_args()
    if args.selftest:
        if args.baseline or args.candidate or args.out:
            parser.error('--selftest cannot launch or name binary runs')
        print(json.dumps(selftest(), indent=2))
        return
    if not args.baseline or not args.candidate or not args.out:
        parser.error('--baseline, --candidate and --out are required')
    if not math.isfinite(args.timeout) or not 0 < args.timeout <= 30:
        parser.error('--timeout must be finite in (0,30] seconds')
    if not math.isfinite(args.total_timeout) or not args.timeout <= args.total_timeout <= 300:
        parser.error('--total-timeout must be finite, at least --timeout and at most300 seconds')
    baseline, candidate, out = args.baseline.resolve(), args.candidate.resolve(), args.out.resolve()
    for binary in [baseline, candidate]:
        if not binary.is_file() or not os.access(binary, os.X_OK):
            parser.error('both binaries must be existing caller-supplied executables')
    if COST.sha256(baseline) != BASELINE_SHA256:
        parser.error('baseline must be the recorded wave-4 binary SHA256 ' + BASELINE_SHA256)
    if baseline == candidate or COST.sha256(baseline) == COST.sha256(candidate):
        parser.error('candidate must differ from the baseline; use the separate initial-probe evidence for reproduction')
    if out.exists() or out.is_relative_to(ROOT):
        parser.error('--out must be a new directory outside the repository')
    out.mkdir(parents=True)
    report = {'schema': 'lookahead-search-order-comparison-v1',
              'started_at_utc': datetime.now(timezone.utc).isoformat(),
              'repository_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'observed_checkout_sha256': source_hashes(),
              'limits': {'case_seconds': args.timeout, 'total_seconds': args.total_timeout,
                         'heap': '512M', 'sampled_group_rss_kib': 3*1024*1024, 'output_bytes': 65536},
              'profile': {'serverContract': 'node-next', 'clientCallbacks': 'generic-successful',
                          'return': 'unit', 'observation': 'driver-log', 'eof': 'prefix'},
              'binaries': {}, 'cases': [],
              'scope': 'Synthetic normalized paired-prefix regression/cost evidence; no raw node capture',
              'limitations': ['Timeout/resource failure is inconclusive, never exhaustive rejection.',
                              'Small completed measurements are not a universal complexity or conformance claim.',
                              'Observed checkout/generated hashes alone do not attest which sources built an executable.',
                              'Synthetic fresh/endpoint assertions do not establish real capture completeness.']}
    for label, binary in [('baseline', baseline), ('candidate', candidate)]:
        report['binaries'][label] = {'path': str(binary), 'sha256': COST.sha256(binary),
                                    'generated_haskell_sha256': generated_hashes(binary)}
    start = time.monotonic()
    for case in cases():
        fixture = out / (case['name'] + '.pair')
        fixture.write_text(case['text'])
        row = {key: value for key, value in case.items() if key != 'text'}
        row.update(fixture=str(fixture), fixture_sha256=COST.sha256(fixture), fixture_bytes=fixture.stat().st_size)
        for label, binary in [('baseline', baseline), ('candidate', candidate)]:
            remaining = args.total_timeout - (time.monotonic() - start)
            if remaining < args.timeout:
                row[label] = {'status': 'not-run', 'inconclusive_reason': 'total-budget-before-full-case'}
                continue
            result = COST.measure(COST.arguments(binary, 'paired', fixture, '512M'), out,
                                  label + '_' + case['name'], timeout=args.timeout)
            result['matches_expected'] = result['status'] == case['expected']
            row[label] = result
            print(label, case['name'], result['status'], result['seconds'], flush=True)
        row['fixture_unchanged'] = COST.sha256(fixture) == row['fixture_sha256']
        report['cases'].append(row)
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    report['seconds'] = round(time.monotonic() - start, 6)
    report['completed_at_utc'] = datetime.now(timezone.utc).isoformat()
    for label, binary in [('baseline', baseline), ('candidate', candidate)]:
        report['binaries'][label]['unchanged'] = COST.sha256(binary) == report['binaries'][label]['sha256']
    report['checkout_unchanged'] = source_hashes() == report['observed_checkout_sha256']
    report['candidate_completed_all_expected'] = all(row['candidate'].get('matches_expected', False) for row in report['cases'])
    report['baseline_unexpected_completed_statuses'] = [
        row['name'] for row in report['cases']
        if row['baseline']['status'] not in ('inconclusive', 'not-run', row['expected'])]
    report['comparison_passed'] = (report['candidate_completed_all_expected'] and
                                   not report['baseline_unexpected_completed_statuses'] and
                                   all(info['unchanged'] for info in report['binaries'].values()) and
                                   all(row['fixture_unchanged'] for row in report['cases']))
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'comparison_passed': report['comparison_passed'], 'report': str(out / 'report.json')}, indent=2))
    raise SystemExit(0 if report['comparison_passed'] else 1)


if __name__ == '__main__':
    main()
