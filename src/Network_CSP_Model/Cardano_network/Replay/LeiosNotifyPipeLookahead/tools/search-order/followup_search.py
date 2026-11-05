#!/usr/bin/env python3
"""Repeat the original 21 schedule/payload follow-ups with exact fixture-byte checks."""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
import math
import os
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
TOOLS = HERE.parent
spec = importlib.util.spec_from_file_location('search_order_followup_cost', TOOLS / 'replay_cost.py')
COST = importlib.util.module_from_spec(spec)
spec.loader.exec_module(COST)
BASELINE = TOOLS / 'replay-cost/result-cost-20261105.json'


def cases():
    """Retain original closed distinct payloads and separately named ordinary prefix controls."""
    for family, payloads, ending in [('delayed-send', 'distinct', 'closed'),
                                      ('serial', 'repeated', 'reply-prefix'),
                                      ('pipeline', 'repeated', 'request-prefix')]:
        for count in [1, 2, 4, 8, 16, 32, 64]:
            data = COST.workload(family, count, payloads)
            if ending == 'reply-prefix':
                data['client'], data['server'] = data['client'][:-2], data['server'][:-2]
            if ending == 'request-prefix':
                data['client'], data['server'] = ['Send RequestNext']*count, ['Recv RequestNext']*count
            yield {'name': f'{family}_{payloads}_{ending}_{count:06d}',
                   'series': (family, payloads, ending), 'count': count, 'data': data}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--timeout', type=float, default=5)
    parser.add_argument('--total-timeout', type=float, default=120)
    parser.add_argument('--selftest', action='store_true')
    args = parser.parse_args()
    original = json.loads(BASELINE.read_text())
    baseline_cases = {case['name']: case for case in original['followup']['cases']}
    prepared = list(cases())
    if args.selftest:
        assert len(prepared) == len(baseline_cases) == 21
        import hashlib
        for case in prepared:
            assert hashlib.sha256(COST.case_text(case['data'], 'paired').encode()).hexdigest() == baseline_cases[case['name']]['fixture_sha256']
        print(json.dumps({'selftest': 'passed', 'original_fixture_hashes_matched': 21,
                          'checker_processes_launched': 0}, indent=2))
        return
    if not args.binary or not args.out:
        parser.error('--binary and --out are required')
    if not math.isfinite(args.timeout) or not 0 < args.timeout <= 30:
        parser.error('--timeout must be finite in (0,30]')
    if not math.isfinite(args.total_timeout) or not args.timeout <= args.total_timeout <= 120:
        parser.error('--total-timeout must be finite, at least --timeout and at most120')
    binary, out = args.binary.resolve(), args.out.resolve()
    if not binary.is_file() or not os.access(binary, os.X_OK):
        parser.error('--binary must be an existing caller-supplied executable')
    if out.exists() or out.is_relative_to(COST.ROOT):
        parser.error('--out must be a new directory outside the repository')
    out.mkdir(parents=True)
    report = {'schema': 'lookahead-search-order-followup-v1',
              'started_at_utc': datetime.now(timezone.utc).isoformat(),
              'binary': str(binary), 'binary_sha256': COST.sha256(binary),
              'script_sha256': COST.sha256(__file__), 'generator_sha256': COST.sha256(TOOLS / 'replay_cost.py'),
              'baseline_report': str(BASELINE), 'baseline_report_sha256': COST.sha256(BASELINE),
              'limits': {'seconds_per_case': args.timeout, 'total_seconds': args.total_timeout, 'heap': '512M',
                         'sampled_group_rss_kib': 3*1024*1024, 'output_bytes': 65536},
              'scope': 'Original 21 synthetic normalized follow-up fixtures; no real-log/conformance claim.',
              'cases': []}
    start, blocked = time.monotonic(), set()
    for case in prepared:
        original_case = baseline_cases[case['name']]
        path = out / (case['name'] + '.pair')
        path.write_text(COST.case_text(case['data'], 'paired'))
        digest = COST.sha256(path)
        assert digest == original_case['fixture_sha256'], 'original fixture bytes differ'
        row = {'name': case['name'], 'series': case['series'], 'count': case['count'],
               'fixture': str(path), 'fixture_sha256': digest, 'matches_original_fixture': True,
               'client_rows': len(case['data']['client']), 'server_rows': len(case['data']['server']),
               'expected': 'accepted-prefix', 'baseline_status': original_case['status'],
               'baseline_seconds': original_case['seconds']}
        if case['series'] in blocked:
            row.update(status='not-run', inconclusive_reason='earlier-series-inconclusive')
        elif args.total_timeout - (time.monotonic()-start) < args.timeout:
            row.update(status='not-run', inconclusive_reason='total-budget-before-full-case')
        else:
            row.update(COST.measure(COST.arguments(binary, 'paired', path, '512M'), out, case['name'], timeout=args.timeout))
            if row['status'] == 'inconclusive':
                blocked.add(case['series'])
        report['cases'].append(row)
        (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(case['name'], row['status'], row.get('seconds'), flush=True)
    report['seconds'] = round(time.monotonic()-start, 6)
    report['binary_unchanged'] = report['binary_sha256'] == COST.sha256(binary)
    report['generator_unchanged'] = report['generator_sha256'] == COST.sha256(TOOLS / 'replay_cost.py')
    report['all_expected'] = all(case['status'] == case['expected'] for case in report['cases'])
    report['completed_at_utc'] = datetime.now(timezone.utc).isoformat()
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'all_expected': report['all_expected'], 'report': str(out / 'report.json')}, indent=2))
    raise SystemExit(0 if report['all_expected'] and report['binary_unchanged'] and report['generator_unchanged'] else 1)


if __name__ == '__main__':
    main()
