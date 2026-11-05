#!/usr/bin/env python3
"""Bounded rejection-heavy paired replay measurements with independent fixture rationales.

Only generated normalized fixtures are used. Timeouts remain inconclusive and
stop that series; no raw-log acquisition or protocol/model modification occurs.
"""
import argparse
from collections import Counter
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
spec = importlib.util.spec_from_file_location('rejection_measure', TOOLS / 'replay_cost.py')
COST = importlib.util.module_from_spec(spec)
spec.loader.exec_module(COST)
BASELINE_SHA256 = '609d2a99ab0f918f3f485b12dd0682e78f701adba9e585372b8fd3b0b6b3e7c6'
RATIONALES = {
    'payload': 'Exact DriverConservation.to-client FIFO lists disagree at the first changed reply. Pending sender/receiver records are suffix corrections and cannot repair an earlier unequal packet.',
    'extra-server': 'The server records n Request receives but n+1 reply Sends. ServerConservation requires requests = replies + owed for every initial source prefix, so no callback schedule can supply the extra reply.',
    'extra-client': 'After n matching replies, recorded server Done disagrees with the extra client Reply at the same FIFO position. Both recorded histories include Done, so a merely delayed Send hook cannot repair that earlier mismatch.',
    'server-done': 'Server Done is moved before its last owed reply: n requests and only n-1 reply Sends precede Done. The actual doneReady/finish guard and closed-balance theorem require zero owed replies; later reply Send is also impossible after closed.',
    'client-done': 'Client Done Receive is moved before its Quit Send record. Physical Quit commit may precede its Send hook, but the client enters awaitDone only after recording that hook. Lead/pending-send behavior therefore does not admit this order.',
    'duplicate-done': 'After the first server Done Send record the server is closed; it cannot commit/send a second Done. This uses actual closed control and the one pending sender slot, not a claim that every duplicated prefix row is invalid.',
}


def make_case(name, client, server, expected, series=None, count=None, payloads=None, rationale=''):
    """Retain both independent endpoint orders and the precise expectation justification."""
    notifications = [row[5:] for row in client if row.startswith('Recv Block')]
    notifications += [row[5:] for row in server if row.startswith('Send Block')]
    return {'name': name, 'client': client, 'server': server, 'expected': expected,
            'series': series, 'count': count, 'payloads': payloads, 'rationale': rationale,
            'normal_payload_occurrences': len(notifications),
            'distinct_observed_normal_payloads': len(set(notifications))}


def controls():
    """A missing Send record alone stays a valid EOF race; malformed rows stay a separate class."""
    closed = COST.workload('serial', 1)
    return [
        make_case('control_closed_normal', closed['client'], closed['server'], 'accepted-prefix', rationale='Complete unchanged documented normal source schedule.'),
        make_case('control_eof_client_request', ['Send RequestNext'], [], 'accepted-prefix', rationale='Client Request Send may precede every server record.'),
        make_case('control_eof_server_receive', [], ['Recv RequestNext'], 'accepted-prefix', rationale='Physical Request commit can precede the delayed client Send record.'),
        make_case('control_eof_both_receive_before_sends', ['Recv BlockOffer 43 23 31'], ['Recv RequestNext'], 'accepted-prefix', rationale='Actual fresh driver schedule can record both Receives while both Send hooks remain pending.'),
        make_case('control_reject_short_payload', ['Recv BlockOffer 49 23 31'], ['Recv RequestNext', 'Send BlockOffer 43 23 31'], 'protocol-rejected', rationale=RATIONALES['payload']),
        make_case('control_reject_done_no_quit', ['Recv Done'], ['Send Done'], 'protocol-rejected', rationale='Both source Done records require prior recorded Quit in their respective control paths.'),
        make_case('control_reject_unsolicited_reply', [], ['Send Canceled'], 'protocol-rejected', rationale=RATIONALES['extra-server']),
        make_case('control_invalid_agency', ['Recv RequestNext'], [], 'invalid-input', rationale='Client Request must be Send; this is schema agency failure, not protocol rejection.'),
        make_case('control_invalid_vote_grammar', ['Recv Votes 43::71'], [], 'invalid-input', rationale='Malformed vote pair is rejected by normalized parsing before any typed protocol decision.'),
    ]


def series_cases(sizes):
    """Keep all original Quit/Done rows; mutations have explicit conservation/control contradictions."""
    definitions = [
        ('payload-early-repeated', 'payload', 'repeated', 'early'),
        ('payload-late-repeated', 'payload', 'repeated', 'late'),
        ('payload-late-distinct', 'payload', 'distinct', 'late'),
        ('extra-server-repeated', 'extra-server', 'repeated', None),
        ('extra-server-distinct', 'extra-server', 'distinct', None),
        ('extra-client-repeated', 'extra-client', 'repeated', None),
        ('premature-server-done', 'server-done', 'repeated', None),
        ('client-done-before-quit', 'client-done', 'repeated', None),
        ('duplicate-server-done', 'duplicate-done', 'repeated', None),
    ]
    for series, kind, payloads, position in definitions:
        for n in sizes:
            base = COST.workload('serial', n, payloads)
            client, server = list(base['client']), list(base['server'])
            wrong = 'BlockOffer %x 23 31' % (0xf0000000 + n)
            if kind == 'payload':
                indices = [i for i, row in enumerate(client) if row.startswith('Recv BlockOffer ')]
                client[indices[0] if position == 'early' else indices[-1]] = 'Recv ' + wrong
            elif kind == 'extra-server':
                server.insert(len(server)-1, 'Send ' + wrong)
            elif kind == 'extra-client':
                client.insert(len(client)-1, 'Recv ' + wrong)
            elif kind == 'server-done':
                # Retain every row: the final reply moves after recorded Quit/Done.
                last_reply = server.pop(-3)
                assert last_reply.startswith('Send BlockOffer ')
                server.append(last_reply)
            elif kind == 'client-done':
                client[-2:] = ['Recv Done', 'Send Quit']
            elif kind == 'duplicate-done':
                server.append('Send Done')
            yield make_case(f'{series}_{n:06d}', client, server, 'protocol-rejected',
                            series, n, payloads, RATIONALES[kind])


def fixture_text(case):
    """Reuse the exact paired grammar while asserting only synthetic source coordinates."""
    return COST.CLI.pair_text(list(enumerate(case['client'], 11)), list(enumerate(case['server'], 17)))


def selftest():
    """Check closed-trace retention and fixture mutations without invoking a checker."""
    prepared = controls() + list(series_cases([1, 2, 4]))
    assert len({case['name'] for case in prepared}) == len(prepared)
    for case in prepared:
        if case['series']:
            assert case['client'].count('Send Quit') == case['server'].count('Recv Quit') == 1
            assert case['client'].count('Recv Done') >= 1 and case['server'].count('Send Done') >= 1
            n = case['count']
            assert case['client'].count('Send RequestNext') == case['server'].count('Recv RequestNext') == n
            if case['series'].startswith('extra-server'):
                assert sum(row.startswith('Send BlockOffer ') for row in case['server']) == n+1
            if case['series'].startswith('extra-client'):
                assert case['client'].index('Send Quit') < next(i for i, row in enumerate(case['client']) if 'f00000' in row)
            if case['series'] == 'premature-server-done':
                assert case['server'][-2] == 'Send Done' and case['server'][-1].startswith('Send BlockOffer ')
            assert case['rationale']
    return {'selftest': 'passed', 'fixtures_checked': len(prepared), 'series': 9,
            'checker_processes_launched': 0, 'closed_negative_series_keep_quit_done': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--reference', type=Path, help='prior report whose exact generated fixture hashes must match')
    parser.add_argument('--expected-binary-sha256')
    parser.add_argument('--sizes', default='1,2,4,8,16,32,64')
    parser.add_argument('--timeout', type=float, default=2)
    parser.add_argument('--total-timeout', type=float, default=60)
    parser.add_argument('--selftest', action='store_true')
    args = parser.parse_args()
    if args.selftest:
        print(json.dumps(selftest(), indent=2)); return
    if not args.binary or not args.out:
        parser.error('--binary and --out are required')
    try:
        sizes = [int(value) for value in args.sizes.split(',')]
    except ValueError:
        parser.error('--sizes must be positive comma-separated integers')
    if not sizes or sizes != sorted(set(sizes)) or not all(1 <= n <= 256 for n in sizes):
        parser.error('--sizes must be strictly increasing integers in [1,256]')
    if not math.isfinite(args.timeout) or not 0 < args.timeout <= 5:
        parser.error('--timeout must be finite in (0,5]')
    if not math.isfinite(args.total_timeout) or not args.timeout <= args.total_timeout <= 120:
        parser.error('--total-timeout must be finite, at least --timeout and at most120')
    binary, out = args.binary.resolve(), args.out.resolve()
    if not binary.is_file() or not os.access(binary, os.X_OK):
        parser.error('--binary must be an existing executable')
    binary_digest = COST.sha256(binary)
    if args.expected_binary_sha256 and binary_digest != args.expected_binary_sha256:
        parser.error('supplied binary hash does not match --expected-binary-sha256')
    if out.exists() or out.is_relative_to(COST.ROOT):
        parser.error('--out must be a new directory outside the repository')
    reference = json.loads(args.reference.read_text()) if args.reference else None
    reference_cases = {case['name']: case for case in reference['cases']} if reference else None
    prepared = controls() + list(series_cases(sizes))
    if reference_cases is not None and set(reference_cases) != {case['name'] for case in prepared}:
        parser.error('reference fixture names differ; use the exact same --sizes')
    out.mkdir(parents=True)
    prior = TOOLS / 'search-order/result-search-order-20261105.json'
    report = {'schema': 'lookahead-rejection-cost-v1', 'started_at_utc': datetime.now(timezone.utc).isoformat(),
              'repository_head_observed': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=COST.ROOT, text=True).strip(),
              'binary': str(binary), 'binary_sha256': binary_digest,
              'known_ordered_baseline_sha256': BASELINE_SHA256,
              'binary_is_known_ordered_baseline': binary_digest == BASELINE_SHA256,
              'prior_ordered_baseline_record': str(prior), 'prior_ordered_baseline_record_sha256': COST.sha256(prior),
              'source_sha256': {str(path): COST.sha256(path) for path in [Path(__file__), TOOLS/'replay_cost.py', TOOLS/'test_lookahead_cli.py']},
              'reference_report': str(args.reference.resolve()) if args.reference else None,
              'reference_report_sha256': COST.sha256(args.reference) if args.reference else None,
              'profile': {'serverContract': 'node-next', 'clientCallbacks': 'generic-successful', 'return': 'unit', 'observation': 'driver-log', 'eof': 'prefix'},
              'limits': {'seconds_per_case': args.timeout, 'total_seconds': args.total_timeout, 'heap': '512M', 'sampled_group_rss_kib': 3*1024*1024, 'output_bytes': 65536},
              'cases': [], 'limitations': ['Expected negatives have explicit conservation/control rationales; no new kernel proofs are introduced by this Python harness.',
                  'Current checkout can differ from the baseline build; immutable binary hashes and its prior build record identify the measured checker.',
                  'Timeout/resource failure is inconclusive and stops that series, not a model rejection.',
                  'Fixture fresh/endpoint/source-line assertions are synthetic; no capture completeness or deployed conformance is inferred.']}
    started, blocked = time.monotonic(), set()
    for case in prepared:
        fixture = out / (case['name'] + '.pair')
        fixture.write_text(fixture_text(case))
        digest = COST.sha256(fixture)
        row = {**case, 'fixture': str(fixture), 'fixture_sha256': digest, 'fixture_bytes': fixture.stat().st_size}
        if reference_cases is not None:
            assert digest == reference_cases[case['name']]['fixture_sha256'], 'fixture bytes changed'
            row['matches_reference_fixture'] = True
            row['reference_status'] = reference_cases[case['name']]['status']
        if case['series'] in blocked:
            row.update(status='not-run', inconclusive_reason='earlier-series-inconclusive')
        elif args.total_timeout - (time.monotonic()-started) < args.timeout:
            row.update(status='not-run', inconclusive_reason='total-budget-before-full-case')
        else:
            row.update(COST.measure(COST.arguments(binary, 'paired', fixture, '512M'), out, case['name'], timeout=args.timeout))
            if row['status'] == 'inconclusive' and case['series']:
                blocked.add(case['series'])
        row['expectation_met'] = row['status'] == row['expected']
        report['cases'].append(row)
        (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
        print(case['name'], row['status'], row.get('seconds'), flush=True)
    report['seconds'] = round(time.monotonic()-started, 6)
    report['counts'] = dict(Counter(case['status'] for case in report['cases']))
    report['unexpected_completed_results'] = [case['name'] for case in report['cases'] if case['status'] not in ('inconclusive','not-run') and not case['expectation_met']]
    report['binary_unchanged'] = COST.sha256(binary) == binary_digest
    report['sources_unchanged'] = all(COST.sha256(path) == digest for path,digest in report['source_sha256'].items())
    report['completed_at_utc'] = datetime.now(timezone.utc).isoformat()
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'counts': report['counts'], 'unexpected_completed_results': report['unexpected_completed_results'], 'report': str(out/'report.json')},indent=2))
    raise SystemExit(1 if report['unexpected_completed_results'] or not report['binary_unchanged'] or not report['sources_unchanged'] else 0)


if __name__ == '__main__':
    main()
