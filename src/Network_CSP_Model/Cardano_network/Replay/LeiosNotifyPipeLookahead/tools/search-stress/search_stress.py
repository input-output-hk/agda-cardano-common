#!/usr/bin/env python3
"""Stress the complete paired fallback with source-reviewed synthetic fixtures.

All fixtures are expected to pass the three committed necessary prechecks.
Review annotations are not kernel witnesses or runtime branch instrumentation.
No capture acquisition, model mutation or prior fixture modification occurs.
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
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
TOOLS = HERE.parent
EXPECTED_BINARY_SHA256 = 'd7bf4b88247a87a535d3e1639603c90c69b09a0a138a808c4fb8932de4726938'
BASELINE_COMMIT = '05eace4e'
POSITIVE_SIZES = (128, 256, 512, 1024, 2048, 4096)
NEGATIVE_SIZES = (0, 1, 2, 4, 8, 16, 32, 64, 128)
POSITIVE_VARIANTS = tuple((family, payloads)
    for family in ('serial', 'pipeline', 'delayed-send', 'cancel-drain')
    for payloads in ('repeated', 'distinct'))
NEGATIVE_VARIANTS = (('early-orphan-reply', 'repeated'),
                     ('early-orphan-reply', 'distinct'),
                     ('requested-orphan-reply', 'repeated'),
                     ('orphan-done', 'repeated'))
MAX_FIXTURE_BYTES = 8*1024*1024


def load(name, path):
    """Reuse immutable fixture and bounded measurement producers without entrypoints."""
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PRECHECK = load('stress_precheck', TOOLS/'precheck/precheck_regressions.py')
COST, CLI, ROOT = PRECHECK.COST, PRECHECK.CLI, PRECHECK.ROOT


def packet_inventory(client, server):
    """Check literal packet-prefix/count arithmetic; do not reimplement local decisions."""
    client_send = [row[5:] for row in client if row.startswith('Send ')]
    client_recv = [row[5:] for row in client if row.startswith('Recv ')]
    server_send = [row[5:] for row in server if row.startswith('Send ')]
    server_recv = [row[5:] for row in server if row.startswith('Recv ')]
    def compatible(first, second):
        return all(a == b for a, b in zip(first, second))
    return dict(client_sends=len(client_send), client_receives=len(client_recv),
        server_sends=len(server_send), server_receives=len(server_recv),
        common_packet_prefixes_equal=compatible(client_send, server_recv) and
                                     compatible(server_send, client_recv),
        pending_send_count_bounds=(len(server_recv) <= len(client_send)+1 and
                                   len(client_recv) <= len(server_send)+1),
        client_reply_receives=sum(value != 'Done' for value in client_recv),
        server_request_receives=server_recv.count('RequestNext'))


def orphan(family, count, payloads='repeated'):
    """Pad an impossible response with fully discharged serial exchanges, without Quit/Done."""
    if family not in ('early-orphan-reply', 'requested-orphan-reply', 'orphan-done'):
        raise ValueError('unknown orphan family')
    if type(count) is not int or not 0 <= count <= 16384:
        raise ValueError('prefix size must be an integer in [0,16384]')
    if payloads not in ('repeated', 'distinct'):
        raise ValueError('unsupported payload mode')
    if count:
        data = COST.workload('serial', count, payloads)
        client, server = data['client'][:-2], data['server'][:-2]
    else:
        client, server = [], []
    value = 'BlockOffer %s 23 31' % format(0x43+(count if payloads == 'distinct' else 0), 'x')
    if family == 'early-orphan-reply':
        client += ['Recv '+value]
        rationale = ('After the discharged serial prefix, client Open 0 permits one early reply '
            'and enters Lead. The server has no recorded additional Request Receive to enable '
            'another owed reply. An unrecorded decode does not advance its continuation.')
    elif family == 'requested-orphan-reply':
        client += ['Send RequestNext', 'Recv '+value]
        rationale = ('The client records a fresh Request and accepts its reply locally. The server '
            'records no additional Request Receive, so it cannot create that extra reply. '
            'An unmatched client command suffix and one pending server Send correction pass '
            'the packet/count guards but do not supply server request credit.')
    else:
        client += ['Send Quit', 'Recv Done']
        rationale = ('The client completes its local Quit/Done phase, but the server records no '
            'Quit Receive and therefore cannot enable Done. Earlier reply credit is fully '
            'discharged. The proposed separate ReplyCredit guard excludes Done and Quit and '
            'would not refute this control; complete fallback is still required.')
    return dict(family=family, count=count, payloads=payloads, client=client, server=server,
                rationale=rationale)


def cases(positive_sizes=POSITIVE_SIZES, negative_sizes=NEGATIVE_SIZES):
    """Keep each series increasing and its expected verdict fixed before running a binary."""
    result = []
    for family, payloads in NEGATIVE_VARIANTS:
        for count in negative_sizes:
            # Empty-prefix distinct/repeated inputs are identical; keep that control once.
            if count == 0 and payloads == 'distinct':
                continue
            data = orphan(family, count, payloads)
            series = 'negative_'+family+'_'+payloads
            case = PRECHECK.paired(series+'_'+format(count, '06d'), data['client'], data['server'],
                'protocol-rejected', data['rationale'], local_pass=True, packet_pass=True)
            case.update(series=series, category='negative', family=family, payloads=payloads,
                        size=count, review_basis='Source review; not a new kernel family theorem.',
                        kernel_reference=('Existing unmatched-client zero-prefix normal-reply control '
                            'in DriverPrecheckTests; it does not certify every generated padded fixture.'
                            if family == 'early-orphan-reply' else
                            'No new kernel fixture theorem is asserted here.'))
            case['packet_inventory'] = packet_inventory(data['client'], data['server'])
            result.append(case)
    for family, payloads in POSITIVE_VARIANTS:
        for count in positive_sizes:
            data = COST.workload(family, count, payloads)
            series = 'positive_'+family+'_'+payloads
            case = PRECHECK.paired(series+'_'+format(count, '06d'), data['client'], data['server'],
                'accepted-prefix', data['expectation_basis'], local_pass=True, packet_pass=True)
            case.update(series=series, category='positive', family=family, payloads=payloads,
                        size=count, review_basis='Existing workload source-schedule construction; not a new kernel witness.',
                        kernel_reference='Existing small source witnesses do not certify each larger generated fixture.')
            case['packet_inventory'] = packet_inventory(data['client'], data['server'])
            result.append(case)
    for case in result:
        if len(case['input'].encode()) > MAX_FIXTURE_BYTES:
            raise ValueError('fixture byte budget exceeded: '+case['name'])
        assert case['packet_inventory']['common_packet_prefixes_equal']
        assert case['packet_inventory']['pending_send_count_bounds']
    assert len({case['name'] for case in result}) == len(result)
    return result


def selftest():
    """Validate construction and immutable old inventories without launching any process."""
    old = PRECHECK.selftest()
    generated = cases()
    assert len(generated) == 83
    assert Counter(case['category'] for case in generated) == {'positive':48, 'negative':35}
    # Canceled carries no payload; repeated/distinct policy names share six inputs.
    unique = len({hashlib.sha256(c['input'].encode()).hexdigest() for c in generated})
    assert unique == 77
    for case in generated:
        assert case['reviewed_local_guard_pass'] and case['reviewed_packet_guard_pass']
        assert case['reviewed_count_guard_pass']
        inventory = case['packet_inventory']
        if case['category'] == 'negative':
            if case['family'] == 'orphan-done':
                assert inventory['client_reply_receives'] == inventory['server_request_receives'] == case['size']
                assert case['input'].endswith('Send Done\n') is False
            else:
                assert inventory['client_reply_receives'] == inventory['server_request_receives']+1
        else:
            data = COST.workload(case['family'], case['size'], case['payloads'])
            assert case['input'] == COST.case_text(data, 'paired')
    # The zero-prefix fixture spells the existing normal-reply kernel control.
    zero = next(case for case in generated if case['family']=='early-orphan-reply' and case['size']==0)
    assert 'client 11 Recv BlockOffer 43 23 31\n' in zero['input']
    return dict(selftest='passed', generated_cases=len(generated),
        categories=dict(Counter(case['category'] for case in generated)),
        unique_fixture_hashes=unique, prior_controls=old,
        packet_prefix_count_arithmetic_checked=True, local_guard_pass_is_review_annotation=True,
        checker_processes_launched=0)


def parse_sizes(text, *, allow_zero):
    """Bound fixture inventories and reject repeated/decreasing size requests."""
    try:
        values = tuple(int(value) for value in text.split(','))
    except ValueError as error:
        raise ValueError('sizes must be comma-separated integers') from error
    if not values or len(values)>12 or tuple(sorted(set(values))) != values:
        raise ValueError('sizes must be a strictly increasing list of at most twelve values')
    if any(value < (0 if allow_zero else 1) or value > 16384 for value in values):
        raise ValueError('size outside supported [0 or 1,16384] range')
    return values


def source_paths():
    """Bind every imported producer and the source-reviewed baseline premises."""
    paths = [Path(__file__).resolve(), TOOLS/'precheck/precheck_regressions.py',
        TOOLS/'replay_cost.py', TOOLS/'test_lookahead_cli.py',
        TOOLS/'rejection-cost/rejection_cost.py', TOOLS/'basis-regressions/regressions.py',
        TOOLS/'search-order/followup_search.py', PRECHECK.REJECTION_RECORD, PRECHECK.POSITIVE_RECORD]
    for name in ('DriverDecide.agda','DriverPrecheckTests.agda','LocalPrecheck.agda',
                 'PacketPrecheck.agda','PacketCountPrecheck.agda'):
        paths.append(TOOLS.parent/name)
    for name in ('DriverModel.agda','Wire/Client.agda','Wire/Server.agda'):
        paths.append(ROOT/'src/Cardano_network/LeiosNotifyPipeLookahead'/name)
    return paths


def main(argv=None):
    """Run serial bounded cases; stop a series after its first inconclusive result."""
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary',type=Path)
    parser.add_argument('--expected-sha256',default=EXPECTED_BINARY_SHA256)
    parser.add_argument('--out',type=Path)
    parser.add_argument('--positive-sizes',default=','.join(map(str,POSITIVE_SIZES)))
    parser.add_argument('--negative-sizes',default=','.join(map(str,NEGATIVE_SIZES)))
    parser.add_argument('--timeout',type=float,default=2)
    parser.add_argument('--total-timeout',type=float,default=180)
    parser.add_argument('--selftest',action='store_true')
    args=parser.parse_args(argv)
    if args.selftest:
        if args.binary or args.out:
            parser.error('--selftest does not launch a binary')
        print(json.dumps(selftest(),indent=2)); return 0
    if not args.binary or not args.out:
        parser.error('--binary and --out are required')
    if not math.isfinite(args.timeout) or not 0<args.timeout<=2:
        parser.error('--timeout must be finite in (0,2]')
    if not math.isfinite(args.total_timeout) or not args.timeout<=args.total_timeout<=180:
        parser.error('--total-timeout must be finite in [--timeout,180]')
    try:
        positive_sizes=parse_sizes(args.positive_sizes,allow_zero=False)
        negative_sizes=parse_sizes(args.negative_sizes,allow_zero=True)
        prepared=cases(positive_sizes,negative_sizes)
    except ValueError as error:
        parser.error(str(error))
    binary,out=args.binary.resolve(),args.out.resolve()
    if not binary.is_file() or not os.access(binary,os.X_OK):
        parser.error('--binary must be an existing executable')
    binary_sha=COST.sha256(binary)
    if binary_sha!=args.expected_sha256:
        parser.error('binary hash mismatch')
    if out.exists() or out.is_relative_to(ROOT):
        parser.error('--out must be a new directory outside the repository')
    pure=selftest()
    out.mkdir(parents=True); (out/'fixtures').mkdir()
    hashes={str(path.relative_to(ROOT)):COST.sha256(path) for path in source_paths()}
    legacy=CLI.legacy_hashes()
    report=dict(schema='lookahead-search-stress-v1',started_at_utc=datetime.now(timezone.utc).isoformat(),
        binary=str(binary),binary_sha256=binary_sha,repository_checkpoint=subprocess.check_output(
            ['git','-C',str(ROOT),'rev-parse','HEAD']).decode().strip(),
        reviewed_baseline_commit=BASELINE_COMMIT,source_sha256=hashes,
        baseline_binary_reference=dict(sha256=EXPECTED_BINARY_SHA256,
            committed_source_revision=subprocess.check_output(
                ['git','-C',str(ROOT),'rev-parse',BASELINE_COMMIT]).decode().strip()),
        measured_binary_association=('Committed three-precheck baseline at '+BASELINE_COMMIT
            if binary_sha==EXPECTED_BINARY_SHA256 else
            'Explicit alternate binary; build/source association must be supplied separately by the coordinator.'),
        observed_source_snapshot_role=('Current checkout files observed for review and before/after preservation. '
            'These hashes are not a compilation manifest or evidence that modified source is in the immutable baseline binary.'),
        limits=dict(seconds_per_case=args.timeout,total_seconds=args.total_timeout,heap='512M',
            sampled_group_rss_kib=3*1024*1024,output_bytes=65536,fixture_bytes=MAX_FIXTURE_BYTES),
        sizes=dict(positive=list(positive_sizes),negative=list(negative_sizes)),pure_selftest=pure,
        scope='Synthetic normalized prefixes; source-review expectations are separate from kernel guarantees.',
        limitations=['All-three-precheck pass annotations are reviewed expectations, not runtime branch instrumentation.',
            'A completed checker rejection refutes the original source model under its declared profile; timeout is inconclusive.',
            'The count-aware baseline binary remains immutable, even if later source development adds another necessary guard.',
            'No fixed node policy, actual capture completeness or deployment conformance is established.'],
        legacy_main=legacy,cases=[])
    started,blocked,halt=time.monotonic(),set(),False
    for case in prepared:
        fixture=out/'fixtures'/(case['name']+'.txt'); fixture.write_text(case['input'])
        row={key:value for key,value in case.items() if key not in ('input','args','contains')}
        row.update(fixture=str(fixture),fixture_sha256=COST.sha256(fixture),fixture_bytes=fixture.stat().st_size)
        if halt:
            row.update(status='not-run',inconclusive_reason='unexpected-completed-result')
        elif case['series'] in blocked:
            row.update(status='not-run',inconclusive_reason='earlier-series-inconclusive')
        elif args.total_timeout-(time.monotonic()-started)<args.timeout:
            row.update(status='not-run',inconclusive_reason='total-budget-before-full-case')
        else:
            argv=[str(binary),*[str(fixture) if value=='{input}' else value for value in case['args']],
                  '+RTS','-M512M','-s','-RTS']
            row.update(COST.measure(argv,out,case['name'],timeout=args.timeout,
                rss_limit_kib=3*1024*1024,output_limit=65536))
            if row['status']=='inconclusive':
                blocked.add(case['series'])
            elif row['status']!=case['expected']:
                halt=True
        row['expectation_met']=row['status']==case['expected']
        report['cases'].append(row)
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        print(case['name'],row['status'],row.get('seconds'),flush=True)
    report['seconds']=round(time.monotonic()-started,6)
    report['counts']=dict(Counter(case['status'] for case in report['cases']))
    report['by_category']={category:dict(Counter(case['status'] for case in report['cases']
        if case['category']==category)) for category in ('negative','positive')}
    report['all_expected']=all(case['expectation_met'] for case in report['cases'])
    report['unexpected_completed_results']=[case['name'] for case in report['cases']
        if case['status'] not in ('inconclusive','not-run') and not case['expectation_met']]
    report['binary_unchanged']=COST.sha256(binary)==binary_sha
    report['sources_unchanged']=all(COST.sha256(ROOT/path)==sha for path,sha in hashes.items())
    legacy['after_sha256']=COST.sha256(CLI.LEGACY)
    legacy['unchanged']=legacy['head_sha256']==legacy['before_sha256']==legacy['after_sha256']
    report['completed_at_utc']=datetime.now(timezone.utc).isoformat()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(report=str(out/'report.json'),counts=report['counts'],
        unexpected_completed_results=report['unexpected_completed_results']),indent=2))
    return 0 if report['all_expected'] and report['binary_unchanged'] and report['sources_unchanged'] and legacy['unchanged'] else 1


if __name__=='__main__':
    raise SystemExit(main())
