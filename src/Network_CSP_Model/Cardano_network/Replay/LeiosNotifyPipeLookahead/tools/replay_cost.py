#!/usr/bin/env python3
"""Measure the explicit compiled checker on synthetic fresh-prefix workload families.

Generated expectations have a documented source-schedule construction rationale,
not new Agda certificates. Completed checker decisions, resource failures and
unlaunched cases are reported separately. This never captures a real node log.
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
import platform
import re
import selectors
import signal
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'src/csp-ptree.agda-lib').is_file())
FAMILIES = ('serial', 'pipeline', 'cancel-drain', 'delayed-send')
MODES = ('localclient', 'localserver', 'paired')
TIME = Path('/usr/bin/time')
EVIDENCE = (
    'src/Cardano_network/LeiosNotifyPipeLookahead/ClientModel.agda',
    'src/Cardano_network/LeiosNotifyPipeLookahead/Model.agda',
    'src/Cardano_network/LeiosNotifyPipeLookahead/DriverModel.agda',
    'src/Cardano_network/LeiosNotifyPipeLookahead/Wire/Client.agda',
    'src/Cardano_network/LeiosNotifyPipeLookahead/Wire/Server.agda',
    'src/Cardano_network/Replay/LeiosNotifyPipeLookahead/DriverDecideNativeTests.agda',
)


def helper():
    """Reuse the existing fixture format and strict verdict classifier, not another checker."""
    spec = importlib.util.spec_from_file_location('lookahead_cost_cli', HERE / 'test_lookahead_cli.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CLI = helper()


def sha256(path):
    """Hash source, fixture and executable bytes incrementally."""
    return CLI.sha256(path)


def workload(family, count, payloads='repeated'):
    """Project a documented physical schedule to two independently ordered endpoint hooks."""
    if family not in FAMILIES or payloads not in ('repeated', 'distinct'):
        raise ValueError('unsupported workload family or payload policy')
    if type(count) is not int or not 1 <= count <= 100000:
        raise ValueError('count must be an integer in [1,100000]')
    client, server = [], []

    def request():
        client.append('Send RequestNext')
        server.append('Recv RequestNext')

    def response(index, canceled=False):
        message = ('Canceled' if canceled else
                   'BlockOffer %s 23 31' % format(0x43 + (index if payloads == 'distinct' else 0), 'x'))
        server.append('Send ' + message)
        client.append('Recv ' + message)

    if family in ('pipeline', 'cancel-drain'):
        for _ in range(count):
            request()
        if family == 'cancel-drain':
            client.append('Send Quit')
            server.append('Recv Quit')
        for index in range(count):
            response(index, family == 'cancel-drain')
    else:
        for index in range(count):
            if family == 'serial':
                request()
                response(index)
            else:
                # Commit/decode the request, then the reply, before their Send
                # hooks. Emit both pending hooks before starting the next cycle.
                response(index)
                request()
                server[-2:] = [server[-1], server[-2]]
    if family != 'cancel-drain':
        client.append('Send Quit')
        server.append('Recv Quit')
    server.append('Send Done')
    client.append('Recv Done')
    return {'family': family, 'count': count, 'payloads': payloads,
            'client': client, 'server': server,
            'peak_logical_outstanding_requests': count if family in ('pipeline', 'cancel-drain') else 1,
            'delayed_client_send_cycles': count if family == 'delayed-send' else 0,
            'notification_values': count if payloads == 'distinct' and family != 'cancel-drain' else int(family != 'cancel-drain'),
            'expectation': 'accepted-prefix',
            'expectation_basis': 'Documented source-schedule construction; not a new kernel-checked witness.'}


def case_text(data, mode):
    """Use the existing normalized local/pair grammar with explicit synthetic declarations."""
    if mode == 'localclient':
        return CLI.local_text('client', data['client'])
    if mode == 'localserver':
        return CLI.local_text('server', data['server'])
    if mode != 'paired':
        raise ValueError('unsupported replay mode')
    return CLI.pair_text(list(enumerate(data['client'], 11)), list(enumerate(data['server'], 17)))


def arguments(binary, mode, fixture, heap):
    """Fix the same generic-client/unit-return profile and node-next server contract for every run."""
    if mode == 'paired':
        args = ['--paired-notify-lookahead', str(fixture)]
    else:
        args = ['--notify-lookahead', str(fixture), '--role', 'client' if mode == 'localclient' else 'server']
    return [str(binary), *args, '--next-contract', 'node-next', '--observation', 'driver-log',
            '--assume-fresh', '+RTS', '-M' + heap, '-s', '-RTS']


def group_rss(pid):
    """Sample the launched GNU-time wrapper and its descendants; Linux only, best effort."""
    pending, seen, total = [pid], set(), 0
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        try:
            status = Path('/proc/%d/status' % current).read_text()
            total += int(next(line for line in status.splitlines() if line.startswith('VmRSS:')).split()[1])
            pending += list(map(int, Path('/proc/%d/task/%d/children' % (current, current)).read_text().split()))
        except (OSError, StopIteration, ValueError):
            pass
    return total


def terminate(process):
    """Stop and reap only the explicitly launched process group, including timeout children."""
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def measure(argv, out, name, timeout=5.0, rss_limit_kib=3*1024*1024, output_limit=65536,
            poll_seconds=0.005):
    """Bound runtime/output/RSS; obtain separate GNU-time child peak and sampled group peak."""
    if not math.isfinite(timeout) or timeout <= 0 or not 0 < poll_seconds <= 0.1:
        raise ValueError('finite positive timeout and poll interval in (0,0.1] required')
    if type(rss_limit_kib) is not int or rss_limit_kib <= 0 or type(output_limit) is not int or output_limit <= 0:
        raise ValueError('RSS/output limits must be positive integers')
    if not re.fullmatch(r'[A-Za-z0-9_.-]+', name):
        raise ValueError('unsafe artifact basename')
    timing_path = out / (name + '.time')
    if timing_path.exists():
        raise ValueError('timing artifact already exists')
    wrapped = [str(TIME), '-f', '%M\n%e\n%U\n%S', '-o', str(timing_path), '--', *argv]
    started, peak, failure, error = time.monotonic(), 0, None, None
    output = {'stdout': bytearray(), 'stderr': bytearray()}
    process, selector = None, selectors.DefaultSelector()
    try:
        process = subprocess.Popen(wrapped, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, start_new_session=True)
        for stream, label in [(process.stdout, 'stdout'), (process.stderr, 'stderr')]:
            selector.register(stream, selectors.EVENT_READ, label)
        while selector.get_map():
            peak = max(peak, group_rss(process.pid))
            if peak > rss_limit_kib:
                failure = 'sampled-rss-limit'
            elif time.monotonic() - started >= timeout:
                failure = 'timeout'
            if failure:
                terminate(process)
                break
            for key, _ in selector.select(min(poll_seconds, max(0, timeout - (time.monotonic() - started)))):
                chunk = os.read(key.fileobj.fileno(), 16384)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                available = output_limit - sum(map(len, output.values()))
                output[key.data].extend(chunk[:max(0, available)])
                if len(chunk) > available:
                    failure = 'output-limit'
                    terminate(process)
                    break
            if failure:
                break
        if failure is None:
            try:
                process.wait(timeout=max(0, timeout - (time.monotonic() - started)))
            except subprocess.TimeoutExpired:
                failure = 'timeout'
                terminate(process)
    except OSError as exc:
        error = str(exc)
    finally:
        if process is not None:
            if process.poll() is None:
                terminate(process)
            for stream in (process.stdout, process.stderr):
                if stream is not None:
                    stream.close()
        selector.close()
    seconds = time.monotonic() - started
    text = {key: value.decode('utf-8', errors='replace') for key, value in output.items()}
    code = None if process is None else process.returncode
    status, reason = CLI.classify(code, text['stdout'], text['stderr'], timed_out=failure == 'timeout',
                                  truncated=failure == 'output-limit', launch_error=error)
    if failure is not None:
        status, reason = 'inconclusive', failure
    metrics = None
    if timing_path.is_file():
        lines = timing_path.read_text().splitlines()
        # GNU time prepends an explanatory line when the command exits nonzero.
        if len(lines) >= 4:
            try:
                metrics = {'child_peak_rss_kib': int(lines[-4]), 'gnu_elapsed_seconds': float(lines[-3]),
                           'user_seconds': float(lines[-2]), 'system_seconds': float(lines[-1])}
            except ValueError:
                pass
    logs = {}
    for key, content in text.items():
        path = out / (name + '.' + key)
        path.write_text(content)
        logs[key] = {'path': str(path), 'sha256': sha256(path), 'retained_bytes': len(output[key])}
    return {'argv': argv, 'measured_argv': wrapped, 'exit_code': code, 'status': status,
            'inconclusive_reason': reason, 'seconds': round(seconds, 6),
            'peak_sampled_group_rss_kib': peak or None, 'gnu_time': metrics,
            'launch_error': error, 'timing_artifact': str(timing_path),
            'timing_sha256': sha256(timing_path) if timing_path.is_file() else None, 'logs': logs}


def selftest():
    """Check fixture conservation/ordering and real subprocess limits without invoking Agda."""
    count = 0
    for family in FAMILIES:
        for n in (1, 2, 7):
            for payloads in ('repeated', 'distinct'):
                data = workload(family, n, payloads)
                client, server = data['client'], data['server']
                assert len(client) == len(server) == 2*n+2
                assert client.count('Send RequestNext') == server.count('Recv RequestNext') == n
                assert client.count('Send Quit') == server.count('Recv Quit') == 1
                assert client[-1] == 'Recv Done' and server[-1] == 'Send Done'
                assert [x[5:] for x in client if x.startswith('Recv ')] == [x[5:] for x in server if x.startswith('Send ')]
                if family == 'delayed-send':
                    assert all(client[2*i].startswith('Recv ') and client[2*i+1] == 'Send RequestNext' for i in range(n))
                    assert all(server[2*i] == 'Recv RequestNext' and server[2*i+1].startswith('Send ') for i in range(n))
                if family == 'cancel-drain':
                    assert client.index('Send Quit') < client.index('Recv Canceled')
                    assert server.index('Recv Quit') < server.index('Send Canceled')
                for mode in MODES:
                    assert case_text(data, mode).endswith('\n')
                count += 1
    for bad in (0, -1, True, 100001):
        try:
            workload('serial', bad)
        except ValueError:
            count += 1
        else:
            raise AssertionError('invalid count accepted')
    controls = []
    with tempfile.TemporaryDirectory(prefix='lookahead-cost-selftest-') as directory:
        out = Path(directory)
        examples = [
            ('accepted', "print('accepted-prefix')", {}, 'accepted-prefix'),
            ('rejected', "print('protocol-rejected');raise SystemExit(1)", {}, 'protocol-rejected'),
            ('invalid', "print('invalid-input');raise SystemExit(2)", {}, 'invalid-input'),
            ('untagged', 'raise SystemExit(1)', {}, 'inconclusive'),
            ('mismatch', "print('accepted-prefix');raise SystemExit(1)", {}, 'inconclusive'),
            ('heap', "import sys;print('accepted-prefix');print('Heap exhausted',file=sys.stderr)", {}, 'inconclusive'),
            ('timeout', 'import time;time.sleep(2)', {'timeout': 0.02}, 'inconclusive'),
            ('rss', 'import time;time.sleep(2)', {'rss_limit_kib': 1}, 'inconclusive'),
            ('output', "print('accepted-prefix');print('x'*10000)", {'output_limit': 128}, 'inconclusive'),
        ]
        for name, code, options, expected in examples:
            result = measure([sys.executable, '-I', '-B', '-c', code], out, name, **options)
            assert result['status'] == expected, result
            if expected != 'inconclusive':
                assert result['gnu_time']['child_peak_rss_kib'] > 0, result
            controls.append({'name': name, 'status': result['status'], 'reason': result['inconclusive_reason']})
    return {'selftest': 'passed', 'fixture_cases': count, 'subprocess_controls': controls,
            'checker_processes_launched': 0,
            'scope': 'Synthetic generation and resource/classification controls; no model or deployed conformance proof.'}


def run(binary, out, sizes, families, modes, payloads, timeout, total_timeout, heap,
        rss_limit_kib, output_limit=65536):
    """Run each series serially; skip larger sizes after its first operational inconclusive result."""
    started = time.monotonic()
    identities = [Path(__file__), HERE/'test_lookahead_cli.py', *[ROOT/name for name in EVIDENCE]]
    report = {'schema': 'lookahead-replay-cost-v1', 'started_at_utc': datetime.now(timezone.utc).isoformat(),
              'repository_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'binary': str(binary), 'binary_sha256': sha256(binary), 'serial': True,
              'environment': {'platform': platform.platform(), 'python': sys.version,
                              'logical_cpus': os.cpu_count(), 'load_average_at_start': list(os.getloadavg())},
              'source_sha256': {str(p.relative_to(ROOT)): sha256(p) for p in identities},
              'gnu_time': {'path': str(TIME), 'sha256': sha256(TIME),
                           'version': subprocess.check_output([str(TIME), '--version'], text=True).splitlines()[0]},
              'limits': {'seconds_per_case': timeout, 'total_seconds': total_timeout, 'heap': heap,
                         'sampled_group_rss_kib': rss_limit_kib, 'output_bytes': output_limit,
                         'rss_poll_seconds': 0.005},
              'profile': {'serverContract': 'node-next', 'clientCallbacks': 'generic-successful',
                          'return': 'unit', 'observation': 'driver-log', 'eof': 'prefix'},
              'limitations': ['Inputs and fresh endpoint declarations are synthetic; no real capture is read.',
                  'Expected acceptance has a documented source-schedule rationale; no new Agda witness is certified.',
                  'Only completed matching exit/tag results are model decisions; timeouts and heap/RSS/output failures are inconclusive.',
                  'GNU time reports Linux child peak RSS; sampled RSS includes the time wrapper and descendants and may miss brief peaks.',
                  'Larger cases skipped after a budget failure have no checker verdict; no universal complexity bound follows.',
                  'This does not establish production throughput, latency, capture fidelity or deployed implementation conformance.'],
              'cases': []}
    stop_series = set()
    for mode in modes:
        for family in families:
            for policy in payloads:
                series = mode, family, policy
                for n in sizes:
                    name = '%s_%s_%s_%06d' % (*series, n)
                    item = {'name': name, 'mode': mode, 'family': family, 'count': n, 'payloads': policy,
                            'expected': 'accepted-prefix', 'status': 'not-run'}
                    if series in stop_series or time.monotonic()-started >= total_timeout:
                        item['skip_reason'] = ('earlier-series-inconclusive' if series in stop_series else 'total-time-budget')
                    else:
                        data = workload(family, n, policy)
                        fixture = out / (name + '.txt')
                        fixture.write_text(case_text(data, mode))
                        item.update({key: data[key] for key in ('peak_logical_outstanding_requests', 'delayed_client_send_cycles', 'notification_values', 'expectation_basis')})
                        item.update(fixture=str(fixture), fixture_sha256=sha256(fixture), fixture_bytes=fixture.stat().st_size,
                                    client_rows=len(data['client']), server_rows=len(data['server']),
                                    checker_rows=len(data['client'])+len(data['server']) if mode == 'paired' else len(data['client']))
                        item.update(measure(arguments(binary, mode, fixture, heap), out, name,
                                            timeout=min(timeout, max(0.000001, total_timeout-(time.monotonic()-started))),
                                            rss_limit_kib=rss_limit_kib, output_limit=output_limit))
                        item['expectation_met'] = item['status'] == item['expected']
                        if item['status'] == 'inconclusive':
                            stop_series.add(series)
                    report['cases'].append(item)
                    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
                    print(name + ': ' + item['status'] + (' %.3fs' % item['seconds'] if 'seconds' in item else ''), flush=True)
    report['counts'] = dict(Counter(case['status'] for case in report['cases']))
    report['by_mode'] = {mode: dict(Counter(case['status'] for case in report['cases'] if case['mode'] == mode)) for mode in modes}
    report['unexpected_completed_results'] = [case['name'] for case in report['cases'] if case['status'] in ('protocol-rejected','invalid-input')]
    report['binary_unchanged'] = report['binary_sha256'] == sha256(binary)
    report['sources_unchanged'] = all(sha256(ROOT/name) == digest for name,digest in report['source_sha256'].items())
    report['seconds'] = round(time.monotonic()-started, 6)
    report['completed_at_utc'] = datetime.now(timezone.utc).isoformat()
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


def main():
    """Require explicit binary/output and finite budgets; do not rebuild or discover a checker."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--selftest', action='store_true')
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--sizes', default='1,2,4,8,16,32,64')
    parser.add_argument('--families', default=','.join(FAMILIES))
    parser.add_argument('--modes', default=','.join(MODES))
    parser.add_argument('--payloads', choices=('repeated','distinct','both'), default='repeated')
    parser.add_argument('--timeout', type=float, default=5.0)
    parser.add_argument('--total-timeout', type=float, default=120.0)
    parser.add_argument('--heap', default='512M')
    parser.add_argument('--rss-limit-mib', type=int, default=3072)
    args = parser.parse_args()
    if args.selftest:
        if args.binary or args.out:
            parser.error('--selftest does not use --binary/--out')
        print(json.dumps(selftest(), indent=2))
        return
    if not args.binary or not args.out:
        parser.error('--binary and --out are required')
    try:
        sizes = sorted(set(map(int, args.sizes.split(','))))
        families, modes = args.families.split(','), args.modes.split(',')
        if not sizes or not all(1 <= n <= 100000 for n in sizes):
            raise ValueError('sizes must be in [1,100000]')
        if len(families) != len(set(families)) or any(x not in FAMILIES for x in families):
            raise ValueError('families must be distinct supported names')
        if len(modes) != len(set(modes)) or any(x not in MODES for x in modes):
            raise ValueError('modes must be distinct supported names')
        if not all(math.isfinite(x) and x > 0 for x in (args.timeout,args.total_timeout)):
            raise ValueError('timeouts must be finite positive numbers')
        if args.rss_limit_mib <= 0 or not re.fullmatch(r'[1-9][0-9]*[KMG]', args.heap):
            raise ValueError('positive RSS and heap limits required')
        binary, out = args.binary.resolve(), args.out.resolve()
        if not binary.is_file() or not os.access(binary, os.X_OK) or not TIME.is_file():
            raise ValueError('explicit executable binary and /usr/bin/time required')
        if out.is_relative_to(ROOT) or out.exists():
            raise ValueError('output must be a new directory outside the repository')
    except ValueError as exc:
        parser.error(str(exc))
    out.mkdir(parents=True)
    policies = ('repeated','distinct') if args.payloads == 'both' else (args.payloads,)
    report = run(binary, out, sizes, families, modes, policies, args.timeout, args.total_timeout,
                 args.heap, args.rss_limit_mib*1024)
    print(json.dumps({'counts': report['counts'], 'report': str(out/'report.json')}, indent=2))
    raise SystemExit(1 if report['unexpected_completed_results'] or not report['binary_unchanged'] or not report['sources_unchanged'] else 0)


if __name__ == '__main__':
    main()
