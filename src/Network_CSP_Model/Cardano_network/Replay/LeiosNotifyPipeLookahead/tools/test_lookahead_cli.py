#!/usr/bin/env python3
"""Run small normalized-input regressions against an explicitly supplied compiled CLI.

This is executable regression evidence, not a raw-capture or deployment certificate.
Fixtures/logs/report are written only to a new caller-selected directory outside
this repository. Checker processes run serially with a timeout and 512M RTS heap.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = next(parent for parent in HERE.parents if (parent / 'src/csp-ptree.agda-lib').is_file())
LEGACY = ROOT / 'src/Cardano_network/Replay/Main.agda'
STATUS_CODES = {'accepted-prefix': 0, 'protocol-rejected': 1, 'invalid-input': 2}
RTS = ['+RTS', '-M512M', '-RTS']
OUTPUT_LIMIT = 65536


def sha256(path):
    """Hash complete artifacts in bounded memory, without treating a digest as provenance proof."""
    digest = hashlib.sha256()
    with Path(path).open('rb') as source:
        for block in iter(lambda: source.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


def classify(code, stdout, stderr, timed_out=False, truncated=False, launch_error=None):
    """Only an exact first-line tag with matching exit code is a protocol/input verdict."""
    if timed_out:
        return 'inconclusive', 'timeout'
    if launch_error:
        return 'inconclusive', 'launch-error'
    if truncated:
        return 'inconclusive', 'output-limit'
    lower = stderr.lower()
    if any(marker in lower for marker in ('heap exhausted', 'out of memory', 'memory exhausted',
                                         'stack space overflow', 'allocation limit exceeded')):
        return 'inconclusive', 'runtime-resource-failure'
    tag = stdout.splitlines()[0] if stdout.splitlines() else None
    if tag not in STATUS_CODES:
        return 'inconclusive', 'missing-or-unknown-status-tag'
    if code != STATUS_CODES[tag]:
        return 'inconclusive', 'status-exit-mismatch'
    return tag, None


def local_text(role, rows):
    """Retain all normalized lines after an explicit role header, including deliberate blank rows."""
    return '\n'.join(['role ' + role, *rows]) + '\n'


def pair_text(client, server, client_source='client-source.log', server_source='server-source.log'):
    """Declare a tiny fresh pair while retaining explicit independent source-line coordinates."""
    lines = ['pair LeiosNotifyP cli-connection cli-session',
             'client node-client connection-client 0 fresh ' + client_source,
             'server node-server connection-server 0 fresh ' + server_source]
    lines += ['client %d %s' % (line, event) for line, event in client]
    lines += ['server %d %s' % (line, event) for line, event in server]
    return '\n'.join(lines) + '\n'


def fixtures():
    """Keep cases small; larger concurrency witnesses belong in the checked Agda regressions."""
    cases = []

    def local(name, rows, status, role='client', contract='generic-next', contains=(), header=None):
        args = ['--notify-lookahead', '{input}', '--role', role, '--next-contract', contract,
                '--observation', 'driver-log', '--assume-fresh']
        case = {'name': name, 'input': local_text(header or role, rows), 'args': args,
                'expected': status, 'contains': list(contains)}
        cases.append(case)
        return case

    def paired(name, client, server, status, contract='generic-next', contains=()):
        case = {'name': name, 'input': pair_text(client, server),
                'args': ['--paired-notify-lookahead', '{input}', '--next-contract', contract,
                         '--observation', 'driver-log', '--assume-fresh'],
                'expected': status, 'contains': list(contains)}
        cases.append(case)
        return case

    accept, reject, invalid = 'accepted-prefix', 'protocol-rejected', 'invalid-input'
    local('local_client_empty', [], accept)
    local('local_server_empty', [], accept, role='server', contract='node-next')
    local('local_client_request_eof', ['Send RequestNext'], accept)
    local('local_server_request_eof', ['Recv RequestNext'], accept, role='server')
    local('local_early_announcement_empty', ['Recv BlockAnnouncement -'], accept)
    local('local_early_announcement_fields', ['Recv BlockAnnouncement 43 23 31'], accept)
    local('local_early_offer', ['Recv BlockOffer 43 23 31'], accept)
    local('local_early_txs_offer', ['Recv BlockTxsOffer 43 23'], accept)
    local('local_early_votes_duplicates', ['Recv Votes 43:71,49:79,43:71'], accept)
    local('local_early_votes_empty', ['Recv Votes -'], accept)
    local('local_early_canceled_node_contract_unused', ['Recv Canceled'], accept, contract='node-next',
          contains=('server contract unused by local client',))
    local('local_two_extra_replies', ['Recv BlockAnnouncement -', 'Recv Canceled'], reject)
    local('local_lead_cannot_quit', ['Recv Canceled', 'Send Quit'], reject)
    local('local_lead_finish_then_close', ['Recv Canceled', 'Send RequestNext', 'Send Quit', 'Recv Done'], accept)
    local('local_idle_close', ['Send Quit', 'Recv Done'], accept)
    local('local_client_done_without_quit', ['Recv Done'], reject)
    local('local_server_done_without_quit', ['Send Done'], reject, role='server')
    local('server_generic_cancel_before_quit', ['Recv RequestNext', 'Send Canceled'], accept, role='server')
    local('server_node_cancel_before_quit', ['Recv RequestNext', 'Send Canceled'], reject,
          role='server', contract='node-next')
    local('server_node_cancel_after_quit', ['Recv RequestNext', 'Recv Quit', 'Send Canceled', 'Send Done'], accept,
          role='server', contract='node-next')
    local('local_role_mismatch_empty', [], invalid, role='client', header='server', contains=('input line 1',))
    local('local_wrong_command_agency', ['Recv RequestNext'], invalid, contains=('wrong agency:', 'input line 2'))
    local('local_wrong_response_agency', ['Send Votes -'], invalid, contains=('wrong agency:',))
    local('local_server_wrong_command_agency', ['Send Quit'], invalid, role='server', contains=('wrong agency:',))
    local('local_unparsed_second_row', ['Send RequestNext', 'not-an-event'], invalid,
          contains=('input line 3', 'unparsed or unsupported'))
    local('local_blank_row_retained', ['', 'Send RequestNext'], invalid,
          contains=('input line 2', 'unparsed or unsupported'))
    for name, row in [
        ('offer_missing_size', 'Recv BlockOffer 43 23'),
        ('offer_bad_hash', 'Recv BlockOffer nothex 23 31'),
        ('offer_negative_slot', 'Recv BlockOffer 43 -1 31'),
        ('announcement_missing_fields', 'Recv BlockAnnouncement 43 23'),
        ('announcement_bad_size', 'Recv BlockAnnouncement 43 23 size'),
        ('votes_double_colon', 'Recv Votes 43::71'),
        ('votes_missing_voter', 'Recv Votes 43:'),
        ('votes_trailing_comma', 'Recv Votes 43:71,'),
        ('votes_empty_element', 'Recv Votes 43:71,,49:79')]:
        local('local_malformed_' + name, [row], invalid, contains=('unparsed or unsupported',))

    paired('paired_empty', [], [], accept)
    paired('paired_request_server_eof', [(11, 'Send RequestNext')], [], accept)
    paired('paired_receive_client_eof', [], [(17, 'Recv RequestNext')], accept)
    paired('paired_both_receives_send_hooks_pending', [(11, 'Recv BlockOffer 43 23 31')],
           [(17, 'Recv RequestNext')], accept)
    paired('paired_exact_offer_match', [(11, 'Recv BlockOffer 43 23 31')],
           [(17, 'Recv RequestNext'), (19, 'Send BlockOffer 43 23 31')], accept)
    paired('paired_exact_offer_hash_mismatch', [(11, 'Recv BlockOffer 49 23 31')],
           [(17, 'Recv RequestNext'), (19, 'Send BlockOffer 43 23 31')], reject)
    paired('paired_optional_empty_announcement', [(11, 'Recv BlockAnnouncement -')],
           [(17, 'Recv RequestNext'), (19, 'Send BlockAnnouncement -')], accept)
    paired('paired_optional_announcement_size_mismatch', [(11, 'Recv BlockAnnouncement 43 23 31')],
           [(17, 'Recv RequestNext'), (19, 'Send BlockAnnouncement 43 23 32')], reject)
    paired('paired_duplicate_votes_match', [(11, 'Recv Votes 43:71,49:79,43:71')],
           [(17, 'Recv RequestNext'), (19, 'Send Votes 43:71,49:79,43:71')], accept)
    paired('paired_vote_order_mismatch', [(11, 'Recv Votes 49:79,43:71,43:71')],
           [(17, 'Recv RequestNext'), (19, 'Send Votes 43:71,49:79,43:71')], reject)
    paired('paired_vote_duplicate_removed', [(11, 'Recv Votes 43:71,49:79')],
           [(17, 'Recv RequestNext'), (19, 'Send Votes 43:71,49:79,43:71')], reject)
    paired('paired_idle_quit_done', [(11, 'Send Quit'), (13, 'Recv Done')],
           [(17, 'Recv Quit'), (19, 'Send Done')], accept, contract='node-next')
    paired('paired_unmatched_reply', [(11, 'Recv Canceled')], [], reject)
    paired('paired_done_without_quit', [(11, 'Recv Done')], [(17, 'Send Done')], reject)
    paired('paired_agency_preserves_client_source123', [(123, 'Recv Quit')], [], invalid,
           contains=('client source client-source.log line 123', 'wrong agency:', 'Recv Quit'))
    paired('paired_agency_preserves_server_source123', [], [(123, 'Send RequestNext')], invalid,
           contains=('server source server-source.log line 123', 'wrong agency:', 'Send RequestNext'))
    paired('paired_malformed_vote', [(123, 'Recv Votes 43::71')], [], invalid,
           contains=('paired input line 4',))
    paired('paired_nonincreasing_coordinates', [(123, 'Send RequestNext'), (123, 'Send Quit')], [], invalid,
           contains=('paired input line 5',))
    changed = paired('paired_wrong_protocol', [], [], invalid)
    changed['input'] = changed['input'].replace('pair LeiosNotifyP', 'pair LeiosFetchP', 1)
    changed = paired('paired_unasserted_endpoint', [], [], invalid)
    changed['input'] = changed['input'].replace('0 fresh client-source.log', '0 unknown client-source.log', 1)

    case = local('missing_assume_fresh', [], invalid)
    case['args'].remove('--assume-fresh')
    case = local('unsupported_observation', [], invalid)
    case['args'][case['args'].index('driver-log')] = 'source-operations'
    case = local('unsupported_contract', [], invalid)
    case['args'][case['args'].index('generic-next')] = 'inferred'
    case = local('unsupported_role', [], invalid)
    case['args'][case['args'].index('client')] = 'both'
    case = local('unsupported_depth_option', [], invalid)
    case['args'] += ['--depth', '4']
    case = local('unsupported_legacy_mode', [], invalid)
    case['args'][0] = '--leiosnotify'
    case = local('missing_input_is_inconclusive', [], 'inconclusive')
    case['input'] = None
    return cases


def read_log(path):
    """Read only a bounded output prefix, retaining full on-disk logs for investigation."""
    with path.open('rb') as source:
        raw = source.read(OUTPUT_LIMIT + 1)
    return raw[:OUTPUT_LIMIT].decode('utf-8', errors='replace'), len(raw) > OUTPUT_LIMIT


def execute(binary, case, out, timeout):
    """Run exactly one checker process; a timeout kills its entire process group before continuing."""
    fixture = out / 'fixtures' / (case['name'] + '.txt')
    if case['input'] is not None:
        fixture.write_text(case['input'], encoding='utf-8')
    argv = [str(binary), *[str(fixture) if arg == '{input}' else arg for arg in case['args']], *RTS]
    stdout_path = out / (case['name'] + '.stdout')
    stderr_path = out / (case['name'] + '.stderr')
    start = time.monotonic()
    code, timed_out, error = None, False, None
    with stdout_path.open('wb') as stdout_file, stderr_path.open('wb') as stderr_file:
        try:
            child = subprocess.Popen(argv, stdout=stdout_file, stderr=stderr_file, start_new_session=True)
        except OSError as exc:
            error = str(exc)
        else:
            try:
                code = child.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                code = child.wait()
            except BaseException:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                child.wait()
                raise
    stdout, large_out = read_log(stdout_path)
    stderr, large_err = read_log(stderr_path)
    status, reason = classify(code, stdout, stderr, timed_out, large_out or large_err, error)
    missing_details = [text for text in case['contains'] if text not in stdout]
    return {'name': case['name'], 'argv': argv, 'expected': case['expected'], 'actual': status,
            'passed': status == case['expected'] and not missing_details,
            'exit_code': code, 'seconds': round(time.monotonic() - start, 3),
            'inconclusive_reason': reason, 'launch_error': error, 'timed_out': timed_out,
            'missing_expected_details': missing_details,
            'stdout': str(stdout_path), 'stderr': str(stderr_path),
            'stdout_sha256': sha256(stdout_path), 'stderr_sha256': sha256(stderr_path),
            'fixture': str(fixture), 'fixture_sha256': sha256(fixture) if fixture.is_file() else None}


def legacy_hashes():
    """Compare the actual legacy Main to HEAD without compiling or changing it."""
    result = subprocess.run(['git', 'show', 'HEAD:src/Cardano_network/Replay/Main.agda'],
                            cwd=ROOT, capture_output=True, timeout=10, check=True)
    return {'path': str(LEGACY), 'head_sha256': hashlib.sha256(result.stdout).hexdigest(),
            'before_sha256': sha256(LEGACY)}


def selftest():
    """Exercise verdict classification and fixture coverage without starting any checker process."""
    examples = [(0, 'accepted-prefix\nmodel', '', 'accepted-prefix'),
                (1, 'protocol-rejected\nmodel', '', 'protocol-rejected'),
                (2, 'invalid-input\nusage', '', 'invalid-input'),
                (1, '', 'file not found', 'inconclusive'),
                (-9, '', '', 'inconclusive'),
                (2, 'accepted-prefix\n', '', 'inconclusive'),
                (1, 'rejected by some prose\n', '', 'inconclusive'),
                (0, 'accepted-prefix\n', 'Heap exhausted', 'inconclusive')]
    for code, stdout, stderr, expected in examples:
        assert classify(code, stdout, stderr)[0] == expected
    assert classify(0, 'accepted-prefix', '', timed_out=True)[0] == 'inconclusive'
    assert classify(0, 'accepted-prefix', '', truncated=True)[0] == 'inconclusive'
    cases = fixtures()
    assert len({case['name'] for case in cases}) == len(cases)
    assert all(case['expected'] in {*STATUS_CODES, 'inconclusive'} for case in cases)
    assert any('line 123' in detail for case in cases for detail in case['contains'])
    assert sum(case['input'] is None for case in cases) == 1
    return {'selftest': 'passed', 'classification_cases': len(examples) + 2,
            'compiled_cli_cases_prepared': len(cases), 'checker_processes_launched': 0,
            'scope': 'Python classifier/fixture tests, not compiled checker or raw-log validation'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--out', type=Path, help='new artifact directory outside the repository')
    parser.add_argument('--timeout', type=float, default=15.0, help='finite seconds per checker process (default15)')
    parser.add_argument('--selftest', action='store_true')
    args = parser.parse_args()
    if args.selftest:
        if args.binary or args.out:
            parser.error('--selftest does not accept --binary/--out or launch a checker')
        print(json.dumps(selftest(), indent=2))
        return
    if not args.binary or not args.out:
        parser.error('--binary and --out are required unless --selftest is selected')
    if not 0 < args.timeout <= 120:
        parser.error('--timeout must be in (0,120] seconds')
    binary, out = args.binary.resolve(), args.out.resolve()
    if not binary.is_file() or not os.access(binary, os.X_OK):
        parser.error('--binary must name an existing executable supplied by the caller')
    if out.is_relative_to(ROOT) or out.exists():
        parser.error('--out must be a new/nonexistent directory outside the repository')
    out.mkdir(parents=True)
    (out / 'fixtures').mkdir()
    legacy = legacy_hashes()
    report = {'schema': 'lookahead-compiled-cli-regressions-v1',
              'started_at_utc': datetime.now(timezone.utc).isoformat(),
              'binary': str(binary), 'binary_sha256': sha256(binary),
              'script_sha256': sha256(__file__), 'timeout_seconds_per_case': args.timeout,
              'rts_arguments': RTS, 'serial': True, 'legacy_main': legacy, 'cases': [],
              'scope': 'Direct compiled CLI regressions on generated tiny normalized fixtures; not raw capture evidence',
              'limitations': ['Fixture fresh/endpoint declarations are deliberately synthetic test assertions.',
                              'Unknown exit/tag, missing file, crash, timeout and resource failure remain inconclusive.',
                              'No deployment provenance, real-log capture completeness or clean Done from EOF is established.']}
    destination = out / 'report.json'
    prepared = fixtures()
    report['prepared_case_count'] = len(prepared)
    for case in prepared:
        result = execute(binary, case, out, args.timeout)
        report['cases'].append(result)
        destination.write_text(json.dumps(report, indent=2) + '\n')
        print(case['name'] + ': ' + result['actual'] + (' PASS' if result['passed'] else ' FAIL'), flush=True)
        if result['actual'] == 'inconclusive' and case['expected'] != 'inconclusive':
            report['aborted_after'] = case['name']
            break
    legacy['after_sha256'] = sha256(LEGACY)
    legacy['unchanged'] = legacy['before_sha256'] == legacy['after_sha256'] == legacy['head_sha256']
    report['binary_unchanged'] = report['binary_sha256'] == sha256(binary)
    report['passed'] = (len(report['cases']) == len(prepared) and
                        all(case['passed'] for case in report['cases']) and
                        legacy['unchanged'] and report['binary_unchanged'])
    report['completed_at_utc'] = datetime.now(timezone.utc).isoformat()
    report['counts'] = {'cases': len(report['cases']), 'passed': sum(case['passed'] for case in report['cases']),
                        'expected_operational_inconclusive': sum(case['expected'] == 'inconclusive' for case in report['cases'])}
    destination.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'passed': report['passed'], 'counts': report['counts'], 'report': str(destination)}, indent=2))
    raise SystemExit(0 if report['passed'] else 1)


if __name__ == '__main__':
    main()
