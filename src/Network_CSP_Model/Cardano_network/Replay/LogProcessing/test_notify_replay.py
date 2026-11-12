#!/usr/bin/env python3
"""Compiled CLI integration tests: python3 -I test_notify_replay.py /tmp/BUILD/Main."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def main(binary):
    """Check verdict text: the CLI intentionally does not encode it in exit codes."""
    binary = str(Path(binary).resolve())
    # Help must succeed without trying to open an input file; aliases agree.
    helps = [subprocess.run([binary, flag], check=True, capture_output=True,
                            text=True, timeout=10) for flag in ('--help', '-h')]
    assert helps[0].stdout == helps[1].stdout
    assert helps[0].stdout.startswith('usage:') and not any(r.stderr for r in helps)
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        def check(contents, expected, mode='--interleaved', bounds=()):
            path = root / 'input.txt'
            path.write_text(contents)
            args = [binary] + ([mode] if mode else []) + [str(path)] + [str(x) for x in bounds]
            result = subprocess.run(args, check=True, capture_output=True, text=True).stdout
            assert result.startswith(expected), (contents, expected, result)
            return result
        rounds = ('Send RequestNext\nRecv BlockAnnouncement -\n'
                  'Send RequestNext\nRecv BlockAnnouncement ab 3 20\n'
                  'Send RequestNext\nRecv BlockOffer cd 4 30\n'
                  'Send RequestNext\nRecv BlockTxsOffer ef 5\n'
                  'Send RequestNext\nRecv Votes ab:2,cd:4\nSend Quit\nRecv Done\n')
        check('role client\n' + rounds, 'accepted (12 events, 1 sessions)', '--notify')
        server = rounds.replace('Send', 'TEMP').replace('Recv', 'Send').replace('TEMP', 'Recv')
        check('role server\n' + server, 'accepted (12 events, 1 sessions)', '--notify')
        for events, index in [('Recv Votes -\n', 1),
                              ('Send RequestNext\nSend RequestNext\n', 2),
                              ('Send RequestNext\nSend Done\n', 2),
                              ('Send Quit\nSend RequestNext\n', 2)]:
            check('role client\n' + events, f'rejected at index {index}', '--notify')
        check('role client\nSend RequestNext\n', 'accepted (1 events, 1 sessions)', '--notify')
        check('role client\nRecv BlockAnnouncement ab\n', 'parse error', '--notify')
        for votes in ['ab::2', 'ab:2,,cd:4', ',ab:2', 'ab:2,']:
            check('role client\nRecv Votes ' + votes + '\n', 'parse error', '--notify')
        check('sessions notify:client fetch:client notify:server\n'
              '0 Send RequestNext\n1 Send BlockRequest ab 3\n2 Recv RequestNext\n'
              '0 Recv Votes -\n2 Send BlockOffer cd 4 30\n1 Recv Block ab 20\n',
              'accepted (6 events, 3 sessions)')
        check('sessions notify:client notify:client\n0 Send RequestNext\n1 Recv Votes -\n',
              'rejected at index 2 (session 1)')
        check('sessions fetch:client\n0 Send RequestNext\n', 'parse error')
        check('sessions\n', 'accepted (0 events, 0 sessions)')
        check('sessions client\n0 Send BlockRequest ab 3\n0 Recv Block ab 20\n',
              'accepted (2 events, 1 sessions)')
        check('role client\nSend BlockRequest ab 3\nRecv Block ab 20\n', 'accepted (2 events)', '')
        # A silent stop admits these out-of-order hashes only as a draining client.
        drained = check('role client\nSend BlockRequest a 10\nSend BlockRequest b 11\n'
                        'Recv Block b 100\nRecv Block a 100\nSend Done\n',
                        'accepted (5 events)', '')
        assert drained.splitlines()[0] == 'accepted (5 events)', drained
        assert drained.splitlines()[1] == (
            'note: checked reading fails at index 3: client: block hash mismatch; '
            'accepted only as a draining client'), drained
        assert len(drained.splitlines()) == 2, drained
        # Drain-only reporting keeps each mode's existing first line verbatim.
        drain_cases = [
            ('', 'role client\nSend BlockRequest a 10\nRecv Block b 100\n',
             'accepted (2 events)'),
            ('--interleaved',
             'sessions client\n0 Send BlockRequest a 10\n0 Recv Block b 100\n',
             'accepted (2 events, 1 sessions)'),
        ]
        for mode, contents, first_line in drain_cases:
            output = check(contents, first_line, mode)
            lines = output.splitlines()
            assert lines[0] == first_line, output
            assert len(lines) == 2 and lines[1].startswith('note: checked reading fails'), output
        # This pair rejects by FIFO mismatch (the client receives Block b, the
        # server sent Block a); a paired client drain would not admit it either.
        paired_drain = (
            'pair LeiosFetchP link-AB session-0\n'
            'client node-A c17 generation-0 fresh client.log\n'
            'server node-B c42 generation-3 fresh server.log\n'
            'client 20 Send BlockRequest a 10\nclient 27 Recv Block b 100\n'
            'server 20 Recv BlockRequest a 10\nserver 27 Send Block a 100\n')
        rejected_pair = check(paired_drain, 'rejected paired trace:', '--paired-fetch')
        assert 'note: checked reading fails' not in rejected_pair, rejected_pair
        checked_pair = paired_drain.replace('client 27 Recv Block b 100',
                                            'client 27 Recv Block a 100')
        accepted_pair = check(checked_pair, 'accepted paired prefix', '--paired-fetch')
        assert accepted_pair.splitlines()[0] == (
            'accepted paired prefix (LeiosFetchP retained message fields; client 2 rows, server 2 rows)'), accepted_pair
        assert accepted_pair.splitlines()[1] == 'pair link-AB session-0', accepted_pair
        assert 'note: checked reading fails' not in accepted_pair, accepted_pair
        mixed_drain = check(
            'sessions notify:client fetch:client fetch:client\n'
            '0 Send RequestNext\n1 Send BlockRequest a 10\n'
            '2 Send BlockRequest c 12\n0 Recv Votes -\n'
            '1 Recv Block b 100\n2 Recv Block c 100\n',
            'accepted (6 events, 3 sessions)')
        assert len(mixed_drain.splitlines()) == 2, mixed_drain
        assert '(session 1, local event)' in mixed_drain.splitlines()[1], mixed_drain
        count_drain = check(
            'sessions client\n0 Send BlockTxsRequest a 10 2 0:c000000000000000\n'
            '0 Recv BlockTxs 3 100\n', 'accepted (2 events, 1 sessions)')
        assert count_drain.splitlines()[1].startswith('note: checked reading fails'), count_drain
        assert 'client: reply count mismatch' in count_drain, count_drain
        # Fetch defaults to 150; an explicit depth still overrides it.
        fetch_full = 'role client\n' + 'Send BlockRequest ab 3\n' * 150
        check(fetch_full, 'accepted (150 events)', '')
        rejected = check(fetch_full + 'Send BlockRequest ab 3\n',
                         'rejected at index 151:', '')
        assert rejected.splitlines()[2] == 'reason: wire: pipeline depth exceeded at index 151', rejected
        check('role client\n' + 'Send BlockRequest ab 3\n' * 5,
              'rejected at index 5:', '', (4,))
        check('sessions fetch:client\n' + '0 Send BlockRequest ab 3\n' * 150,
              'accepted (150 events, 1 sessions)')
        txrequest = 'BlockTxsRequest ab 3 2 0:c000000000000000\n'
        check('role client\nSend ' + txrequest + 'Recv BlockTxs 2 80\nSend Done\n',
              'accepted (3 events)', '')
        check('role client\nRecv BlockTxs ab 3 2 80 -\n', 'parse error at line 2:', '')
        rejected = check('role server\nRecv ' + txrequest + 'Send BlockTxs 9 90\n',
                         'rejected at index 2:', '')
        assert rejected.splitlines()[2] == 'reason: client: reply count mismatch at index 2', rejected
        # Independent numeric bounds, including the audited prototype values.
        piped = ('role client\nSend RequestNext\nSend RequestNext\n'
                 'Recv Votes -\nSend RequestNext\nRecv BlockOffer ab 3 20\n'
                 'Recv BlockTxsOffer cd 4\nSend Quit\nRecv Done\n')
        check(piped, 'accepted (8 events, 1 sessions)', '--notify', (2,))
        check(piped, 'rejected at index 2', '--notify', (1,))
        check('role server\nRecv RequestNext\nRecv RequestNext\nSend Votes -\nSend Votes -\nRecv Quit\nSend Done\n',
              'accepted (6 events, 1 sessions)', '--notify', (2,))
        check('role client\nSend RequestNext\n', 'rejected at index 1', '--notify', (0,))
        check('role client\nSend Quit\nRecv Done\n', 'accepted (2 events, 1 sessions)', '--notify', (0,))
        # New shutdown messages, agency and request-credit boundaries.
        check('role client\nSend RequestNext\nRecv Canceled\nSend Quit\nRecv Done\n',
              'accepted (4 events, 1 sessions)', '--notify')
        check('role client\nSend RequestNext\nSend RequestNext\nSend Quit\nRecv Votes -\nRecv Canceled\nRecv Done\n',
              'accepted (6 events, 1 sessions)', '--notify', (2,))
        check('role server\nRecv RequestNext\nRecv RequestNext\nRecv Quit\nSend Canceled\nSend Canceled\nSend Done\n',
              'accepted (6 events, 1 sessions)', '--notify', (2,))
        for events, index in [('Recv Canceled\n', 1),
                              ('Send RequestNext\nSend Quit\nRecv Done\n', 3),
                              ('Send Quit\nSend Quit\n', 2),
                              ('Send RequestNext\nSend Canceled\n', 2),
                              ('Send Done\n', 1)]:
            check('role client\n' + events, f'rejected at index {index}', '--notify', (2,))
        full = 'role client\n' + 'LeiosNotify.Remote.Send.RequestNext\n' * 1000
        check(full, 'accepted (1000 events, 1 sessions)', '--notify', (1000,))
        check(full + 'LeiosNotify.Remote.Send.RequestNext\n', 'rejected at index 1001', '--notify', (1000,))
        mixed = ('sessions notify:client fetch:client\n0 Send RequestNext\n'
                 '0 Send RequestNext\n1 Send BlockRequest ab 3\n1 Send BlockRequest cd 4\n')
        check(mixed, 'accepted (4 events, 2 sessions)', bounds=(150, 1000))
        check(mixed, 'rejected at index 4', bounds=(1, 2))
        check(mixed, 'rejected at index 2', bounds=(150, 1))
        check(mixed, 'rejected at index 2', bounds=(150,))
        for value in ['-1', 'abc']:
            check('role client\n', 'usage:', '--notify', (value,))
            check('sessions\n', 'usage:', bounds=(4, value))
            check('sessions\n', 'usage:', bounds=(value, 2))
        check('sessions\n', 'accepted (0 events, 0 sessions)', bounds=(4, 2, 3))
        check('sessions\n', 'accepted (0 events, 0 sessions)', bounds=(4, 2, 3, 4))
        check('sessions\n', 'accepted (0 events, 0 sessions)', bounds=(4, 2, 3, 4, 5))
        check('sessions\n', 'usage:', bounds=(4, 2, 3, 4, 5, 6))
        raw = root / 'raw.jsonl'
        records = []
        for protocol, suffix, msg in [
            ('LeiosNotify', 'Send.RequestNext', {}),
            ('LeiosFetch', 'Send.BlockRequest', {'ebHash': 'ab', 'ebSlot': 3}),
            ('LeiosNotify', 'Receive.Votes', {'votes': []}),
            ('LeiosNotify', 'Send.Quit', {'kind': 'MsgQuit'}),
            ('LeiosNotify', 'Receive.Done', {'kind': 'MsgDone'}),
            ('LeiosFetch', 'Receive.Block', {'ebHash': 'ab', 'ebBytesSize': 20}),
            ('LeiosNotify', 'Send.RequestNext', {})]:
            records.append({'ns': protocol + '.Remote.' + suffix, 'at': 't',
                            'data': {'peer': {'connectionId': 'a b'}, 'msg': msg}})
        raw.write_text(''.join(json.dumps(r) + '\n' for r in records))
        out = root / 'normalized'
        subprocess.run([sys.executable, '-I', str(Path(__file__).with_name('normalize_logs.py')),
                        str(raw), str(out)], check=True, capture_output=True, text=True)
        check((out / 'interleaved.txt').read_text(), 'accepted (7 events, 3 sessions)')
    print('compiled Notify/Fetch CLI integration tests passed')


if __name__ == '__main__':
    main(sys.argv[1])
