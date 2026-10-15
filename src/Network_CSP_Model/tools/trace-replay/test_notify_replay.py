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
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        def check(contents, expected, mode='--interleaved', bounds=()):
            path = root / 'input.txt'
            path.write_text(contents)
            args = [binary] + ([mode] if mode else []) + [str(path)] + [str(x) for x in bounds]
            result = subprocess.run(args, check=True, capture_output=True, text=True).stdout
            assert result.startswith(expected), (contents, expected, result)
        rounds = ('Send RequestNext\nRecv BlockAnnouncement -\n'
                  'Send RequestNext\nRecv BlockAnnouncement ab 3 20\n'
                  'Send RequestNext\nRecv BlockOffer cd 4 30\n'
                  'Send RequestNext\nRecv BlockTxsOffer ef 5\n'
                  'Send RequestNext\nRecv Votes ab:2,cd:4\nSend Done\n')
        check('role client\n' + rounds, 'accepted (11 events, 1 sessions)', '--notify')
        server = rounds.replace('Send', 'TEMP').replace('Recv', 'Send').replace('TEMP', 'Recv')
        check('role server\n' + server, 'accepted (11 events, 1 sessions)', '--notify')
        for events, index in [('Recv Votes -\n', 1),
                              ('Send RequestNext\nSend RequestNext\n', 2),
                              ('Send RequestNext\nSend Done\n', 2),
                              ('Send Done\nSend RequestNext\n', 2)]:
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
        # Independent numeric bounds, including the audited prototype values.
        piped = ('role client\nSend RequestNext\nSend RequestNext\n'
                 'Recv Votes -\nSend RequestNext\nRecv BlockOffer ab 3 20\n'
                 'Recv BlockTxsOffer cd 4\nSend Done\n')
        check(piped, 'accepted (7 events, 1 sessions)', '--notify', (2,))
        check(piped, 'rejected at index 2', '--notify', (1,))
        check('role server\nRecv RequestNext\nRecv RequestNext\nSend Votes -\nSend Votes -\nRecv Done\n',
              'accepted (5 events, 1 sessions)', '--notify', (2,))
        check('role client\nSend RequestNext\n', 'rejected at index 1', '--notify', (0,))
        check('role client\nSend Done\n', 'accepted (1 events, 1 sessions)', '--notify', (0,))
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
        check('sessions\n', 'usage:', bounds=(4, 2, 3))
        raw = root / 'raw.jsonl'
        records = []
        for protocol, suffix, msg in [
            ('LeiosNotify', 'Send.RequestNext', {}),
            ('LeiosFetch', 'Send.BlockRequest', {'ebHash': 'ab', 'ebSlot': 3}),
            ('LeiosNotify', 'Receive.Votes', {'votes': []}),
            ('LeiosNotify', 'Send.Done', {}),
            ('LeiosFetch', 'Receive.Block', {'ebHash': 'ab', 'ebBytesSize': 20}),
            ('LeiosNotify', 'Send.RequestNext', {})]:
            records.append({'ns': protocol + '.Remote.' + suffix, 'at': 't',
                            'data': {'peer': {'connectionId': 'a b'}, 'msg': msg}})
        raw.write_text(''.join(json.dumps(r) + '\n' for r in records))
        out = root / 'normalized'
        subprocess.run([sys.executable, '-I', str(Path(__file__).with_name('leios_adapter.py')),
                        str(raw), str(out)], check=True, capture_output=True, text=True)
        check((out / 'interleaved.txt').read_text(), 'accepted (6 events, 3 sessions)')
    print('compiled Notify/Fetch CLI integration tests passed')


if __name__ == '__main__':
    main(sys.argv[1])
