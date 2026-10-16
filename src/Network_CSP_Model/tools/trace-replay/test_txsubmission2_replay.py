#!/usr/bin/env python3
"""TxSubmission2 CLI, control evidence, role reversal and adapter regressions."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def adapter_tests(root, binary):
    """Never infer unlogged blocking style or ID-reply emptiness."""
    spec = importlib.util.spec_from_file_location('adapter', Path(__file__).with_name('leiosfetch_adapter.py'))
    a = importlib.util.module_from_spec(spec)
    sys.dont_write_bytecode = True
    spec.loader.exec_module(a)

    def row(suffix, fields=None, wrapped=False, cid='a b'):
        kind = suffix.rsplit('.', 1)[-1]
        msg = {'kind': 'MsgInit' if kind == 'MsgInit' else 'Msg' + kind, **(fields or {})}
        raw = json.dumps({'ns': a.TS + suffix, 'at': 't', 'data': {'peer': {'connectionId': cid}, 'msg': msg}})
        return json.dumps({'message': raw}) if wrapped else raw

    lines = ['irrelevant row', row('Send.MsgInit', wrapped=True),
             row('Receive.RequestTxIds', {'blocking': True}), row('Send.ReplyTxIds', {'txIdCount': 2}),
             row('Receive.RequestTxs'), row('Send.ReplyTxs'),
             row('Receive.RequestTxIds', {'blocking': False}), row('Send.ReplyTxIds', {'txIds': []}),
             row('Receive.RequestTxIds', {'blocking': True}), row('Send.Done'),
             row('Receive.MsgInit'), row('Send.RequestTxIds', {'blocking': False}),
             row('Send.RequestTxs'), row('Receive.ReplyTxIds', {'txIds': ['a'], 'txIdCount': 1}),
             row('Receive.ReplyTxs'), row('Send.RequestTxIds', {'blocking': True}), row('Receive.Done'),
             row('Send.MsgInit')]
    out = root / 'adapted'
    rows = a.split(lines, out, include_txsubmission2=True)
    global_rows = (out / 'interleaved.txt').read_text().splitlines()
    assert global_rows[0] == 'sessions txsubmission2:client txsubmission2:server txsubmission2:client'
    assert [r[6] for r in rows] == ['done', 'done', 'eof']
    assert global_rows[3] == '0 TxSubmission.Remote.Send.ReplyTxIds NonEmpty'
    assert (out / 'interleaved.src').read_text().splitlines()[0] == '2 t 0'
    for i, r in enumerate(rows):
        projected = [x.split(' ', 1)[1] for x in global_rows[1:] if int(x.split()[0]) == i]
        assert (out / f'{r[0]}-{r[7]}-{r[2]}.txt').read_text().splitlines()[1:] == projected
    verdict = subprocess.run([binary, '--interleaved', str(out / 'interleaved.txt'), '1', '1', '1', '1', '2'],
                             check=True, capture_output=True, text=True).stdout
    assert verdict.startswith('accepted (17 events, 3 sessions)'), verdict
    for fields in ({}, {'blocking': 'True'}, {'blocking': 1}, {'blocking': None}):
        try:
            a.split([row('Receive.RequestTxIds', fields)], root / 'bad', include_txsubmission2=True)
        except ValueError as e:
            assert 'line 1' in str(e) and 'blocking' in str(e)
        else:
            raise AssertionError('missing/invalid blocking evidence accepted')
    for fields in ({}, {'txIdCount': -1}, {'txIdCount': True}, {'txIds': '[]'}, {'txIds': [], 'txIdCount': 1}):
        try:
            a.split([row('Send.ReplyTxIds', fields)], root / 'bad', include_txsubmission2=True)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid/missing emptiness evidence accepted')
    try:
        a.split([row('Send.MsgInit', {'kind': 'MsgDone'})], root / 'bad', include_txsubmission2=True)
    except ValueError:
        pass
    else:
        raise AssertionError('contradictory namespace accepted')
    # NewMux ends both roles, without fabricating Done. Dead does not split.
    mux = lambda name: json.dumps({'ns': a.MUX + name, 'at': 't', 'data': {'bearer': {'connectionId': 'a b'}}})
    rows = a.split([row('Send.MsgInit'), row('Receive.MsgInit'), mux('State'), mux('NewMux'), row('Send.MsgInit')],
                   root / 'mux', include_txsubmission2=True)
    assert [r[6] for r in rows] == ['mux', 'mux', 'eof']
    a.split([row('Send.MsgInit'), row('Send.MsgInit')], root / 'repeat', include_txsubmission2=True)
    assert (root / 'repeat/interleaved.txt').read_text().splitlines()[0] == 'sessions txsubmission2:client'
    # The user-facing mixed adapter enables TxSubmission2 and surfaces missing evidence.
    raw = root / 'raw.jsonl'
    raw.write_text('\n'.join(lines) + '\n')
    cli = Path(__file__).with_name('leios_adapter.py')
    proc = subprocess.run([sys.executable, '-I', str(cli), str(raw), str(root / 'cli')], capture_output=True, text=True)
    assert proc.returncode == 0, proc.stderr
    raw.write_text(row('Receive.RequestTxIds') + '\n')
    proc = subprocess.run([sys.executable, '-I', str(cli), str(raw), str(root / 'insufficient')], capture_output=True, text=True)
    assert proc.returncode != 0 and 'requires a logged boolean blocking field' in proc.stderr
    assert 'Traceback' not in proc.stderr
    proc = subprocess.run([sys.executable, '-I', str(cli), str(raw), str(root / 'excluded'),
                           '--exclude-txsubmission2'], capture_output=True, text=True)
    assert proc.returncode == 0, proc.stderr
    assert (root / 'excluded/interleaved.txt').read_text() == 'sessions\n'
    proc = subprocess.run([sys.executable, '-I', str(cli), str(raw), str(root / 'unknown'),
                           '--invent-controls'], capture_output=True, text=True)
    assert proc.returncode != 0


def main(binary):
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        adapter_tests(root, binary)
        path = root / 'input.txt'

        def check(contents, expected, mode='--txsubmission2', bounds=()):
            path.write_text(contents)
            result = subprocess.run([binary, mode, str(path), *map(str, bounds)], check=True, capture_output=True, text=True).stdout
            assert result.startswith(expected), (contents, bounds, result, expected)

        rounds = ('role server\nRecv Init\nSend RequestTxIds NonBlocking\nSend RequestTxs\n'
                  'Recv ReplyTxIds Empty\nRecv ReplyTxs\nSend RequestTxIds Blocking\nRecv Done\n')
        check(rounds, 'accepted (7 events', bounds=(2,))
        check(rounds, 'rejected at index 3', bounds=(1,))
        check('role client\nSend Init\nRecv RequestTxIds Blocking\nSend ReplyTxIds NonEmpty\n'
              'Recv RequestTxs\nSend ReplyTxs\nRecv RequestTxIds Blocking\nSend Done\n',
              'accepted (7 events', bounds=(0,))
        for events, index in [
            ('Send RequestTxs\n', 1), ('Recv Init\nRecv Init\n', 2), ('Send Init\n', 1),
            ('Recv Init\nRecv ReplyTxs\n', 2), ('Recv Init\nRecv Done\n', 2),
            ('Recv Init\nSend RequestTxIds NonBlocking\nRecv Done\n', 3),
            ('Recv Init\nSend RequestTxs\nSend RequestTxIds Blocking\n', 3),
            ('Recv Init\nSend RequestTxIds Blocking\nSend RequestTxs\n', 3),
            ('Recv Init\nSend RequestTxIds Blocking\nRecv ReplyTxIds Empty\n', 3),
            ('Recv Init\nSend RequestTxs\nRecv ReplyTxIds NonEmpty\n', 3),
            ('Recv Init\nSend RequestTxIds NonBlocking\nSend RequestTxs\nRecv ReplyTxs\n', 4),
            ('Recv Init\nSend RequestTxIds Blocking\nRecv Done\nRecv Init\n', 4),
        ]:
            check('role server\n' + events, f'rejected at index {index}', bounds=(2,))
        check('role server\nRecv Init\nSend RequestTxIds Blocking\nRecv Done\n', 'accepted (3 events', bounds=(0,))
        check('role server\nRecv Init\nSend RequestTxs\n', 'rejected at index 2', bounds=(0,))
        check('role server\nRecv Init\n' + 'Send RequestTxs\n' * 4, 'accepted (5 events')
        check('role server\nRecv Init\n' + 'Send RequestTxs\n' * 5, 'rejected at index 6')
        check('role client\nSend Init\nRecv RequestTxs\nRecv RequestTxs\n', 'rejected at index 3', bounds=(100,))
        check('role server\nRecv Init\n' + 'Send RequestTxs\nRecv ReplyTxs\n' * 4,
              'accepted (9 events', bounds=(1,))
        for row in ['Send RequestTxIds', 'Recv ReplyTxIds', 'Send RequestTxIds Unknown',
                    'Recv ReplyTxIds 1', 'Send RequestTxs ab', 'ChainSync.Remote.Send.Done',
                    'TxSubmission.Remote.Send.Init']:
            check('role server\n' + row + '\n', 'parse error at line 2')
        check('role other\n', 'parse error at line 1')
        mixed = ('sessions fetch:client notify:client blockfetch:client chainsync:client txsubmission2:server txsubmission2:client\n'
                 '0 Send BlockRequest ab 1\n1 Send RequestNext\n2 Send RequestRange\n3 Send RequestNext\n'
                 '4 Recv Init\n5 Send Init\n4 Send RequestTxIds NonBlocking\n4 Send RequestTxs\n'
                 '5 Recv RequestTxIds Blocking\n0 Recv Block ab 2\n1 Recv Votes -\n2 Recv NoBlocks\n'
                 '3 Recv RollForward\n4 Recv ReplyTxIds Empty\n4 Recv ReplyTxs\n5 Send Done\n')
        check(mixed, 'accepted (16 events, 6 sessions)', '--interleaved', (1, 1, 1, 1, 2))
        check(mixed, 'rejected at index 8 (session 4)', '--interleaved', (1, 1, 1, 1, 1))
        check(mixed, 'accepted (16 events, 6 sessions)', '--interleaved', (1, 1, 1, 1))
        for index in range(4):
            bounds = [1, 1, 1, 1, 2]
            bounds[index] = 0
            check(mixed, f'rejected at index {index + 1}', '--interleaved', bounds)
        check('sessions txsubmission2:server txsubmission2:server\n0 Recv Init\n1 Recv Init\n0 Send RequestTxs\n1 Recv ReplyTxs\n',
              'rejected at index 4 (session 1)', '--interleaved')
        for bad in ['-1', '1.2', 'abc']:
            check('role server\n', 'usage:', bounds=(bad,))
            check('sessions\n', 'usage:', '--interleaved', (1, 1, 1, 1, bad))
        check('role client\n', 'usage:', bounds=(1, 2))
        check('sessions\n', 'usage:', '--interleaved', (1, 1, 1, 1, 1, 1))
        assert subprocess.run([binary, '--txsubmission2'], capture_output=True, text=True, check=True).stdout.startswith('usage:')
    print('TxSubmission2 CLI, FIFO, role dispatch, mixed sessions and adapter tests passed')


if __name__ == '__main__':
    main(sys.argv[1])
