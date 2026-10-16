#!/usr/bin/env python3
"""Compiled CLI and raw adapter regressions for ChainSync control replay."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def adapter_tests(root):
    """Preserve namespaces, original row numbers, roles and generations."""
    spec = importlib.util.spec_from_file_location(
        'adapter', Path(__file__).with_name('leiosfetch_adapter.py'))
    adapter = importlib.util.module_from_spec(spec)
    sys.dont_write_bytecode = True
    spec.loader.exec_module(adapter)

    def row(ns, kind=None, wrap=False, cid='a b'):
        data = {'bearer': {'connectionId': cid}} if ns.startswith(adapter.MUX) else {
            'peer': {'connectionId': cid}, 'msg': {'kind': kind or 'Msg' + ns.rsplit('.', 1)[-1]}}
        raw = json.dumps({'ns': ns, 'at': 't', 'data': data})
        return json.dumps({'message': raw, 'process': 'Node1'}) if wrap else raw

    lines = [
        'unrelated line',
        row(adapter.CS + 'Send.RequestNext', wrap=True),
        row(adapter.LN + 'Send.RequestNext', 'MsgLeiosNotificationRequestNext'),
        row(adapter.CS + 'Receive.AwaitReply'),
        row(adapter.CS + 'Receive.RequestNext'),
        row(adapter.CS + 'Send.RollBackward'),
        row(adapter.BF + 'Send.RequestRange'),
        row(adapter.CS + 'Receive.RollForward', wrap=True),
        row(adapter.CS + 'Send.Done'),
        row(adapter.BF + 'Receive.NoBlocks'),
        row(adapter.BF + 'Send.ClientDone'),
        row(adapter.CS + 'Send.FindIntersect'),
        row(adapter.MUX + 'State'),
        row(adapter.CS + 'Receive.IntersectNotFound'),
        row(adapter.MUX + 'NewMux'),
        row(adapter.CS + 'Send.Done'),
        row(adapter.CS + 'Send.Done', cid='c d'),
    ]
    out = root / 'adapted'
    rows = adapter.split(lines, out, include_notify=True, include_control=True)
    global_rows = (out / 'interleaved.txt').read_text().splitlines()
    assert global_rows[0] == ('sessions chainsync:client notify:client chainsync:server '
                              'blockfetch:client chainsync:client chainsync:client chainsync:client')
    assert [r[6] for r in rows] == ['done', 'mux', 'mux', 'done', 'mux', 'done', 'done']
    assert (out / 'interleaved.src').read_text().splitlines()[0] == '2 t 0'
    assert len(global_rows) == 15
    for i, r in enumerate(rows):
        local = (out / f'{r[0]}-{r[7]}-{r[2]}.txt').read_text().splitlines()[1:]
        projection = [l.split(' ', 1)[1] for l in global_rows[1:] if int(l.split()[0]) == i]
        assert local == projection
    # Missing requests stay absent rather than being repaired.
    adapter.split([row(adapter.CS + 'Receive.RollForward')], root / 'missing', include_control=True)
    assert (root / 'missing/interleaved.txt').read_text() == (
        'sessions chainsync:client\n0 ChainSync.Remote.Receive.RollForward\n')
    for bad in [row(adapter.CS + 'Send.RequestNext', 'MsgDone'),
                row(adapter.CS + 'Send.Unknown')]:
        try:
            adapter.split([bad], root / 'bad', include_control=True)
        except ValueError:
            pass
        else:
            raise AssertionError('malformed control event accepted')
    # No duplicated observations from the separate serialised tracer.
    adapter.split([row(adapter.CS + 'Serialised.Send.RequestNext')], root / 'serial', include_control=True)
    assert (root / 'serial/interleaved.txt').read_text() == 'sessions\n'
    adapter.split(lines, root / 'nosplit', mux_split=False, include_notify=True, include_control=True)
    assert '\tmux\t' not in (root / 'nosplit/index.tsv').read_text()


def main(binary):
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        adapter_tests(root)
        path = root / 'input.txt'

        def check(contents, expected, mode='--chainsync', bounds=()):
            path.write_text(contents)
            actual = subprocess.run([binary, mode, str(path), *map(str, bounds)],
                                    check=True, capture_output=True, text=True).stdout
            assert actual.startswith(expected), (contents, bounds, actual, expected)

        def client(events, expected, k=2):
            check('role client\n' + events, expected, bounds=(k,))

        trace = ('Send RequestNext\nRecv AwaitReply\nSend RequestNext\n'
                 'Recv RollForward\nRecv AwaitReply\nRecv RollBackward\n'
                 'Send FindIntersect\nRecv IntersectFound\nSend Done\n')
        client(trace, 'accepted (9 events', 2)
        client(trace, 'rejected at index 3', 1)
        client('Send RequestNext\nRecv AwaitReply\n', 'accepted (2 events', 1)
        client('Send FindIntersect\n', 'accepted (1 events', 0)
        client('Send Done\n', 'accepted (1 events', 0)
        client('Send RequestNext\n', 'rejected at index 1', 0)
        for events, index in [
            ('Recv RollForward\n', 1), ('Recv AwaitReply\n', 1),
            ('Recv IntersectFound\n', 1), ('Recv RequestNext\n', 1),
            ('Send RequestNext\nRecv AwaitReply\nRecv AwaitReply\n', 3),
            ('Send RequestNext\nSend FindIntersect\n', 2),
            ('Send RequestNext\nSend Done\n', 2),
            ('Send FindIntersect\nSend RequestNext\n', 2),
            ('Send FindIntersect\nRecv AwaitReply\n', 2),
            ('Send RequestNext\nRecv IntersectNotFound\n', 2),
            ('Send Done\nSend Done\n', 2),
        ]:
            client(events, f'rejected at index {index}')
        client('Send RequestNext\nRecv RollForward\n' * 4 + 'Send Done\n', 'accepted (9 events', 1)
        server = ('role server\nRecv FindIntersect\nSend IntersectNotFound\n'
                  'Recv RequestNext\nSend AwaitReply\nSend RollForward\n'
                  'Recv RequestNext\nSend RollBackward\nRecv Done\n')
        check(server, 'accepted (8 events', bounds=(0,))
        check('role server\nRecv RequestNext\nRecv RequestNext\n', 'rejected at index 2', bounds=(300,))
        check('role server\nRecv RequestNext\nSend AwaitReply\nSend AwaitReply\n', 'rejected at index 3')
        client('ChainSync.Remote.Send.FindIntersect\nChainSync.Remote.Receive.IntersectFound\n', 'accepted (2 events')
        for event in ['LeiosNotify.Remote.Send.RequestNext', 'BlockFetch.Remote.Send.Done',
                      'Send RequestNext extra', 'Recv RollForward ab', 'Send MsgRequestNext']:
            client(event + '\n', 'parse error at line 2')
        check('role other\n', 'parse error at line 1')
        check('role client\n' + 'Send RequestNext\n' * 300, 'accepted (300 events')
        check('role client\n' + 'Send RequestNext\n' * 301, 'rejected at index 301')
        mixed = ('sessions chainsync:client chainsync:server fetch:client notify:server blockfetch:client\n'
                 '0 Send RequestNext\n1 Recv FindIntersect\n2 Send BlockRequest ab 1\n'
                 '3 Recv RequestNext\n4 Send RequestRange\n0 Send RequestNext\n'
                 '1 Send IntersectFound\n0 Recv AwaitReply\n2 Recv Block ab 3\n'
                 '4 Recv NoBlocks\n3 Send Votes -\n0 Recv RollForward\n0 Recv RollBackward\n')
        check(mixed, 'accepted (13 events, 5 sessions)', '--interleaved', (1, 1, 1, 2))
        check(mixed, 'rejected at index 6 (session 0)', '--interleaved', (1, 1, 1, 1))
        check(mixed, 'accepted (13 events, 5 sessions)', '--interleaved', (1, 1, 1))
        for bounds, index in [((0, 1, 1, 2), 3), ((1, 0, 1, 2), 4), ((1, 1, 0, 2), 5), ((1, 1, 1, 0), 1)]:
            check(mixed, f'rejected at index {index}', '--interleaved', bounds)
        check('sessions chainsync:client chainsync:client\n0 Send RequestNext\n1 Recv RollForward\n',
              'rejected at index 2 (session 1)', '--interleaved')
        check('sessions chainsync:client chainsync:client\n0 Send Done\n1 Send RequestNext\n',
              'accepted (2 events, 2 sessions)', '--interleaved')
        check('sessions chainsync:client\n1 Send Done\n', 'parse error at line 2', '--interleaved')
        for bad in ['-1', 'no', '1.2']:
            check('role client\n', 'usage:', bounds=(bad,))
            check('sessions\n', 'usage:', '--interleaved', (1, 1, 1, bad))
        check('role client\n', 'usage:', bounds=(1, 2))
        check('sessions\n', 'accepted (0 events, 0 sessions)', '--interleaved', (1, 1, 1, 1, 1))
        check('sessions\n', 'usage:', '--interleaved', (1, 1, 1, 1, 1, 1))
        assert subprocess.run([binary, '--chainsync'], check=True, capture_output=True, text=True).stdout.startswith('usage:')
    print('ChainSync CLI, mixed-session and raw adapter tests passed')


if __name__ == '__main__':
    main(sys.argv[1])
