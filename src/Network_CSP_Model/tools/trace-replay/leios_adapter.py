#!/usr/bin/env python3
"""Normalize prototype LeiosFetch/LeiosNotify logs into one interleaved stream.

Usage: python3 -I leios_adapter.py LOG OUTDIR [--no-mux-split]
       python3 -I leios_adapter.py --selftest

Writes interleaved.txt with fetch:client/server and notify:client/server entries,
interleaved.src, original tracer namespaces on event rows, protocol-qualified per-session files and index.tsv (including
protocol). Sessions are grouped by connection/protocol/role; Done ends only that
session, NewMux ends all open sessions on the connection, and Dead does not cut.
No RequestNext is synthesized. Logs omitting Notify requests are not complete
inputs to the strict LeiosNotifyP wire-order checker.
"""
import importlib.util
from pathlib import Path
import sys

# Load the sibling explicitly so the entry point also works with Python -I.
_spec = importlib.util.spec_from_file_location(
    'leiosfetch_adapter', Path(__file__).with_name('leiosfetch_adapter.py'))
adapter = importlib.util.module_from_spec(_spec)
sys.dont_write_bytecode = True
_spec.loader.exec_module(adapter)


def selftest():
    """Exercise all Notify shapes and mixed-protocol lifecycle isolation."""
    import json
    import tempfile
    adapter.selftest()
    cid = 'local remote'
    def line(ns, msg=None):
        data = {'bearer': {'connectionId': cid}} if ns.startswith(adapter.MUX) else {
            'peer': {'connectionId': cid}, 'msg': msg}
        return json.dumps({'ns': ns, 'at': 't', 'data': data})
    def ln(suffix, msg):
        return line(adapter.LN + suffix, msg)
    assert adapter.normalize_notify('Recv', 'BlockAnnouncement', {}) == 'Recv BlockAnnouncement -'
    assert adapter.normalize_notify('Recv', 'BlockAnnouncement', {
        'ebHash': 'AB', 'ebSlot': 3, 'ebBodySize': 20}) == 'Recv BlockAnnouncement ab 3 20'
    assert adapter.normalize_notify('Send', 'Votes', {'votes': [
        {'rbHash': 'AB', 'voterId': 2}, {'rbHash': 'CD', 'voterId': 4}]}) == 'Send Votes ab:2,cd:4'
    assert adapter.normalize_notify('Send', 'Votes', {'votes': []}) == 'Send Votes -'
    for kind, msg in [('BlockAnnouncement', {'ebHash': 'ab'}),
                      ('Votes', {'votes': {}}),
                      ('Votes', {'votes': [{'rbHash': 'ab', 'voterId': -1}]}),
                      ('RequestNext', {'kind': 'MsgDone'})]:
        try:
            adapter.normalize_notify('Send', kind, msg)
        except (ValueError, KeyError):
            pass
        else:
            raise AssertionError((kind, msg))
    lines = [
        ln('Send.RequestNext', {}),
        line(adapter.LF + 'Send.BlockRequest', {'ebHash': 'ab', 'ebSlot': 3}),
        ln('Receive.BlockOffer', {'ebHash': 'ab', 'ebSlot': 3, 'ebBytesSize': 20}),
        ln('Send.Done', {}),
        line(adapter.LF + 'Receive.Block', {'ebHash': 'ab', 'ebBytesSize': 20}),
        ln('Send.NotificationRequestNext', {}),
        ln('Receive.BlockTxsOffer', {'ebHash': 'ab', 'ebSlot': 3}),
        ln('Receive.RequestNext', {}),
        line(adapter.MUX + 'State', {'state': 'Dead'}),
        ln('Send.Votes', {'votes': []}),
        line(adapter.MUX + 'NewMux'),
        ln('Send.RequestNext', {}),
    ]
    with tempfile.TemporaryDirectory() as tmp:
        rows = adapter.split(lines, tmp, include_notify=True)
        root = Path(tmp)
        text = (root / 'interleaved.txt').read_text().splitlines()
        assert text[0] == 'sessions notify:client fetch:client notify:client notify:server notify:client'
        assert text[1] == '0 LeiosNotify.Remote.Send.RequestNext'
        assert text[2] == '1 LeiosFetch.Remote.Send.BlockRequest ab 3'
        assert text[6] == '2 LeiosNotify.Remote.Send.NotificationRequestNext'
        assert [int(e.split()[0]) for e in text[1:]] == [0, 1, 0, 0, 1, 2, 2, 3, 3, 4]
        assert [r[6] for r in rows] == ['done', 'mux', 'mux', 'mux', 'eof']
        assert (root / 'index.tsv').read_text().splitlines()[0].endswith('\tprotocol')
        for tag, row in enumerate(rows):
            path = root / ('%s-%s-%s.txt' % (row[0], row[7], row[2]))
            projection = [e.split(' ', 1)[1] for e in text[1:] if int(e.split()[0]) == tag]
            assert path.read_text().splitlines()[1:] == projection
        assert len((root / 'interleaved.src').read_text().splitlines()) == 10
        # Missing requests stay missing; the adapter never repairs trace evidence.
        adapter.split([ln('Receive.BlockAnnouncement', {})], root / 'missing', include_notify=True)
        assert (root / 'missing/interleaved.txt').read_text() == 'sessions notify:client\n0 LeiosNotify.Remote.Receive.BlockAnnouncement -\n'
    print('mixed Notify/Fetch selftest ok')


if __name__ == '__main__':
    args = sys.argv[1:]
    if args == ['--selftest']:
        selftest()
    elif len(args) in (2, 3) and args[2:] in ([], ['--no-mux-split']):
        with open(args[0], encoding='utf-8') as log:
            rows = adapter.split(log, args[1], mux_split=not args[2:], include_notify=True)
        print('%d sessions written to %s' % (len(rows), args[1]))
    else:
        sys.exit(__doc__)
