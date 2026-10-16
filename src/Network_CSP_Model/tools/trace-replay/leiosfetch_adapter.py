#!/usr/bin/env python3
"""Split a cardano-node journal into normalized LeiosFetch session files.

Trace-replay Phase 6 adapter (stdlib only). For mixed Fetch/Notify replay use
leios_adapter.py, which shares this implementation with include_notify=True.
 Input: a raw journal, one
`journalctl` prefix plus one JSON object per line. The log is streamed and
never modified. Output, into OUTDIR (never into the repository):

  sNNNN-<role>.txt   one session in the normalized format parsed by
                     src/Cardano_network/Replay/LeiosFetchParse.agda: a header line
                     `role client|server`, then one event per line
  sNNNN-<role>.src   per event (same order): raw log line number and `at`
  interleaved.txt    `sessions <role> ...`, then `<zero-based id> <event>`
  interleaved.src    raw line number, timestamp and zero-based id per event
  index.tsv          session, connectionId, role, events, first at,
                     last at, end (done | mux | eof)

Session rule. LeiosFetch lines (`LeiosFetch.Remote.{Send,Receive}.*`) are
keyed by `data.peer.connectionId` and by role: client = Send.*Request,
Receive.Block*, Send.Done; server = the converse. A key's stream is cut
  * after a Done (the Done ends its session), and
  * at a mux restart for that connectionId: a `Net.Mux.Remote.NewMux` line
    (key `data.bearer.connectionId`); both roles' open sessions end there.
    `Net.Mux.Remote.State` `Dead` is NOT a cut: in the Phase 6 log 274
    LeiosFetch lines follow a `Dead` on their connectionId with no NewMux in
    between (one connection carries on for 272 events), and `Dead` lines
    outnumber `NewMux` lines (5826 vs 5727), so some belong to other muxes.
Sessions still open at end of log end with `eof`. Events keep file order
(within a connectionId no LeiosFetch line is out of `at` order in the
Phase 6 log). `--no-mux-split` cuts at Done only.

Usage:  python3 -I leiosfetch_adapter.py LOG OUTDIR [--no-mux-split]
        python3 -I leiosfetch_adapter.py --selftest
"""
import json
import os
import re
import sys
import tempfile

LF = 'LeiosFetch.Remote.'
LN = 'LeiosNotify.Remote.'
CS = 'ChainSync.Remote.'
BF = 'BlockFetch.Remote.'
TS = 'TxSubmission.Remote.'
MUX = 'Net.Mux.Remote.'
HEX = re.compile(r'[0-9a-f]+')
BITMAP = re.compile(r'(\d+):0x([0-9a-fA-F]+)')

# namespace suffix -> (role, direction, kind)
KINDS = {
    'Send.BlockRequest':       ('client', 'Send', 'BlockRequest'),
    'Send.BlockTxsRequest':    ('client', 'Send', 'BlockTxsRequest'),
    'Receive.Block':           ('client', 'Recv', 'Block'),
    'Receive.BlockTxs':        ('client', 'Recv', 'BlockTxs'),
    'Send.Done':               ('client', 'Send', 'Done'),
    'Receive.BlockRequest':    ('server', 'Recv', 'BlockRequest'),
    'Receive.BlockTxsRequest': ('server', 'Recv', 'BlockTxsRequest'),
    'Send.Block':              ('server', 'Send', 'Block'),
    'Send.BlockTxs':           ('server', 'Send', 'BlockTxs'),
    'Receive.Done':            ('server', 'Recv', 'Done'),
}


# Prototype Notify agency: RequestNext/Done travel from consumer to producer.
NOTIFY_KINDS = {}
for _name in ('RequestNext', 'NotificationRequestNext', 'Done'):
    _kind = 'RequestNext' if _name != 'Done' else 'Done'
    NOTIFY_KINDS['Send.' + _name] = ('client', 'Send', _kind)
    NOTIFY_KINDS['Receive.' + _name] = ('server', 'Recv', _kind)
for _name in ('BlockAnnouncement', 'BlockOffer', 'BlockTxsOffer', 'Votes'):
    NOTIFY_KINDS['Send.' + _name] = ('server', 'Send', _name)
    NOTIFY_KINDS['Receive.' + _name] = ('client', 'Recv', _name)


# Kind-only control protocols: request agency determines endpoint role.
def control_kinds(requests, replies):
    """Build exact namespace mappings without accepting unknown messages."""
    kinds = {}
    for name in requests:
        kinds['Send.' + name] = ('client', 'Send', name)
        kinds['Receive.' + name] = ('server', 'Recv', name)
    for name in replies:
        kinds['Send.' + name] = ('server', 'Send', name)
        kinds['Receive.' + name] = ('client', 'Recv', name)
    return kinds


CHAIN_SYNC_KINDS = control_kinds(
    ('RequestNext', 'FindIntersect', 'Done'),
    ('AwaitReply', 'RollForward', 'RollBackward',
     'IntersectFound', 'IntersectNotFound'))
BLOCK_FETCH_KINDS = control_kinds(
    ('RequestRange', 'ClientDone'),
    ('StartBatch', 'NoBlocks', 'Block', 'BatchDone'))


# TxSubmission2 reverses the requester/submitter roles used by Fetch.
TX_SUBMISSION_KINDS = {}
for _name in ('MsgInit', 'ReplyTxIds', 'ReplyTxs', 'Done'):
    _kind = 'Init' if _name == 'MsgInit' else _name
    TX_SUBMISSION_KINDS['Send.' + _name] = ('client', 'Send', _kind)
    TX_SUBMISSION_KINDS['Receive.' + _name] = ('server', 'Recv', _kind)
for _name in ('RequestTxIds', 'RequestTxs'):
    TX_SUBMISSION_KINDS['Send.' + _name] = ('server', 'Send', _name)
    TX_SUBMISSION_KINDS['Receive.' + _name] = ('client', 'Recv', _name)


def normalize_txsubmission2(direction, kind, msg):
    """Require the control evidence omitted by the standard node tracer.

    An enriched tracer must supply RequestTxIds.blocking (JSON boolean),
    and ReplyTxIds.txIdCount (natural) or ReplyTxIds.txIds (JSON array).
    Do not reconstruct missing flags or reply shape from later events.
    """
    if not isinstance(msg, dict) or msg.get('kind', 'Msg' + kind) != 'Msg' + kind:
        raise ValueError('TxSubmission2 namespace disagrees with message kind')
    fields = []
    if kind == 'RequestTxIds':
        if type(msg.get('blocking')) is not bool:
            raise ValueError('TxSubmission2 RequestTxIds requires a logged boolean blocking field; standard tracer evidence is insufficient')
        fields = ['Blocking' if msg['blocking'] else 'NonBlocking']
    elif kind == 'ReplyTxIds':
        count = None
        if 'txIds' in msg:
            if not isinstance(msg['txIds'], list):
                raise ValueError('TxSubmission2 txIds must be a JSON array')
            count = len(msg['txIds'])
        if 'txIdCount' in msg:
            n(msg['txIdCount'])
            if count is not None and count != msg['txIdCount']:
                raise ValueError('TxSubmission2 txIdCount disagrees with txIds')
            count = msg['txIdCount']
        if count is None:
            raise ValueError('TxSubmission2 ReplyTxIds requires logged txIdCount or txIds; reply emptiness is unknown')
        fields = ['Empty' if count == 0 else 'NonEmpty']
    return ' '.join([direction, kind] + fields)


def normalize_control(direction, kind, msg):
    """Explicitly erase payloads; reject contradictory logged message kinds."""
    if not isinstance(msg, dict) or msg.get('kind', 'Msg' + kind) != 'Msg' + kind:
        raise ValueError('control namespace disagrees with message kind')
    return direction + ' ' + kind


def h(x):
    """An ebHash as lowercase hex (rejects anything else)."""
    x = x.lower()
    if not HEX.fullmatch(x):
        raise ValueError('bad ebHash %r' % x)
    return x


def n(x):
    """A natural number field."""
    if not isinstance(x, int) or isinstance(x, bool) or x < 0:
        raise ValueError('bad number %r' % x)
    return str(x)


def bm(xs):
    """Bitmaps `["i:0xw", ...]` as `i:w,...` (or `-` when empty)."""
    out = []
    for x in xs:
        m = BITMAP.fullmatch(x)
        if not m:
            raise ValueError('bad bitmap %r' % x)
        out.append('%s:%s' % (m.group(1), m.group(2).lower()))
    return ','.join(out) or '-'


def normalize(direction, kind, m):
    """One normalized event line from the tracer's `msg` object."""
    f = {
        'BlockRequest':    lambda: [h(m['ebHash']), n(m['ebSlot'])],
        'Block':           lambda: [h(m['ebHash']), n(m['ebBytesSize'])],
        'BlockTxsRequest': lambda: [h(m['ebHash']), n(m['ebSlot']),
                                    n(m['numTxs']), bm(m['bitmaps'])],
        'BlockTxs':        lambda: [h(m['ebHash']), n(m['ebSlot']),
                                    n(m['numTxs']), n(m['txsBytesSize']),
                                    bm(m['bitmaps'])],
        'Done':            lambda: [],
    }[kind]
    return ' '.join([direction, kind] + f())


def normalize_notify(direction, kind, m):
    """Prototype fields from LeiosDemoTypes.messageLeiosNotifyToObject.

    Preserve logged data but do not manufacture RequestNext records. The strict
    peer checker requires those records, even if a tracer configuration omits them.
    """
    expected = 'MsgLeiosNotificationRequestNext' if kind == 'RequestNext' else (
        'MsgDone' if kind == 'Done' else 'MsgLeios' + kind)
    if m.get('kind', expected) != expected:
        raise ValueError('Notify namespace disagrees with message kind')
    if kind in ('RequestNext', 'Done'):
        fields = []
    elif kind == 'BlockAnnouncement':
        names = ('ebHash', 'ebSlot', 'ebBodySize')
        if not any(name in m for name in names):
            fields = ['-']
        else:
            fields = [h(m['ebHash']), n(m['ebSlot']), n(m['ebBodySize'])]
    elif kind == 'BlockOffer':
        fields = [h(m['ebHash']), n(m['ebSlot']), n(m['ebBytesSize'])]
    elif kind == 'BlockTxsOffer':
        fields = [h(m['ebHash']), n(m['ebSlot'])]
    elif kind == 'Votes':
        if not isinstance(m['votes'], list):
            raise ValueError('votes must be a list')
        fields = [','.join(h(v['rbHash']) + ':' + n(v['voterId'])
                           for v in m['votes']) or '-']
    else:
        raise ValueError('unknown Notify kind %r' % kind)
    return ' '.join([direction, kind] + fields)


def split(lines, outdir, mux_split=True, include_notify=False, include_control=False, include_txsubmission2=False):
    """Stream `lines` and write the session files and index into `outdir`.
    With include_notify, include Notify. With include_control, include control-only
    ChainSync and BlockFetch. include_txsubmission2 requires enriched control
    evidence. Any protocol option enables protocol-tagged output.
    Returns the index rows."""
    mixed = include_notify or include_control or include_txsubmission2
    os.makedirs(outdir, exist_ok=True)
    open_ = {}   # (cid, role, protocol) -> session generation
    rows = []
    counter = [0]
    session_roles = []
    interleaved = []  # original file order, including separate generations

    def close(key, end):
        s = open_.pop(key, None)
        if s is None:
            return
        suffix = '%s-%s' % (key[2], key[1]) if mixed else key[1]
        base = os.path.join(outdir, '%s-%s' % (s['id'], suffix))
        with open(base + '.txt', 'w') as fh:
            fh.write('role %s\n' % key[1])
            fh.writelines(e + '\n' for e in s['events'])
        with open(base + '.src', 'w') as fh:
            fh.writelines('%d %s\n' % src for src in s['src'])
        rows.append((s['id'], key[0], key[1], len(s['events']),
                     s['src'][0][1], s['src'][-1][1], end) +
                    ((key[2],) if mixed else ()))

    for lineno, line in enumerate(lines, 1):
        i = line.find('{')
        if i < 0 or (LF not in line and MUX not in line and
                     (not include_notify or LN not in line) and
                     (not include_control or (CS not in line and BF not in line)) and
                     (not include_txsubmission2 or TS not in line)):   # cheap pre-filter
            continue
        o = json.loads(line[i:])
        # Local devnet supervisors wrap the node JSON in a message string.
        # Keep the outer line number as the source-map coordinate.
        if 'ns' not in o and isinstance(o.get('message'), str):
            nested = o['message']
            if not nested.startswith('{'):
                continue
            o = json.loads(nested)
        if 'ns' not in o:
            continue
        ns, d = o['ns'], o['data']
        if ns.startswith(MUX):
            if mux_split and ns == MUX + 'NewMux':
                cid = d['bearer']['connectionId']
                for key in list(open_):
                    if key[0] == cid:
                        close(key, 'mux')
            continue
        if ns.startswith(LF):
            protocol, prefix, kinds, normalizer = 'fetch', LF, KINDS, normalize
        elif include_notify and ns.startswith(LN):
            protocol, prefix, kinds, normalizer = 'notify', LN, NOTIFY_KINDS, normalize_notify
        elif include_txsubmission2 and ns.startswith(TS):
            protocol, prefix, kinds, normalizer = 'txsubmission2', TS, TX_SUBMISSION_KINDS, normalize_txsubmission2
        elif include_control and ns.startswith(CS):
            protocol, prefix, kinds, normalizer = 'chainsync', CS, CHAIN_SYNC_KINDS, normalize_control
        elif include_control and ns.startswith(BF):
            protocol, prefix, kinds, normalizer = 'blockfetch', BF, BLOCK_FETCH_KINDS, normalize_control
        else:
            continue
        # Serialised tracers are separate observations, not wire-message rows.
        if ns.startswith(prefix + 'Serialised.'):
            continue
        suffix = ns[len(prefix):]
        if suffix not in kinds:
            raise ValueError('line %d: unknown %s namespace %s' % (lineno, protocol, ns))
        role, direction, kind = kinds[suffix]
        try:
            key = (d['peer']['connectionId'], role, protocol)
            ev = normalizer(direction, kind, d['msg'])
            if mixed:
                # Keep the exact tracer namespace on each row, including aliases.
                payload = ev.split(' ', 2)
                ev = ns + (' ' + payload[2] if len(payload) == 3 else '')
        except (KeyError, ValueError, TypeError, AttributeError) as err:
            raise ValueError('line %d: %s' % (lineno, err))
        if key not in open_:
            counter[0] += 1
            open_[key] = {'id': 's%04d' % counter[0], 'tag': counter[0] - 1,
                          'events': [], 'src': []}
            session_roles.append(protocol + ':' + role if mixed else role)
        interleaved.append((open_[key]['tag'], ev, lineno, o['at']))
        open_[key]['events'].append(ev)
        open_[key]['src'].append((lineno, o['at']))
        if kind in ('Done', 'ClientDone'):
            close(key, 'done')
    for key in list(open_):
        close(key, 'eof')

    with open(os.path.join(outdir, 'interleaved.txt'), 'w') as fh:
        fh.write('sessions' + (' ' + ' '.join(session_roles) if session_roles else '') + '\n')
        fh.writelines('%d %s\n' % (tag, ev) for tag, ev, _, _ in interleaved)
    with open(os.path.join(outdir, 'interleaved.src'), 'w') as fh:
        fh.writelines('%d %s %d\n' % (line, at, tag)
                      for tag, _, line, at in interleaved)

    rows.sort()
    with open(os.path.join(outdir, 'index.tsv'), 'w') as fh:
        fh.write('session\tconnectionId\trole\tevents\tfirst_at\tlast_at\tend' +
                 ('\tprotocol' if mixed else '') + '\n')
        fh.writelines('\t'.join(map(str, r)) + '\n' for r in rows)
    return rows


def selftest():
    """Split a few embedded lines and check the files."""
    pre = '2026-09-27T14:00:00+00:00 host cardano-node-start[1]: '
    cid = '10.0.0.1:3001 10.0.0.2:3001'
    hh = 'ab' * 32

    def lf(at, ns, msg, connection=cid):
        return pre + json.dumps({'at': at, 'ns': LF + ns, 'data': {
            'msg': msg, 'peer': {'connectionId': connection}}})

    def mux(at, ns, ev):
        return pre + json.dumps({'at': at, 'ns': MUX + ns, 'data': {
            'bearer': {'connectionId': cid}, 'event': ev}})

    lines = [
        'not json at all',
        lf('t1', 'Send.BlockRequest', {'ebHash': hh, 'ebSlot': 5}),
        lf('t2', 'Receive.BlockRequest', {'ebHash': hh, 'ebSlot': 5}),
        mux('t3', 'State', {'state': 'Dead'}),
        mux('t4', 'NewMux', {}),
        lf('t5', 'Send.BlockTxsRequest', {'ebHash': hh.upper(), 'ebSlot': 5,
                                          'numTxs': 2, 'bitmaps': ['0:0xFF', '3:0x01']}),
        mux('t5b', 'State', {'state': 'Dead'}),          # not a cut
        lf('t6', 'Receive.BlockTxs', {'ebHash': hh, 'ebSlot': 5, 'numTxs': 2,
                                      'txsBytesSize': 9, 'bitmaps': []}),
        lf('t7', 'Send.Done', {'kind': 'MsgDone'}),
        lf('t8', 'Send.Block', {'ebHash': hh, 'ebBytesSize': 7}),
    ]
    with tempfile.TemporaryDirectory() as tmp:
        rows = split(lines, tmp)
        assert [r[0] + r[2] + r[6] for r in rows] == \
            ['s0001clientmux', 's0002servermux', 's0003clientdone', 's0004servereof'], rows
        read = lambda f: open(os.path.join(tmp, f)).read()
        assert read('s0003-client.txt') == (
            'role client\n'
            'Send BlockTxsRequest %s 5 2 0:ff,3:01\n'
            'Recv BlockTxs %s 5 2 9 -\n'
            'Send Done\n') % (hh, hh), read('s0003-client.txt')
        assert read('s0004-server.txt') == 'role server\nSend Block %s 7\n' % hh
        assert read('s0003-client.src') == '6 t5\n8 t6\n9 t7\n'
        global_lines = read('interleaved.txt').splitlines()
        assert global_lines[0] == 'sessions client server client server'
        assert [int(e.split()[0]) for e in global_lines[1:]] == [0, 1, 2, 2, 2, 3]
        assert [int(e.split()[0]) for e in read('interleaved.src').splitlines()] == [2, 3, 6, 8, 9, 10]
        # Every projection is exactly the previously produced session file.
        for i, row in enumerate(rows):
            local = read('%s-%s.txt' % (row[0], row[2])).splitlines()[1:]
            projection = [e.split(' ', 1)[1] for e in global_lines[1:]
                          if int(e.split()[0]) == i]
            assert projection == local
        # A post-Done event creates a new generation of the same role/key.
        done_lines = [lf('z1', 'Send.Done', {}), lf('z2', 'Send.Done', {})]
        split(done_lines, os.path.join(tmp, 'done'))
        assert read('done/interleaved.txt') == 'sessions client client\n0 Send Done\n1 Send Done\n'
        split([], os.path.join(tmp, 'empty'))
        assert read('empty/interleaved.txt') == 'sessions\n'
        # Distinct connections keep separate state and preserve interleaving.
        other = '10.0.0.1:3001 10.0.0.3:3001'
        peers = [lf('p1', 'Send.BlockRequest', {'ebHash': hh, 'ebSlot': 5}),
                 lf('p2', 'Send.Done', {}, other),
                 lf('p3', 'Receive.Block', {'ebHash': hh, 'ebBytesSize': 7})]
        split(peers, os.path.join(tmp, 'peers'))
        assert read('peers/interleaved.txt').splitlines() == [
            'sessions client client', '0 Send BlockRequest %s 5' % hh,
            '1 Send Done', '0 Recv Block %s 7' % hh]
        rows = split(lines, os.path.join(tmp, 'nomux'), mux_split=False)
        assert [r[3] for r in rows] == [4, 2], rows
    print('selftest ok')


if __name__ == '__main__':
    args = sys.argv[1:]
    if args == ['--selftest']:
        selftest()
    elif len(args) in (2, 3) and args[2:] in ([], ['--no-mux-split']):
        with open(args[0], encoding='utf-8') as log:
            rows = split(log, args[1], mux_split=not args[2:])
        print('%d sessions written to %s' % (len(rows), args[1]))
    else:
        sys.exit(__doc__)
