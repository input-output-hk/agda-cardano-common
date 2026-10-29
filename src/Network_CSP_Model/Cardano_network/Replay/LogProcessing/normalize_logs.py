#!/usr/bin/env python3
"""Normalize captured mini-protocol logs into replay sessions and source maps.

By default, include LeiosFetchP, LeiosNotifyP, BlockFetch, ChainSync and
TxSubmission2 in one protocol-tagged interleaved stream. --fetch-only retains
only LeiosFetch and uses the original role-only session format and filenames.

Reads raw node JSON, journal-prefixed JSON and supervisor JSON wrappers in file
order. Writes session .txt/.src files, interleaved.txt, interleaved.src and
index.tsv into OUTDIR, which must be new or empty and is populated only when the
whole log normalizes; a protocol row that cannot be read is a line-numbered error,
never skipped. Sessions are keyed by connection, protocol and role; Done closes
that session and NewMux closes the connection's open sessions by default.
For devnet captures without NewMux, --connection-lifecycle instead uses successful
handshakes and matching handler cleanups. It requires handler/wire thread IDs,
rejects ambiguous generations, and writes connections.tsv plus generation columns
in index.tsv. Mux Dead and exception messages alone never create generations.
EOF is a prefix boundary, not evidence of successful completion.

BlockFetch, ChainSync and TxSubmission2 retain control observations only.
TxSubmission2 requires enriched blocking/reply-emptiness evidence; use
--exclude-txsubmission2 to omit it explicitly if the capture lacks those fields.
No missing protocol events or control fields are fabricated.

Run with --help for options, or --selftest for embedded regression checks.
"""
import argparse
import json
import ipaddress
from pathlib import Path
import os
import re
import shutil
import sys
import tempfile

LF = 'LeiosFetch.Remote.'
LN = 'LeiosNotify.Remote.'
CS = 'ChainSync.Remote.'
BF = 'BlockFetch.Remote.'
TS = 'TxSubmission.Remote.'
MUX = 'Net.Mux.Remote.'
CONNECTION = 'Net.ConnectionManager.Remote.'
HANDSHAKE = CONNECTION + 'ConnectionHandler.HandshakeSuccess'
CLEANUP = CONNECTION + 'ConnectionCleanup'
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


def connection_id(value):
    """Match structured lifecycle socket addresses to textual wire connection IDs."""
    def endpoint(address, port):
        if not isinstance(address, str) or not address or isinstance(port, bool):
            raise ValueError('connection address and port are required')
        if not isinstance(port, (str, int)) or not str(port).isdigit() or not 0 <= int(port) <= 65535:
            raise ValueError('connection port must be between 0 and 65535')
        host = address
        if host.startswith('[') and host.endswith(']'):
            host = host[1:-1]
        if '[' in host or ']' in host:
            raise ValueError('malformed brackets in connection address')
        try:
            host = str(ipaddress.ip_address(host))
        except ValueError:
            if not re.fullmatch(r'[A-Za-z0-9_.-]+', host):
                raise ValueError('unsupported connection address %r' % address)
        return ('[' + host + ']' if ':' in host else host) + ':' + str(int(port))

    if isinstance(value, str):
        pair = value.split()
        if len(pair) != 2 or any(':' not in part for part in pair):
            raise ValueError('connectionId must contain local and remote socket addresses')
        return ' '.join(endpoint(*part.rsplit(':', 1)) for part in pair)
    if isinstance(value, dict):
        ends = []
        for name in ('localAddress', 'remoteAddress'):
            address = value[name]
            ends.append(endpoint(address.get('address', address.get('addr')), address['port']))
        return ' '.join(ends)
    raise ValueError('unsupported connectionId format')


def thread_id(record):
    """Require an observable thread identity instead of guessing a connection epoch."""
    value = record.get('thread')
    if isinstance(value, bool) or not isinstance(value, (str, int)) or not str(value).strip():
        raise ValueError('connection-lifecycle mode requires handler and wire thread IDs')
    return str(value).strip()


class ConnectionLifecycle:
    """Use successful handshakes and matching handler cleanups as explicit generations.

    Requires ordered, single-process capture evidence. Handler threads identify
    lifecycle instances; observed mini-protocol threads bind wire rows to them.
    Neither protocol contents nor mux errors create a generation.
    """
    def __init__(self):
        self.current = {}
        self.wire_threads = {}
        self.records = []

    def observe(self, record, line):
        """Return the address pair to close only for its matching live cleanup."""
        cid = connection_id(record['data']['connectionId'])
        handler = thread_id(record)
        previous = self.current.get(cid)
        if record['ns'] == HANDSHAKE:
            if previous and previous['handlerThread'] == handler:
                if previous['cleanupLine']:
                    raise ValueError('handshake reuses a cleaned-up handler thread for %s' % cid)
                return None  # A duplicate notification is not a new generation.
            if previous and not previous['cleanupLine']:
                raise ValueError('ambiguous overlapping connection generations for %s: '
                                 'new handshake before cleanup of handler %s' % (cid, previous['handlerThread']))
            generation = previous['generation'] + 1 if previous else 0
            info = dict(connectionId=cid, generation=generation, handlerThread=handler,
                        handshakeLine=line, handshakeAt=record['at'], cleanupLine='', cleanupAt='')
            self.current[cid] = info
            self.records.append(info)
        elif previous and previous['handlerThread'] == handler and not previous['cleanupLine']:
            previous['cleanupLine'] = line
            previous['cleanupAt'] = record['at']
            return cid
        return None  # Unobserved/old handler cleanups cannot close a newer instance.

    def wire(self, record, cid, role, protocol):
        """Bind each wire actor to one live generation and reject known stale actors."""
        current = self.current.get(cid)
        if current is None:
            raise ValueError('wire event for %s has no preceding successful handshake' % cid)
        if current['cleanupLine']:
            raise ValueError('wire event for %s follows connection cleanup without a new handshake' % cid)
        actor = (cid, role, protocol, thread_id(record))
        generation = current['generation']
        if actor in self.wire_threads and self.wire_threads[actor] != generation:
            raise ValueError('wire thread %s belongs to an earlier generation of %s' % (actor[-1], cid))
        self.wire_threads[actor] = generation
        return current

    def write(self, outdir):
        """Retain the raw lifecycle coordinates used for every inferred generation."""
        fields = ('connectionId', 'generation', 'handlerThread', 'handshakeLine',
                  'handshakeAt', 'cleanupLine', 'cleanupAt')
        with open(os.path.join(outdir, 'connections.tsv'), 'w') as stream:
            stream.write('\t'.join(fields) + '\n')
            for record in self.records:
                stream.write('\t'.join(str(record[field]) for field in fields) + '\n')


def split(lines, outdir, **options):
    """Normalize into a fresh sibling directory and publish it as `outdir` only on success.

    Refuses an existing non-empty `outdir`, so two runs are never mixed and a
    failing run leaves no partial output. See `split_into` for the options."""
    outdir = os.path.realpath(outdir)
    if os.path.exists(outdir) and (not os.path.isdir(outdir) or os.listdir(outdir)):
        raise ValueError('output directory %s already exists and is not empty; choose a fresh OUTDIR' % outdir)
    parent = os.path.dirname(outdir)
    os.makedirs(parent, exist_ok=True)
    work = tempfile.mkdtemp(prefix='.' + os.path.basename(outdir) + '.', dir=parent)
    try:
        rows = split_into(lines, work, **options)
        mask = os.umask(0)
        os.umask(mask)
        os.chmod(work, 0o777 & ~mask)  # mkdtemp is private; match a plain mkdir
        os.replace(work, outdir)  # fails rather than merges if OUTDIR gained files meanwhile
    except BaseException:
        shutil.rmtree(work, ignore_errors=True)
        raise
    return rows


def split_into(lines, outdir, mux_split=True, include_notify=False, include_control=False, include_txsubmission2=False,
               connection_lifecycle=False):
    """Stream `lines` and write the session files and index into existing `outdir`.
    With include_notify, include Notify. With include_control, include control-only
    ChainSync and BlockFetch. include_txsubmission2 requires enriched control
    evidence. Any protocol option enables protocol-tagged output.
    connection_lifecycle selects explicit handshake/cleanup boundaries instead
    of NewMux, requiring an observed live generation for every supported wire row.
    Returns the index rows, with extra generation fields in lifecycle mode."""
    if connection_lifecycle and not mux_split:
        raise ValueError('--connection-lifecycle cannot be combined with --no-mux-split')
    lifecycle = ConnectionLifecycle() if connection_lifecycle else None
    mixed = include_notify or include_control or include_txsubmission2
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
                    ((key[2],) if mixed else ()) +
                    ((s['generation']['generation'], s['generation']['handlerThread'],
                      s['generation']['handshakeLine']) if lifecycle else ()))

    def record(lineno, line):
        """Process one raw line; every malformed protocol row raises, none is skipped."""
        i = line.find('{')
        if i < 0 or (LF not in line and MUX not in line and
                     (not include_notify or LN not in line) and
                     (not include_control or (CS not in line and BF not in line)) and
                     (not include_txsubmission2 or TS not in line) and
                     (not lifecycle or (HANDSHAKE not in line and CLEANUP not in line))):   # cheap pre-filter
            return
        o = json.loads(line[i:])
        # Local devnet supervisors wrap the node JSON in a message string or object,
        # possibly after whitespace or a journal prefix.
        # Keep the outer line number as the source-map coordinate.
        if 'ns' not in o:
            nested = o.get('message')
            if isinstance(nested, str) and '{' in nested:
                nested = json.loads(nested[nested.find('{'):])
            if isinstance(nested, dict):
                o = nested
        if 'ns' not in o:
            # The pre-filter saw protocol text; dropping the row could change a verdict.
            raise ValueError('protocol text without a parseable "ns" record')
        ns = o['ns']
        if not isinstance(ns, str):
            raise ValueError('"ns" must be a string')
        if lifecycle and ns in (HANDSHAKE, CLEANUP):
            cid = lifecycle.observe(o, lineno)
            if cid is not None:
                for key in list(open_):
                    if key[0] == cid:
                        close(key, 'connection')
            return
        if ns.startswith(MUX):
            if not lifecycle and mux_split and ns == MUX + 'NewMux':
                cid = o['data']['bearer']['connectionId']
                for key in list(open_):
                    if key[0] == cid:
                        close(key, 'mux')
            return
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
            return
        # Serialised tracers are separate observations, not wire-message rows.
        if ns.startswith(prefix + 'Serialised.'):
            return
        suffix = ns[len(prefix):]
        if suffix not in kinds:
            raise ValueError('unknown %s namespace %s' % (protocol, ns))
        role, direction, kind = kinds[suffix]
        d = o['data']
        cid = connection_id(d['peer']['connectionId']) if lifecycle else d['peer']['connectionId']
        generation = lifecycle.wire(o, cid, role, protocol) if lifecycle else None
        key = (cid, role, protocol)
        ev = normalizer(direction, kind, d['msg'])
        if mixed:
            # Keep the exact tracer namespace on each row, including aliases.
            payload = ev.split(' ', 2)
            ev = ns + (' ' + payload[2] if len(payload) == 3 else '')
        if key not in open_:
            counter[0] += 1
            open_[key] = {'id': 's%04d' % counter[0], 'tag': counter[0] - 1,
                          'events': [], 'src': [], 'generation': generation}
            session_roles.append(protocol + ':' + role if mixed else role)
        interleaved.append((open_[key]['tag'], ev, lineno, o['at']))
        open_[key]['events'].append(ev)
        open_[key]['src'].append((lineno, o['at']))
        if kind in ('Done', 'ClientDone'):
            close(key, 'done')

    for lineno, line in enumerate(lines, 1):
        try:
            record(lineno, line)
        except (KeyError, ValueError, TypeError, AttributeError) as err:
            raise ValueError('line %d: %s' % (lineno, 'missing field %s' % err if isinstance(err, KeyError) else err))
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
                 ('\tprotocol' if mixed else '') +
                 ('\tconnectionGeneration\thandlerThread\thandshakeLine' if lifecycle else '') + '\n')
        fh.writelines('\t'.join(map(str, r)) + '\n' for r in rows)
    if lifecycle:
        lifecycle.write(outdir)
    return rows


def selftest_fetch():
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
    print('Fetch normalization selftest passed')


def selftest_mixed():
    """Exercise all Notify shapes and mixed-protocol lifecycle isolation."""
    import json
    import tempfile
    selftest_fetch()
    cid = 'local remote'
    def line(ns, msg=None):
        data = {'bearer': {'connectionId': cid}} if ns.startswith(MUX) else {
            'peer': {'connectionId': cid}, 'msg': msg}
        return json.dumps({'ns': ns, 'at': 't', 'data': data})
    def ln(suffix, msg):
        return line(LN + suffix, msg)
    assert normalize_notify('Recv', 'BlockAnnouncement', {}) == 'Recv BlockAnnouncement -'
    assert normalize_notify('Recv', 'BlockAnnouncement', {
        'ebHash': 'AB', 'ebSlot': 3, 'ebBodySize': 20}) == 'Recv BlockAnnouncement ab 3 20'
    assert normalize_notify('Send', 'Votes', {'votes': [
        {'rbHash': 'AB', 'voterId': 2}, {'rbHash': 'CD', 'voterId': 4}]}) == 'Send Votes ab:2,cd:4'
    assert normalize_notify('Send', 'Votes', {'votes': []}) == 'Send Votes -'
    for kind, msg in [('BlockAnnouncement', {'ebHash': 'ab'}),
                      ('Votes', {'votes': {}}),
                      ('Votes', {'votes': [{'rbHash': 'ab', 'voterId': -1}]}),
                      ('RequestNext', {'kind': 'MsgDone'})]:
        try:
            normalize_notify('Send', kind, msg)
        except (ValueError, KeyError):
            pass
        else:
            raise AssertionError((kind, msg))
    lines = [
        ln('Send.RequestNext', {}),
        line(LF + 'Send.BlockRequest', {'ebHash': 'ab', 'ebSlot': 3}),
        ln('Receive.BlockOffer', {'ebHash': 'ab', 'ebSlot': 3, 'ebBytesSize': 20}),
        ln('Send.Done', {}),
        line(LF + 'Receive.Block', {'ebHash': 'ab', 'ebBytesSize': 20}),
        ln('Send.NotificationRequestNext', {}),
        ln('Receive.BlockTxsOffer', {'ebHash': 'ab', 'ebSlot': 3}),
        ln('Receive.RequestNext', {}),
        line(MUX + 'State', {'state': 'Dead'}),
        ln('Send.Votes', {'votes': []}),
        line(MUX + 'NewMux'),
        ln('Send.RequestNext', {}),
    ]
    with tempfile.TemporaryDirectory() as tmp:
        rows = split(lines, tmp, include_notify=True)
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
        split([ln('Receive.BlockAnnouncement', {})], root / 'missing', include_notify=True)
        assert (root / 'missing/interleaved.txt').read_text() == 'sessions notify:client\n0 LeiosNotify.Remote.Receive.BlockAnnouncement -\n'
    print('Mixed Notify/Fetch normalization selftest passed')


def selftest_cli():
    """Check the consolidated entry point, its modes and actionable input errors."""
    import subprocess

    def row(ns, msg):
        return json.dumps({'ns': ns, 'at': 't', 'data': {
            'peer': {'connectionId': 'a b'}, 'msg': msg}}) + '\n'

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        log = root / 'node.jsonl'
        log.write_text(row(LF + 'Send.BlockRequest', {'ebHash': 'ab', 'ebSlot': 3}) +
                       row(LN + 'Send.RequestNext', {}) +
                       row(CS + 'Send.RequestNext', {}) +
                       row(BF + 'Send.RequestRange', {}))
        command = [sys.executable, '-I', str(Path(__file__).resolve())]

        def run(name, *options, expected=0):
            out = root / name
            result = subprocess.run(command + [str(log), str(out), *options],
                                    cwd=root, capture_output=True, text=True)
            assert result.returncode == expected, (options, result.stdout, result.stderr)
            assert 'Traceback' not in result.stderr, result.stderr
            return out, result

        out, _ = run('mixed')
        assert (out / 'interleaved.txt').read_text().splitlines()[0] == (
            'sessions fetch:client notify:client chainsync:client blockfetch:client')
        assert (out / 's0001-fetch-client.txt').is_file()
        out, _ = run('fetch', '--fetch-only')
        assert (out / 'interleaved.txt').read_text() == (
            'sessions client\n0 Send BlockRequest ab 3\n')
        assert (out / 's0001-client.txt').is_file()
        assert not (out / 's0001-fetch-client.txt').exists()
        assert not (out / 'index.tsv').read_text().splitlines()[0].endswith('protocol')
        run('no-mux-split', '--no-mux-split')
        log.write_text(row(TS + 'Receive.RequestTxIds', {}))
        _, result = run('missing-evidence', expected=2)
        assert 'requires a logged boolean blocking field' in result.stderr
        out, _ = run('excluded', '--exclude-txsubmission2')
        assert (out / 'interleaved.txt').read_text() == 'sessions\n'
        run('conflict', '--fetch-only', '--exclude-txsubmission2', expected=2)
        run('unknown', '--invent-controls', expected=2)
        run('selftest-conflict', '--selftest', expected=2)
        result = subprocess.run(command, capture_output=True, text=True)
        assert result.returncode == 2 and 'LOG and OUTDIR are required' in result.stderr
        result = subprocess.run(command + ['--help'], capture_output=True, text=True)
        assert result.returncode == 0 and '--fetch-only' in result.stdout
        # Wrapped rows survive leading whitespace, journal prefixes and object messages.
        record = json.loads(row(LF + 'Send.BlockRequest', {'ebHash': 'ab', 'ebSlot': 3}))
        log.write_text(''.join(json.dumps({'message': m}) + '\n' for m in
                               (' ' + json.dumps(record), 'node[1]: ' + json.dumps(record), record)))
        out, _ = run('wrapped', '--fetch-only')
        assert (out / 'interleaved.txt').read_text() == 'sessions client\n' + '0 Send BlockRequest ab 3\n' * 3
        # Rerunning into a used OUTDIR is refused and leaves the earlier run intact.
        before = {p.name: p.read_bytes() for p in out.iterdir()}
        _, result = run('wrapped', '--fetch-only', expected=2)
        assert 'not empty' in result.stderr
        assert {p.name: p.read_bytes() for p in out.iterdir()} == before
        # Unreadable protocol rows are line-numbered input errors, never skipped.
        for bad in ['{"ns": "%sSend.Done", ' % LF,
                    json.dumps({'message': 'dropped ' + LF + 'Send.Done'}),
                    json.dumps({'ns': LF + 'Send.Done', 'at': 't'}),
                    json.dumps({'ns': LF + 'Send.Done', 'data': record['data']}),
                    json.dumps({'ns': MUX + 'NewMux', 'at': 't', 'data': {}}),
                    json.dumps({'ns': ['x'], 'note': LF})]:
            log.write_text('irrelevant\n' + bad + '\n')
            _, result = run('bad', expected=2)
            assert result.stderr.startswith('error: line 2:'), (bad, result.stderr)
        # A failing run publishes nothing, not even session files closed before the error.
        log.write_text(row(LF + 'Send.Done', {}) + row(LF + 'Send.Bogus', {}))
        out, _ = run('partial', expected=2)
        assert not out.exists() and not list(root.glob('.partial*'))
        (root / 'premade').mkdir()
        log.write_text(row(LF + 'Send.Done', {}))
        out, _ = run('premade', '--fetch-only')
        assert (out / 'index.tsv').is_file()
        print('Log normalization CLI modes and diagnostics passed')


def main(argv=None):
    """Expose one protocol-neutral CLI, retaining an explicit legacy Fetch mode."""
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('log', nargs='?', metavar='LOG', help='raw node log to read')
    parser.add_argument('outdir', nargs='?', metavar='OUTDIR', help='directory for normalized sessions and source maps')
    parser.add_argument('--fetch-only', action='store_true',
                        help='normalize only Fetch, with legacy role-only headers and filenames')
    parser.add_argument('--no-mux-split', action='store_true',
                        help='split after protocol Done only; do not split at NewMux')
    parser.add_argument('--exclude-txsubmission2', action='store_true',
                        help='explicitly omit TxSubmission2 when its control evidence is unavailable')
    parser.add_argument('--connection-lifecycle', action='store_true',
                        help='use explicit handshake/cleanup generations instead of NewMux; requires thread IDs')
    parser.add_argument('--selftest', action='store_true', help='run embedded adapter and CLI checks without input files')
    args = parser.parse_args(argv)
    if args.selftest:
        if args.log is not None or args.outdir is not None or args.fetch_only or args.no_mux_split or args.exclude_txsubmission2 or args.connection_lifecycle:
            parser.error('--selftest cannot be combined with input paths or normalization options')
        selftest_mixed()
        selftest_cli()
        return 0
    if args.log is None or args.outdir is None:
        parser.error('LOG and OUTDIR are required unless --selftest is used')
    if args.connection_lifecycle and args.no_mux_split:
        parser.error('--connection-lifecycle cannot be combined with --no-mux-split')
    if args.fetch_only and args.exclude_txsubmission2:
        parser.error('--fetch-only already excludes TxSubmission2; choose one option')
    try:
        with open(args.log, encoding='utf-8') as log:
            rows = split(log, args.outdir, mux_split=not args.no_mux_split,
                         include_notify=not args.fetch_only,
                         include_control=not args.fetch_only,
                         include_txsubmission2=not args.fetch_only and not args.exclude_txsubmission2,
                         connection_lifecycle=args.connection_lifecycle)
    except (OSError, ValueError) as err:
        parser.exit(2, f'error: {err}\n')
    print('%d sessions written to %s' % (len(rows), args.outdir))
    return 0


if __name__ == '__main__':
    sys.exit(main())
