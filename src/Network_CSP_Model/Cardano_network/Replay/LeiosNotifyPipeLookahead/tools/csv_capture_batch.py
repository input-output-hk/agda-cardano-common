#!/usr/bin/env python3
"""Split a per-connection CSV capture into LeiosNotify sessions and replay each with LookaheadMain.

CSV columns: at,protocol,direction,msg,ebSlot,ebHash,ebBodySize,ebBytesSize,rbHash,voterId,nVotes
One file per remote address:port, named conn-<address>-<port>.csv. Role follows
message agency; Done closes that role's session. File order is kept (timestamps are
not sorted).

The capture has no NewMux, handshake or connection id, and an outbound reconnect
reuses the peer's listening port, so it lands in the same file as the dead
connection. A role's session is therefore also closed when its next row is a
RequestNext that follows at least --split-silence seconds without rows while that
session still has unanswered requests (a live client at full depth resumes with a
reply, not a request). A split is undone when the new session ever has more replies
than requests: a fresh connection starts with nothing outstanding, so the pause was
live. This prefers the reading that fits the log, so a reply without a request right
after a real reconnect would be read as answering the old session. Sessions are
assumed fresh only by operator assertion.

Each client session runs under `generic` and `node-client-control`; each server
session under `generic-next` and `node-next`. Timeouts are resource-inconclusive;
exit/tag disagreement is checker-inconclusive. Neither is a protocol verdict.

Writes OUT_DIR/sessions/, splits.jsonl, results.jsonl and summary.json (OUT_DIR must be new).

usage: csv_capture_batch.py CAPTURE_DIR OUT_DIR --checker BIN [--timeout S] [--heap 2G] [--only GLOB]
                            [--split-silence S] [--split-only]
       csv_capture_batch.py --selftest
"""
import argparse, csv, glob, json, os, subprocess, sys, tempfile, time
from collections import Counter
from datetime import datetime

sys.dont_write_bytecode = True
KIND = {'MsgLeiosNotificationRequestNext': 'RequestNext', 'MsgQuit': 'Quit',
        'MsgLeiosBlockAnnouncement': 'BlockAnnouncement', 'MsgLeiosBlockOffer': 'BlockOffer',
        'MsgLeiosBlockTxsOffer': 'BlockTxsOffer', 'MsgLeiosVotes': 'Votes',
        'MsgCanceled': 'Canceled', 'MsgDone': 'Done'}
INITIATOR = {'RequestNext', 'Quit'}  # client sends; everything else the server sends
# (local checker, extra args) per role
RUNS = {'client': [('generic', ['--role', 'client', '--next-contract', 'generic-next']),
                   ('node-client-control', ['--role', 'client', '--client-policy', 'node-client-control'])],
        'server': [('generic-next', ['--role', 'server', '--next-contract', 'generic-next']),
                   ('node-next', ['--role', 'server', '--next-contract', 'node-next'])]}


def hexf(s):
    if not s or any(c not in '0123456789abcdefABCDEF' for c in s):
        raise ValueError('bad hex %r' % s)
    return s.lower()


def nat(s):
    if not s.isdigit():
        raise ValueError('bad natural %r' % s)
    return str(int(s))


def event(r, lossy):
    kind = KIND[r['msg']]
    direction = {'Send': 'Send', 'Receive': 'Recv'}[r['direction']]
    role = 'client' if (direction == 'Send') == (kind in INITIATOR) else 'server'
    if kind == 'BlockAnnouncement':
        f = [r['ebHash'], r['ebSlot'], r['ebBodySize']]
        pay = '-' if not any(f) else '%s %s %s' % (hexf(f[0]), nat(f[1]), nat(f[2]))
    elif kind == 'BlockOffer':
        pay = '%s %s %s' % (hexf(r['ebHash']), nat(r['ebSlot']), nat(r['ebBytesSize']))
    elif kind == 'BlockTxsOffer':
        pay = '%s %s' % (hexf(r['ebHash']), nat(r['ebSlot']))
    elif kind == 'Votes':
        # ponytail: CSV keeps one sample vote plus a count; payload does not constrain control.
        n = int(r['nVotes'] or 0)
        if n != 1:
            lossy['votesNot1'] += 1
        pay = '-' if n == 0 else '%s:%s' % (hexf(r['rbHash']), nat(r['voterId']))
    else:
        pay = ''
    return role, kind, ('%s %s %s' % (direction, kind, pay)).rstrip()


def stamp(s):
    """Seconds since the epoch; fractions vary in length and may carry Z or a quote."""
    head, _, frac = s.strip().strip('"').partition('.')
    frac = ''.join(c for c in frac[:7] if c.isdigit())
    return datetime.fromisoformat(head + '.' + (frac + '000000')[:6]).timestamp()


def split(capture, out, only, silence):
    sessions, lossy = [], Counter()
    for path in sorted(glob.glob(os.path.join(capture, only))):
        conn = os.path.basename(path)[len('conn-'):-len('.csv')]
        seg = {'client': 0, 'server': 0}
        open_ = {}
        with open(path, newline='') as fh:
            for line, r in enumerate(csv.DictReader(fh), start=2):
                if r['protocol'] != 'LeiosNotify':
                    continue
                try:
                    role, kind, ev = event(r, lossy)
                    at = stamp(r['at'])
                except (KeyError, ValueError) as e:
                    sys.exit('%s:%d: invalid row: %s' % (path, line, e))
                gap = None
                if role in open_:
                    s = open_[role]
                    if kind == 'RequestNext' and s['outstanding'] > 0 and at - s['lastAt'] >= silence:
                        gap = at - s['lastAt']
                        s['txt'].close(); s['src'].close()
                        s['endsBy'] = 'silence'
                        del open_[role]
                        seg[role] += 1
                if role not in open_:
                    name = '%s.%s.%d' % (conn, role, seg[role])
                    s = {'name': name, 'conn': conn, 'role': role, 'segment': seg[role],
                         'rows': 0, 'last': None, 'firstLine': line, 'outstanding': 0, 'low': 0,
                         'endsBy': 'eof', 'silenceBefore': None if gap is None else round(gap, 1),
                         'txt': open(os.path.join(out, 'sessions', name + '.txt'), 'w'),
                         'src': open(os.path.join(out, 'sessions', name + '.src'), 'w')}
                    s['txt'].write('role %s\n' % role)
                    open_[role] = s
                    sessions.append(s)
                s = open_[role]
                s['txt'].write(ev + '\n')
                s['src'].write('%d %s\n' % (line, r['at']))
                s['rows'] += 1
                s['last'] = kind
                s['lastAt'] = at
                s['outstanding'] += 1 if kind == 'RequestNext' else 0 if kind in ('Quit', 'Done') else -1
                s['low'] = min(s['low'], s['outstanding'])
                if kind == 'Done':
                    s['txt'].close(); s['src'].close()
                    s['endsBy'] = 'done'
                    del open_[role]
                    seg[role] += 1
        for s in open_.values():
            s['txt'].close(); s['src'].close()
    return merge_live(sessions), lossy


def merge_live(sessions):
    """Undo a silence split whose new session ever has more replies than requests: a fresh
    connection starts with nothing outstanding, so those replies answer the old session."""
    kept, prev = [], {}
    for s in sessions:
        key = (s['conn'], s['role'])
        p = prev.get(key)
        if s['silenceBefore'] is not None and s['low'] < 0:
            for ext in ('txt', 'src'):
                with open(p[ext].name, 'a') as fh:
                    lines = open(s[ext].name).read().splitlines(True)
                    fh.writelines(lines[1:] if ext == 'txt' else lines)
                os.remove(s[ext].name)
            p['rows'] += s['rows']
            p['last'], p['endsBy'] = s['last'], s['endsBy']
            p['mergedLivePauses'] = p.get('mergedLivePauses', []) + [s['silenceBefore']]
            continue
        kept.append(s)
        prev[key] = s
    return kept


def run(checker, txt, extra, timeout, heap):
    cmd = [checker, '--notify-lookahead', txt] + extra + ['--observation', 'driver-log', '--assume-fresh',
                                                          '+RTS', '-M' + heap, '-RTS']
    t = time.monotonic()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'resource-inconclusive', None, time.monotonic() - t, 'timeout'
    lines = p.stdout.splitlines()
    tag = lines[0] if lines else ''
    expect = {0: 'accepted-prefix', 1: 'protocol-rejected', 2: 'invalid-input'}.get(p.returncode)
    status = tag if tag == expect else 'checker-inconclusive'
    diag = next((l for l in lines[1:] if l.strip()), p.stderr.strip()[:300])
    return status, p.returncode, time.monotonic() - t, diag


def selftest():
    """A reconnect after silence splits; a live pause, a request with nothing outstanding,
    and a split whose new session has more replies than requests do not."""
    hdr = 'at,protocol,direction,msg,ebSlot,ebHash,ebBodySize,ebBytesSize,rbHash,voterId,nVotes\n'
    row = lambda t, d, m: '2026-11-06T08:%s,LeiosNotify,%s,%s,,,,,,,\n' % (t, d, m)
    rn, cx = 'MsgLeiosNotificationRequestNext', 'MsgCanceled'
    rows = [row('00:00.0000001', 'Send', rn), row('00:00.0000002', 'Send', rn),
            row('00:01.0', 'Receive', cx),               # 1 outstanding
            row('02:00.0', 'Receive', cx),               # live pause of 119 s: reply, no split
            row('03:00.0', 'Send', rn),                  # 60 s, nothing outstanding: no split
            row('04:00.0', 'Send', rn),                  # 60 s, 1 outstanding: reconnect, split
            row('04:00.1', 'Send', rn)]
    live = [row('00:00.1', 'Send', rn), row('00:00.2', 'Send', rn),
            row('01:00.2', 'Send', rn),                  # candidate split after 60 s...
            row('01:00.3', 'Receive', cx), row('01:00.4', 'Receive', cx),
            row('01:00.5', 'Receive', cx)]               # ...but 3 replies to 1 request: live, merged
    with tempfile.TemporaryDirectory() as d:
        os.makedirs(os.path.join(d, 'cap')); os.makedirs(os.path.join(d, 'out', 'sessions'))
        open(os.path.join(d, 'cap', 'conn-1.2.3.4-3001.csv'), 'w').write(hdr + ''.join(rows))
        open(os.path.join(d, 'cap', 'conn-5.6.7.8-3001.csv'), 'w').write(hdr + ''.join(live))
        ss, _ = split(os.path.join(d, 'cap'), os.path.join(d, 'out'), 'conn-*.csv', 30)
        got = [(s['name'], s['rows'], s['endsBy'], s['silenceBefore']) for s in ss]
        merged = open(os.path.join(d, 'out', 'sessions', '5.6.7.8-3001.client.0.txt')).read().count('\n')
        gone = os.path.exists(os.path.join(d, 'out', 'sessions', '5.6.7.8-3001.client.1.txt'))
    assert got == [('1.2.3.4-3001.client.0', 5, 'silence', None),
                   ('1.2.3.4-3001.client.1', 2, 'eof', 60.0),
                   ('5.6.7.8-3001.client.0', 6, 'eof', None)], got
    assert ss[2]['mergedLivePauses'] == [60.0] and merged == 7 and not gone
    print('selftest ok')


def main():
    if sys.argv[1:] == ['--selftest']:
        return selftest()
    ap = argparse.ArgumentParser()
    ap.add_argument('capture'); ap.add_argument('out')
    ap.add_argument('--checker', required=True)
    ap.add_argument('--timeout', type=float, default=600)
    ap.add_argument('--heap', default='2G')
    ap.add_argument('--only', default='conn-*.csv')
    ap.add_argument('--split-silence', type=float, default=30)
    ap.add_argument('--split-only', action='store_true', help='write sessions and splits.jsonl, run nothing')
    a = ap.parse_args()
    os.makedirs(os.path.join(a.out, 'sessions'))  # must be new
    sessions, lossy = split(a.capture, a.out, a.only, a.split_silence)
    with open(os.path.join(a.out, 'splits.jsonl'), 'w') as fh:
        for s in sessions:
            fh.write(json.dumps({k: s.get(k) for k in ('name', 'conn', 'role', 'segment', 'rows', 'firstLine',
                                                       'endsBy', 'silenceBefore', 'mergedLivePauses')}) + '\n')
    if a.split_only:
        return
    summary = Counter()
    with open(os.path.join(a.out, 'results.jsonl'), 'w') as res:
        for s in sessions:
            graceful = s['last'] == 'Done'
            for label, extra in RUNS[s['role']]:
                status, code, secs, diag = run(a.checker, s['txt'].name, extra, a.timeout, a.heap)
                row = {'session': s['name'], 'conn': s['conn'], 'role': s['role'], 'segment': s['segment'],
                       'rows': s['rows'], 'firstCsvLine': s['firstLine'], 'endsWithDone': graceful,
                       'endsBy': s['endsBy'], 'silenceBefore': s['silenceBefore'],
                       'check': label, 'status': status, 'exit': code, 'seconds': round(secs, 2),
                       'firstDiagnostic': diag}
                res.write(json.dumps(row) + '\n'); res.flush()
                summary['%s/%s/%s/%s' % (s['role'], label, s['endsBy'], status)] += 1
                print(json.dumps(row), flush=True)
    report = {'sessions': len(sessions), 'lossy': lossy, 'counts': dict(sorted(summary.items()))}
    with open(os.path.join(a.out, 'summary.json'), 'w') as fh:
        json.dump(report, fh, indent=1)
    print(json.dumps(report, indent=1))


if __name__ == '__main__':
    main()
