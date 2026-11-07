#!/usr/bin/env python3
"""Batch-replay every LeiosNotify session of a multi-host raw capture through LookaheadMain.

The raw log is split by its JSON `host` field; each host subset goes through
normalize_logs.split_into(include_notify=True), keeping original raw line numbers.
Every Notify session runs locally (server under generic-next and node-next, client
once). A client session at host A on connection "x y" is paired with the unique
server session at another host on the literal connection "y x" with the same
generation "<NewMux count before it>.<Done segment within that mux>"; addresses are
never canonicalized. Each pair runs under both contracts. Timeouts, output-budget
and heap exhaustion are resource-inconclusive; exit/tag disagreement is
checker-inconclusive. Neither is a protocol verdict.

Writes DIR/results.jsonl, DIR/summary.json and DIR/input.sha256 (DIR must be new).
"""
import argparse
from bisect import bisect_left
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SILENCED = 'driver-log-no-request-votes'
CONTRACTS = ('generic-next', 'node-next')


def module_at(name, path):
    """Load repository-owned helpers by path, never via the interpreter search path."""
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


RUNNER = module_at('capture_batch_runner', HERE / 'replay_lookahead.py')
NORMAL = module_at('capture_batch_normal', HERE.parents[1] / 'LogProcessing/normalize_logs.py')
PAIR = RUNNER.PAIR
NEWMUX = NORMAL.MUX + 'NewMux'


def owners(raw):
    """Map raw line -> host for Notify and NewMux rows; count NewMux lines per (host, connection)."""
    owner, muxes = {}, defaultdict(list)
    with open(raw, encoding='utf-8') as lines:
        for number, line in enumerate(lines, 1):
            if NORMAL.LN not in line and NEWMUX not in line:
                continue
            try:
                record = json.loads(line[line.index('{'):])
                if 'ns' not in record:  # supervisor wrapper, unwrapped as normalize_logs.split_into does
                    nested = record.get('message')
                    if isinstance(nested, str) and '{' in nested:
                        nested = json.loads(nested[nested.find('{'):])
                    if isinstance(nested, dict):
                        record = nested
                ns = record['ns']
                if not (isinstance(ns, str) and (ns.startswith(NORMAL.LN) or ns == NEWMUX)):
                    continue
                host = record['host']
                if not isinstance(host, str) or not host:
                    raise ValueError('host must be a nonempty string')
                owner[number] = host
                if ns == NEWMUX:
                    muxes[host, record['data']['bearer']['connectionId']].append(number)
            except (ValueError, KeyError, TypeError) as exc:
                raise ValueError('%s line %d: Notify/NewMux row needs JSON with ns, host and data: %s'
                                 % (raw, number, exc)) from exc
    return owner, muxes


def sessions(raw, out, owner, muxes):
    """Split each host subset in place (other lines blanked) so .src files keep raw line numbers."""
    found = []
    for index, host in enumerate(sorted(set(owner.values()))):
        target = out / 'sessions' / ('host-%02d' % index)
        target.mkdir(parents=True)
        with open(raw, encoding='utf-8') as lines:
            rows = NORMAL.split_into((line if owner.get(n) == host else '' for n, line in enumerate(lines, 1)),
                                     target, include_notify=True)
        segments = Counter()
        for sid, cid, role, *_rest, protocol in rows:  # rows are in session-open order
            if protocol != 'notify':
                continue
            stem = target / ('%s-notify-%s' % (sid, role))
            first = int(stem.with_suffix('.src').read_text().split()[0])
            mux = bisect_left(muxes[host, cid], first)
            segment = segments[cid, role, mux]
            segments[cid, role, mux] += 1
            found.append({'host': host, 'connection': cid, 'role': role, 'generation': '%d.%d' % (mux, segment),
                          'file': stem.with_suffix('.txt'), 'sourceMap': stem.with_suffix('.src')})
    return found


def swapped(cid):
    """The peer's view of a literal "local remote" connection string, or None."""
    parts = cid.split(' ')
    return parts[1] + ' ' + parts[0] if len(parts) == 2 else None


def pairs(found):
    """Pair a client with a server only if each is the other's unique exact-literal, equal-generation match."""
    clients = defaultdict(list)
    servers = defaultdict(list)
    for s in found:
        (clients if s['role'] == 'client' else servers)[s['connection'], s['generation']].append(s)
    matched = []
    for c in (s for s in found if s['role'] == 'client'):
        cands = [s for s in servers[swapped(c['connection']), c['generation']] if s['host'] != c['host']]
        if len(cands) == 1:
            back = [x for x in clients[c['connection'], c['generation']] if x['host'] != cands[0]['host']]
            if back == [c]:
                matched.append((c, cands[0]))
    return matched


def classify(execution, observation):
    """Return (status, firstDiagnostic); only an exit code agreeing with the first-line tag is a verdict."""
    out, err = execution['stdout'].splitlines(), execution['stderr']
    if execution['failure'] or 'heap exhausted' in err.lower():
        return 'resource-inconclusive', execution['failure'] or 'heap exhausted'
    expected = {0: 'accepted-prefix', 1: 'protocol-rejected', 2: 'invalid-input'}
    if observation == SILENCED:
        expected[3] = 'undetermined'
    detail = next((l for l in out[1:] if not l.startswith(('observation=', 'initial=', 'connection='))), None)
    if not out or expected.get(execution['code']) != out[0]:
        return 'checker-inconclusive', (err.strip().splitlines() or ['exit/tag disagree'])[0]
    return out[0], detail


def run_batch(raw, checker, out, observation, timeout=60, heap='512M'):
    """Run every local session and every matched pair sequentially; return the summary counts."""
    if not re.fullmatch(r'[1-9][0-9]*[KMG]', heap):
        raise ValueError('heap must be a positive K/M/G limit, for example 512M')
    raw, checker, out = Path(raw).resolve(), Path(checker).resolve(), Path(out).resolve()
    if any(c.isspace() for c in raw.name):
        raise ValueError('raw log file name must not contain whitespace (it labels pair sources)')
    if not (checker.is_file() and os.access(checker, os.X_OK)):
        raise ValueError('%s is not an executable checker' % checker)
    owner, muxes = owners(raw)  # validate before creating DIR
    out.mkdir(parents=True)  # refuses an existing DIR, so runs never mix
    (out / 'input.sha256').write_text('%s  %s\n' % (RUNNER.sha256_file(raw)[0], raw))
    found = sessions(raw, out, owner, muxes)
    matched = pairs(found)
    counts = Counter()

    def run(row, mode, args, source):
        argv = [str(checker), *args, '--observation', observation, '--assume-fresh', '+RTS', '-M' + heap, '-RTS']
        execution = RUNNER.execute(argv, timeout, 1048576)
        status, diagnostic = classify(execution, observation)
        row = dict(row, mode=mode, status=status, exit=execution['code'], seconds=execution['seconds'],
                   firstDiagnostic=diagnostic, sourceFile=str(source))
        counts['/'.join([mode, row['role'], row['contract'], status])] += 1
        with open(out / 'results.jsonl', 'a') as stream:
            stream.write(json.dumps(row) + '\n')

    for s in found:
        key = {k: s[k] for k in ('host', 'connection', 'role', 'generation')}
        for contract in (CONTRACTS if s['role'] == 'server' else ('-',)):
            run(dict(key, contract=contract), 'local',
                ['--notify-lookahead', str(s['file']), '--role', s['role'],
                 '--next-contract', 'generic-next' if contract == '-' else contract], s['file'])
    for index, (c, s) in enumerate(matched):
        pair_file = out / 'pairs' / ('pair-%04d.txt' % index)
        pair_file.parent.mkdir(exist_ok=True)
        key = dict(host=[c['host'], s['host']], connection=c['connection'], role='pair', generation=c['generation'])
        try:
            declared = [PAIR.endpoint(dict(node=e['host'], connection=Path(e['file']).stem, generation=e['generation'],
                                           capture='fresh', file=str(e['file']), source=raw.name,
                                           sourceMap=str(e['sourceMap'])), role, out, 'LeiosNotifyP')
                        for e, role in ((c, 'client'), (s, 'server'))]
        except (ValueError, OSError) as exc:
            for contract in CONTRACTS:
                counts['paired/pair/%s/invalid-input' % contract] += 1
                with open(out / 'results.jsonl', 'a') as stream:
                    stream.write(json.dumps(dict(key, mode='paired', contract=contract, status='invalid-input',
                                                 exit=None, seconds=0, firstDiagnostic=str(exc),
                                                 sourceFile=str(pair_file))) + '\n')
            continue
        pair_file.write_text('\n'.join(['pair LeiosNotifyP pair-%04d %s' % (index, c['generation']),
                                        declared[0][0], declared[1][0], *declared[0][1], *declared[1][1]]) + '\n')
        for contract in CONTRACTS:
            run(dict(key, contract=contract), 'paired',
                ['--paired-notify-lookahead', str(pair_file), '--next-contract', contract], pair_file)
    summary = dict(sorted(counts.items()), pairedMatched=len(matched), pairedUnmatched=len(found) - 2 * len(matched))
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    return summary


def synthetic_log(path):
    """Two hosts: one graceful pair (after NewMux) and one client-only session with a RequestNext row.
    One Notify row is supervisor-wrapped (node JSON in a `message` string after a journal prefix)."""
    def row(host, cid, ns, **msg):
        return {'host': host, 'at': 't', 'ns': ns, 'data': {'peer': {'connectionId': cid}, 'msg': msg}}

    def mux(host, cid):
        return {'host': host, 'at': 't', 'ns': 'Net.Mux.Remote.NewMux', 'data': {'bearer': {'connectionId': cid}}}

    a, b, ln = '10.0.0.1:3001 10.0.0.2:3001', '10.0.0.2:3001 10.0.0.1:3001', 'LeiosNotify.Remote.'
    rows = [mux('A', a), mux('B', b),
            row('B', b, ln + 'Send.BlockAnnouncement'), row('A', a, ln + 'Receive.BlockAnnouncement'),
            row('A', a, ln + 'Send.Quit'), row('B', b, ln + 'Receive.Quit'),
            row('B', b, ln + 'Send.Canceled'), row('A', a, ln + 'Receive.Canceled'),
            row('B', b, ln + 'Send.Done'), row('A', a, ln + 'Receive.Done'),
            row('A', '10.0.0.1:3001 10.0.0.3:3001', ln + 'Send.RequestNext'),
            row('A', a, 'LeiosFetch.Remote.Send.Done')]
    rows[7] = {'message': 'node[1]: ' + json.dumps(rows[7])}  # A Receive.Canceled
    path.write_text('not json\n' + ''.join(json.dumps(r) + '\n' for r in rows))


FAKE = '''import sys
from pathlib import Path
args = sys.argv[1:]
text = Path(args[1]).read_text()
if %r:
    import time; time.sleep(30)
if args[0] == '--notify-lookahead' and 'RequestNext' in text and '%s' in args:
    print('invalid-input\\nobservation=fake\\ninitial=fake\\ninput line 2: silenced kind present'); raise SystemExit(2)
print('accepted-prefix\\nobservation=fake\\ninitial=fake\\nfake accepted'); raise SystemExit(0)
'''


def selftest(checker=None, out=None):
    """Assert the per-session/pair summary on the synthetic capture; a fake checker unless one is given."""
    run = lambda code, out, err='': dict(code=code, stdout=out, stderr=err, failure=None)
    assert classify(run(3, 'undetermined\nconnection=c\nno verdict'), SILENCED) == ('undetermined', 'no verdict')
    assert classify(run(3, 'undetermined\n'), 'driver-log')[0] == 'checker-inconclusive'
    assert classify(run(251, '', 'Heap exhausted;'), SILENCED)[0] == 'resource-inconclusive'
    assert classify(run(1, 'accepted-prefix\n'), SILENCED)[0] == 'checker-inconclusive'
    with tempfile.TemporaryDirectory(prefix='capture-batch-') as tmp:
        tmp = Path(tmp)
        # Keep the smoke capture beside --out so input.sha256 names a surviving file.
        raw = Path(str(out) + '-capture.log') if out else tmp / 'capture.log'
        synthetic_log(raw)
        fakes = []
        for slow in (False, True):
            fake = tmp / ('fake-slow' if slow else 'fake')
            fake.write_text('#!' + sys.executable + '\n' + FAKE % (slow, SILENCED))
            fake.chmod(0o700)
            fakes.append(fake)
        summary = run_batch(raw, checker or fakes[0], out or tmp / 'run', SILENCED, timeout=15)
        expect = {'local/server/node-next/accepted-prefix': 1, 'local/server/generic-next/accepted-prefix': 1,
                  'local/client/-/invalid-input': 1, 'local/client/-/accepted-prefix': 1,
                  'paired/pair/node-next/accepted-prefix': 1, 'paired/pair/generic-next/accepted-prefix': 1,
                  'pairedMatched': 1, 'pairedUnmatched': 1}
        assert summary == expect, summary
        rows = [json.loads(l) for l in ((out or tmp / 'run') / 'results.jsonl').read_text().splitlines()]
        assert {(r['role'], r['connection'], r['generation']) for r in rows} == {
            ('client', '10.0.0.1:3001 10.0.0.2:3001', '1.0'), ('server', '10.0.0.2:3001 10.0.0.1:3001', '1.0'),
            ('client', '10.0.0.1:3001 10.0.0.3:3001', '0.0'), ('pair', '10.0.0.1:3001 10.0.0.2:3001', '1.0')}, rows
        graceful = next(r for r in rows if r['role'] == 'client' and r['generation'] == '1.0')
        assert 'Receive.Canceled' in Path(graceful['sourceFile']).read_text(), graceful  # wrapped row kept
        if checker:
            return {'selftest': 'passed', 'checker': str(checker), 'runs': len(rows), 'summary': summary}
        slow = run_batch(raw, fakes[1], tmp / 'slow', SILENCED, timeout=0.3)
        assert set(k.split('/')[-1] for k in slow if '/' in k) == {'resource-inconclusive'}, slow
    return {'selftest': 'passed', 'checker': 'fake', 'runs': len(rows), 'timeoutControl': 'resource-inconclusive'}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--raw', type=Path, help='raw multi-host JSON capture')
    parser.add_argument('--checker', type=Path, help='compiled LookaheadMain (with --selftest: real-binary smoke)')
    parser.add_argument('--out', type=Path, help='new output directory')
    parser.add_argument('--observation', choices=['driver-log', SILENCED])
    parser.add_argument('--timeout', type=float, default=60, help='seconds per checker run (default 60)')
    parser.add_argument('--heap', default='512M', help='checker RTS heap cap (default 512M)')
    parser.add_argument('--selftest', action='store_true',
                        help='synthetic capture; fake checker unless --checker is given')
    args = parser.parse_args()
    if args.selftest:
        if args.raw or args.observation:
            parser.error('--selftest takes only --checker/--out')
        print(json.dumps(selftest(args.checker, args.out), indent=2))
        return
    if not (args.raw and args.checker and args.out and args.observation):
        parser.error('--raw, --checker, --out and --observation are required unless --selftest is used')
    if not 0 < args.timeout < float('inf'):
        parser.error('--timeout must be finite and positive')
    try:
        summary = run_batch(args.raw, args.checker, args.out, args.observation, args.timeout, args.heap)
    except (OSError, ValueError) as exc:
        parser.exit(2, 'error: %s\n' % exc)
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
