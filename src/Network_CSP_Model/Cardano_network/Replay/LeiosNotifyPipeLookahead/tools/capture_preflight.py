#!/usr/bin/env python3
"""Inventory strict Notify capture evidence; never decide protocol compatibility."""
import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
AREA = Path(__file__).resolve().parent
KINDS = ('RequestNext', 'Quit', 'BlockAnnouncement', 'BlockOffer',
         'BlockTxsOffer', 'Votes', 'Canceled', 'Done')
ROLES = ('client', 'server')


def raw_helper():
    """Use the same strict raw-record parser as normalization verification."""
    name = '_lookahead_preflight_raw'
    if name not in sys.modules:
        spec = importlib.util.spec_from_file_location(name, AREA/'raw-input/lookahead_raw.py')
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        spec.loader.exec_module(module)
    return sys.modules[name]


class Inventory:
    """Retain bounded endpoint/generation/role segments in original source order."""

    def __init__(self, expected_role='observed', max_segments=10000,
                 host=None, connection=None):
        if expected_role not in ('observed', 'client', 'server', 'both'):
            raise ValueError('unsupported expected role')
        if isinstance(max_segments, bool) or not isinstance(max_segments, int) or max_segments <= 0:
            raise ValueError('max_segments must be a positive integer')
        self.expected_role, self.max_segments = expected_role, max_segments
        self.host, self.connection = host, connection
        self.segments, self.kinds = {}, Counter()
        self.total, self.selected, self.without_threads = 0, 0, 0

    def observe(self, row, source):
        """Selection occurs after strict parsing; malformed other endpoints still fail."""
        self.total += 1
        if self.host is not None and row['host'] != self.host:
            return
        if self.connection is not None and row['connection'] != self.connection:
            return
        if self.expected_role in ROLES and row['role'] != self.expected_role:
            return
        self.selected += 1
        if not row.get('threads'):
            self.without_threads += 1
        key = (source, row['host'], row['connection'], row['observedMuxGeneration'],
               row['segmentAfterDone'], row['role'])
        if key not in self.segments:
            if len(self.segments) >= self.max_segments:
                raise raw_helper().ResourceLimitError('preflight segment metadata limit exceeded')
            self.segments[key] = dict(source=source, host=row['host'],
                connection=row['connection'], observedMuxGeneration=row['observedMuxGeneration'],
                segmentAfterDone=row['segmentAfterDone'], role=row['role'],
                precedingNewMux=row.get('precedingNewMux'), first=None, last=None,
                events=0, counts=Counter())
        segment = self.segments[key]
        coordinate = {name: row.get(name) for name in
                      ('line', 'byteOffset', 'byteLength', 'rawLineSha256', 'at')}
        coordinate.update(kind=row['kind'], direction=row['direction'])
        if segment['first'] is None:
            segment['first'] = coordinate
        segment['last'] = coordinate
        segment['events'] += 1
        label = ('Receive' if row['direction'] == 'Recv' else row['direction']) + '.' + row['kind']
        segment['counts'][label] += 1
        self.kinds[label] += 1

    def report(self, sources):
        """Require exercised request hooks, without certifying freshness or losslessness."""
        segments, missing = [], []
        for segment in self.segments.values():
            item = dict(segment)
            hook = ('Send' if item['role'] == 'client' else 'Receive') + '.RequestNext'
            item['requiredRequestHook'] = hook
            item['requestHookObserved'] = item['counts'][hook] > 0
            item['newMuxBoundaryObserved'] = bool(item['precedingNewMux'])
            # A boundary followed by replies is allowed by delayed Send hooks;
            # this diagnostic does not impose a first-record RequestNext rule.
            item['boundaryStatus'] = ('observed-candidate' if item['newMuxBoundaryObserved']
                                      else 'not-observed')
            item['doneObserved'] = item['counts'][
                ('Receive' if item['role'] == 'client' else 'Send') + '.Done'] > 0
            item['counts'] = dict(sorted(item['counts'].items()))
            if not item['requestHookObserved']:
                missing.append(dict(segment=len(segments), evidence=hook))
            if not item['newMuxBoundaryObserved']:
                missing.append(dict(segment=len(segments), evidence='preceding NewMux boundary'))
            segments.append(item)
        observed_roles = sorted({item['role'] for item in segments})
        required_roles = (ROLES if self.expected_role == 'both' else
                          (self.expected_role,) if self.expected_role in ROLES else observed_roles)
        for role in required_roles:
            if role not in observed_roles:
                missing.append(dict(evidence='observed ' + role + ' role'))
        if not segments:
            missing.append(dict(evidence='selected Notify records'))
        totals = {kind: sum(self.kinds[direction+'.'+kind]
                           for direction in ('Send', 'Receive')) for kind in KINDS}
        return dict(schema='leiosnotify-capture-preflight-v1',
            status='missing-capture-evidence' if missing else 'preflight-observations-present',
            protocolVerdict=None, sourceProvenance='not established by log inventory',
            captureFreshness='not certified', captureLosslessness='not certified',
            selection=dict(host=self.host, connection=self.connection,
                           expectedRole=self.expected_role), sources=sources,
            totalNotifyRowsValidated=self.total, selectedNotifyRows=self.selected,
            selectedRowsWithoutThreads=self.without_threads, observedRoles=observed_roles,
            counts=dict(sorted(self.kinds.items())), messageTotals=totals,
            alphabetCoverage=dict(observed=[kind for kind in KINDS if totals[kind]],
                absent=[kind for kind in KINDS if not totals[kind]],
                meaning='Scenario coverage only; absence is not evidence of lost messages.'),
            segments=segments, missingEvidence=missing,
            limitations=[
                'This is a request-exercise capture preflight, not a replay verdict.',
                'Client segments require Send RequestNext; server segments require Receive RequestNext.',
                'Both hooks are required only when both endpoint roles are selected.',
                'Idle Quit without RequestNext can be a valid protocol trace but does not exercise this preflight.',
                'Observed NewMux is a boundary candidate, not proof of fresh/lossless capture.',
                'A first reply is allowed; delayed Send records need not precede Receive records.',
                'Sources remain separate; no paired session or cross-endpoint causal merge is inferred.',
                'Absent Votes is unexercised coverage, not proof of a filtering defect.',
                'Done and EOF do not establish physical cleanup or whole-node completion.'])


def analyze(paths, *, expected_role='observed', max_segments=10000,
            host=None, connection=None, limits=None):
    """Consume complete strict scans; return no successful partial report on failure."""
    inventory = Inventory(expected_role, max_segments, host, connection)
    sources, seen = [], set()
    for path in paths:
        source = str(Path(path).resolve())
        stat = Path(source).stat()
        identity = stat.st_dev, stat.st_ino
        if identity in seen:
            raise raw_helper().RawInputError('same capture file supplied more than once')
        seen.add(identity)
        scan = raw_helper().scan_raw(path, limits=limits)
        for row in scan:
            inventory.observe(row, source)
        sources.append(scan.summary)
    return inventory.report(sources)


def selftest():
    """Exercise endpoint-specific hooks, parser reuse, cutoffs and malformed rows."""
    checks = []
    with tempfile.TemporaryDirectory(prefix='notify-preflight-') as directory:
        path = Path(directory)/'capture.log'
        conn = '127.0.0.1:3001 127.0.0.1:3002'
        def mux(host='a'):
            return dict(host=host, ns='Net.Mux.Remote.NewMux', data=dict(bearer=dict(connectionId=conn)))
        def wire(direction, kind, host='a', **extra):
            msg = dict(kind=('MsgLeiosNotificationRequestNext' if kind in
                ('RequestNext', 'NotificationRequestNext') else
                'Msg'+kind if kind in ('Quit', 'Canceled', 'Done') else 'MsgLeios'+kind), **extra)
            return dict(host=host, at='2026-11-05T00:00:00Z', ns='LeiosNotify.Remote.'+direction+'.'+kind,
                data=dict(kind='Send' if direction=='Send' else 'Recv',
                          peer=dict(connectionId=conn), msg=msg))
        def run(rows, **kwargs):
            path.write_text(''.join(json.dumps(row)+'\n' for row in rows))
            return analyze([path], **kwargs)
        def check(name, condition):
            assert condition, name
            checks.append(name)
        r=run([mux(), wire('Send','RequestNext')], expected_role='client')
        check('single client requires only Send hook', r['status']=='preflight-observations-present')
        r=run([mux(), wire('Receive','NotificationRequestNext')], expected_role='server')
        check('server alias maps to Receive RequestNext', r['counts']=={'Receive.RequestNext':1})
        r=run([mux(), wire('Send','NotificationRequestNext'), mux('b'), wire('Receive','RequestNext','b')], expected_role='both')
        check('both roles observed without inferred pairing', r['status']=='preflight-observations-present' and len(r['segments'])==2)
        r=run([mux(), wire('Send','RequestNext')], expected_role='both')
        check('both requires server evidence', r['status']=='missing-capture-evidence')
        r=run([wire('Send','RequestNext')], expected_role='client')
        check('missing lifecycle stays explicit', r['status']=='missing-capture-evidence')
        r=run([mux(), wire('Receive','Canceled'), wire('Send','RequestNext')], expected_role='client')
        check('reply before recorded Send is permitted', r['status']=='preflight-observations-present')
        r=run([mux(), wire('Send','RequestNext'), wire('Send','RequestNext')])
        check('repeated identical messages retained', r['messageTotals']['RequestNext']==2)
        check('missing Votes informational', 'Votes' in r['alphabetCoverage']['absent'] and r['status']=='preflight-observations-present')
        check('no provenance or losslessness invention', r['protocolVerdict'] is None and r['captureLosslessness']=='not certified')
        try:
            analyze([path, path])
        except raw_helper().RawInputError:
            check('duplicate input cannot double counts', True)
        else:
            check('duplicate input', False)
        r=run([mux(), wire('Send','Quit'), wire('Receive','Done')])
        check('idle Quit is missing request exercise, not protocol rejection', r['status']=='missing-capture-evidence' and r['protocolVerdict'] is None)
        r=run([mux(), wire('Send','RequestNext'), wire('Send','Quit'), wire('Receive','Done'), wire('Send','Quit')])
        check('Done splits role segments', len(r['segments'])==2 and not r['segments'][1]['requestHookObserved'])
        r=run([mux(), wire('Send','RequestNext'), mux(), wire('Send','Quit')])
        check('reused connection gets new mux generation', len(r['segments'])==2 and r['segments'][0]['observedMuxGeneration']!=r['segments'][1]['observedMuxGeneration'])
        r=run([mux(), wire('Send','RequestNext')], host='absent')
        check('empty selection is missing evidence', r['status']=='missing-capture-evidence')
        for name, rows in [('unknown Notify kind', [wire('Send','Future')]),
                           ('wrong message discriminator', [dict(host='a', ns='LeiosNotify.Remote.Send.RequestNext', data=dict(kind='Send', peer=dict(connectionId=conn), msg=dict(kind='MsgQuit')))]),
                           ('wrong envelope direction', [dict(host='a',ns='LeiosNotify.Remote.Send.RequestNext',data=dict(kind='Recv',peer=dict(connectionId=conn),msg=dict(kind='MsgLeiosNotificationRequestNext')))])]:
            try:
                run(rows, host='absent')
            except raw_helper().RawInputError:
                check(name+' fails even outside selection', True)
            else:
                check(name, False)
        path.write_text('{"ns":"LeiosNotify.Remote.Send.RequestNext","ns":"ignored"}\n')
        try:
            analyze([path])
        except raw_helper().RawInputError:
            check('duplicate JSON keys fail', True)
        else:
            check('duplicate JSON keys', False)
        try:
            run([mux(), wire('Send','RequestNext'), mux(), wire('Send','RequestNext')], max_segments=1)
        except raw_helper().ResourceLimitError:
            check('bounded segment map', True)
        else:
            check('bounded segment map', False)
        try:
            run([wire('Send','RequestNext')], limits={'max_line_bytes':16})
        except raw_helper().ResourceLimitError:
            check('bounded line reads', True)
        else:
            check('bounded line reads', False)
    return dict(selftest='passed', count=len(checks), checks=checks)


def main(argv=None):
    """Emit JSON with distinct evidence, invalid-input and resource exit classes."""
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', nargs='*', type=Path)
    parser.add_argument('--expect-role', choices=('observed','client','server','both'), default='observed')
    parser.add_argument('--host')
    parser.add_argument('--connection')
    parser.add_argument('--max-segments', type=int, default=10000)
    parser.add_argument('--max-line-bytes', type=int, default=1048576)
    parser.add_argument('--max-input-bytes', type=int, default=17179869184)
    parser.add_argument('--max-records', type=int, default=10000000)
    parser.add_argument('--max-seconds', type=float, default=300)
    parser.add_argument('--selftest', action='store_true')
    args=parser.parse_args(argv)
    if args.selftest:
        print(json.dumps(selftest(), indent=2)); return 0
    if not args.files:
        parser.error('supply original capture files or --selftest')
    try:
        report=analyze(args.files, expected_role=args.expect_role,
            host=args.host, connection=args.connection, max_segments=args.max_segments,
            limits=dict(max_line_bytes=args.max_line_bytes, max_raw_bytes=args.max_input_bytes,
                        max_records=args.max_records, max_seconds=args.max_seconds))
        code=0 if report['status']=='preflight-observations-present' else 3
    except raw_helper().ResourceLimitError as error:
        report=dict(status='resource-inconclusive', protocolVerdict=None, error=str(error)); code=4
    except (raw_helper().RawInputError, OSError, ValueError) as error:
        report=dict(status='invalid-input', protocolVerdict=None, error=str(error)); code=2
    print(json.dumps(report, indent=2, sort_keys=True))
    return code


if __name__ == '__main__':
    raise SystemExit(main())
