#!/usr/bin/env python3
"""Exercise raw replay binding failures and optional real-binary fixture smoke tests."""
import argparse
import json
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def module_at(name, path):
    """Use fixed local helper paths without changing interpreter search paths."""
    import importlib.util
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


COORDINATOR = module_at('raw_coordinator_test_target', HERE / 'replay_raw_lookahead.py')
RAW = module_at('raw_coordinator_test_normalizer', HERE / 'raw-input/lookahead_raw.py')


def record(host, connection, direction, kind, **payload):
    """Build a structured fixture, retaining duplicate and ordered vote objects."""
    wire_kind = ('MsgLeiosNotificationRequestNext' if kind == 'RequestNext' else
                 'Msg' + kind if kind in {'Quit', 'Canceled', 'Done'} else
                 'MsgLeios' + kind)
    return {'host': host, 'at': '2026-11-05T00:00:00.000000000Z',
            'thread': 'wire-1',
            'ns': 'LeiosNotify.Remote.' + direction + '.' + kind,
            'data': {'kind': 'Send' if direction == 'Send' else 'Recv',
                     'peer': {'connectionId': connection},
                     'msg': {'kind': wire_kind, **payload}}}


def prepare(base, mode='paired'):
    """Build a fresh request/votes/idle-close exchange at both endpoint hooks."""
    manifest = COORDINATOR.RUNNER.MANIFEST.example_manifest(mode)
    bindings = {'version': COORDINATOR.VERSION, 'endpoints': {}}
    for role, endpoint in manifest['endpoints'].items():
        host = 'node-' + role
        connection = '127.0.0.1:1 127.0.0.2:2'
        command, reply = ('Send', 'Receive') if role == 'client' else ('Receive', 'Send')
        rows = [
            {'host': host, 'at': '2026-11-05T00:00:00Z',
             'ns': 'Net.Mux.Remote.NewMux',
             'data': {'bearer': {'connectionId': connection}}},
            record(host, connection, command, 'RequestNext'),
            record(host, connection, reply, 'Votes', votes=[
                {'rbHash': '11', 'voterId': 23},
                {'rbHash': '1f', 'voterId': 37},
                {'rbHash': '11', 'voterId': 23}]),
            record(host, connection, command, 'Quit'),
            record(host, connection, reply, 'Done')]
        if mode == 'paired' and role == 'client':
            # Use the established delayed-Send schedule family for the small
            # integration smoke; closed ordinary pairs have a separate cost test.
            rows[1], rows[2] = rows[2], rows[1]
        source = base / (role + '.log')
        source.write_text(''.join(json.dumps(row) + '\n' for row in rows))
        selector = {'host': host, 'connection': connection, 'role': role,
                    'observedMuxGeneration': 1, 'segmentAfterDone': 0}
        out = base / role
        RAW.normalize_selected(source, selector, out)
        endpoint.update(file=str(out / 'local.txt'), source=str(source),
                        sourceMap=str(out / 'local.src'))
        bindings['endpoints'][role] = {'selector': selector,
                                     'detailedMap': str(out / 'map.jsonl')}
    if mode == 'paired':
        declarations, events = [], []
        for role, endpoint in manifest['endpoints'].items():
            legacy = {key: endpoint[key] for key in [
                'node', 'connection', 'generation', 'capture', 'file', 'source', 'sourceMap']}
            declaration, local, _ = COORDINATOR.RUNNER.PAIR.endpoint(
                legacy, role, base, 'LeiosNotifyP')
            declarations.append(declaration)
            events.extend(local)
        checker_input = base / 'pair.txt'
        checker_input.write_text('\n'.join([
            'pair LeiosNotifyP ' + manifest['connection'] + ' ' + manifest['session'],
            *declarations, *events]) + '\n')
        manifest['checkerInput']['file'] = str(checker_input)
    else:
        role = next(iter(manifest['endpoints']))
        manifest['checkerInput']['file'] = manifest['endpoints'][role]['file']
    mp, bp = base / 'manifest.json', base / 'bindings.json'
    mp.write_text(json.dumps(manifest))
    bp.write_text(json.dumps(bindings))
    return mp, bp, manifest, bindings


def selftest(binary=None):
    """Confirm corrupt evidence never reaches a checker or becomes protocol rejection."""
    results = []

    def check(name, expected, mutate=None, mode='paired', arguments=None, code=0,
              tag='accepted-prefix', fake_body=None, memory_error=False):
        with tempfile.TemporaryDirectory(prefix='lookahead-raw-integration-') as directory:
            base = Path(directory)
            mp, bp, manifest, bindings = prepare(base, mode)
            marker = base / 'checker-ran'
            checker = Path(binary).resolve() if binary else base / 'fake-checker'
            if not binary:
                body = fake_body(base, manifest, bindings) if fake_body else ''
                checker.write_text('#!' + sys.executable + '\nfrom pathlib import Path\n' +
                    'Path(' + repr(str(marker)) + ').write_text("ran")\n' + body +
                    '\nprint(' + repr(tag) + ')\nraise SystemExit(' + str(code) + ')\n')
                checker.chmod(0o700)
            if mutate:
                mutate(base, mp, bp, manifest, bindings)
            original = COORDINATOR.module_at

            def injected(name, path):
                module = original(name, path)
                if name == 'lookahead_raw_correspondence':
                    def exhausted(*args, **kwargs):
                        raise MemoryError()
                    module.verify_selected = exhausted
                return module

            try:
                if memory_error:
                    COORDINATOR.module_at = injected
                report, actual = COORDINATOR.run_raw_replay(
                    checker, mp, bp, **(arguments or {}))
            finally:
                COORDINATOR.module_at = original
            assert actual == expected, (name, report)
            if actual not in (0, 1):
                assert report['protocolVerdict'] is None, (name, report)
            if actual in (2, 3) and not binary:
                assert not marker.exists(), (name, 'checker launched despite bad evidence')
            if memory_error:
                assert not marker.exists(), (name, 'checker launched despite allocation failure')
            if actual == 0:
                assert set(report['rawCorrespondence']) == set(manifest['endpoints'])
            results.append({'name': name, 'exitCode': actual, 'status': report['status'],
                            'errors': report['errors']})

    for mode in ['localclient', 'localserver', 'paired']:
        check('valid-' + mode, 0, mode=mode,
              arguments={'timeout': 5} if binary else None)
    if binary:
        return {'validation': 'real compiled binary, synthetic raw fixtures',
                'cases': len(results), 'results': results}

    def change_source(base, mp, bp, manifest, bindings):
        path = Path(manifest['endpoints']['client']['source'])
        path.write_text(path.read_text().replace('"voterId": 37', '"voterId": 38'))

    check('changed-raw-vote', 2, change_source)

    def drop_duplicate(base, mp, bp, manifest, bindings):
        path = Path(manifest['endpoints']['client']['file'])
        path.write_text(path.read_text().replace('11:23,1f:37,11:23', '11:23,1f:37'))

    check('omitted-duplicate-vote', 2, drop_duplicate)

    def bad_map(base, mp, bp, manifest, bindings):
        path = Path(bindings['endpoints']['client']['detailedMap'])
        rows = [json.loads(line) for line in path.read_text().splitlines()]
        rows[0]['byteOffset'] += 1
        path.write_text(''.join(json.dumps(row) + '\n' for row in rows))

    check('forged-byte-coordinate', 2, bad_map)

    def bad_legacy_map(base, mp, bp, manifest, bindings):
        path = Path(manifest['endpoints']['client']['sourceMap'])
        rows = path.read_text().splitlines()
        rows[0] = '999 forged-time'
        path.write_text('\n'.join(rows) + '\n')

    check('forged-legacy-coordinate', 2, bad_legacy_map)

    def bad_role(base, mp, bp, manifest, bindings):
        bindings['endpoints']['client']['selector']['role'] = 'server'
        bp.write_text(json.dumps(bindings))

    check('selector-role-mismatch', 2, bad_role)

    def no_match(base, mp, bp, manifest, bindings):
        bindings['endpoints']['client']['selector']['host'] = 'unknown'
        bp.write_text(json.dumps(bindings))

    check('selector-matches-no-events', 2, no_match)

    def unknown_other_endpoint(base, mp, bp, manifest, bindings):
        path = Path(manifest['endpoints']['client']['source'])
        obj = record('another-host', '127.0.0.3:3 127.0.0.4:4', 'Send', 'Unknown')
        with path.open('a') as stream:
            stream.write(json.dumps(obj) + '\n')

    check('unknown-notify-outside-selector', 2, unknown_other_endpoint)

    def no_assertion(base, mp, bp, manifest, bindings):
        manifest['endpoints']['client']['capture'] = 'unknown'
        mp.write_text(json.dumps(manifest))

    check('missing-capture-assertion', 3, no_assertion)

    def no_source(base, mp, bp, manifest, bindings):
        for key in ['source', 'sourceMap']:
            manifest['endpoints']['client'].pop(key)
        mp.write_text(json.dumps(manifest))

    check('missing-raw-source-binding', 2, no_source)

    def extra_role(base, mp, bp, manifest, bindings):
        bindings['endpoints']['extra'] = bindings['endpoints']['client']
        bp.write_text(json.dumps(bindings))

    check('extra-binding-role', 2, extra_role)
    check('normalized-budget', 4, arguments={'max_input_bytes': 1})
    check('raw-byte-budget', 4, arguments={'raw_limits': {'max_raw_bytes': 1}})
    check('invalid-raw-budget', 2, arguments={'raw_limits': {'unknown_limit': 1}})
    check('checker-untagged-exit', 4, code=1, tag='')
    check('completed-protocol-rejection', 1, code=1, tag='protocol-rejected')

    def mutate_during_checker(base, manifest, bindings):
        path = bindings['endpoints']['client']['detailedMap']
        return 'Path(' + repr(path) + ').write_text("changed after verification")\n'

    check('map-changed-during-checker', 4, fake_body=mutate_during_checker)

    def delete_during_checker(base, manifest, bindings):
        path = bindings['endpoints']['client']['detailedMap']
        return 'Path(' + repr(path) + ').unlink()\n'

    check('map-deleted-during-checker', 4, fake_body=delete_during_checker)

    def too_deep(base, mp, bp, manifest, bindings):
        bp.write_text('[' * 2000 + '0' + ']' * 2000)

    check('excessive-json-nesting', 2, too_deep)

    def nonfinite(base, mp, bp, manifest, bindings):
        bp.write_text('{"version":1e999,"endpoints":{}}')

    check('overflowing-json-number', 2, nonfinite)
    check('raw-allocation-failure', 4, memory_error=True)
    return {'validation': 'explicit fake checkers, no protocol proof',
            'cases': len(results), 'results': results}


def main():
    """Print auditable test summaries; optional binary mode runs three small cases."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path)
    args = parser.parse_args()
    print(json.dumps(selftest(args.binary), indent=2))


if __name__ == '__main__':
    main()
