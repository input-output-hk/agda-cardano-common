#!/usr/bin/env python3
"""Read-only manifest coordinator for an explicitly supplied LookaheadMain executable.

Input/evidence/resource failures remain separate from the Agda checker's verdict.
This wrapper validates declarations and artifact binding; it adds no protocol proof.
"""
import argparse
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import selectors
import signal
import stat
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def module_at(name, path):
    """Load only repository-owned helpers, never a module named by the manifest."""
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


MANIFEST = module_at('lookahead_manifest', HERE/'lookahead_manifest.py')
PAIR = module_at('lookahead_paired_sessions', HERE.parent.parent/'LogProcessing/paired_sessions.py')


class InputFailure(ValueError):
    """A structural/artifact mismatch does not assert a protocol counterexample."""


class BudgetFailure(ValueError):
    """Resource limits and changing files are inconclusive, never protocol rejection."""


def signature(path):
    """Require an existing regular file before any content read or invocation."""
    value = path.stat()
    if not stat.S_ISREG(value.st_mode):
        raise InputFailure(str(path) + ': expected regular file')
    return (value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns)


def sha256_file(path):
    """Hash even a large raw capture incrementally without loading it into memory."""
    before = signature(path)
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024*1024), b''):
            digest.update(chunk)
    if signature(path) != before:
        raise BudgetFailure(str(path) + ': changed while hashing')
    return digest.hexdigest(), before


def bounded_bytes(path, limit):
    """Bound the actual read as well as the initial stat, including concurrently growing inputs."""
    before = signature(path)
    with path.open('rb') as stream:
        raw = stream.read(limit + 1)
    if len(raw) > limit:
        raise BudgetFailure(str(path) + ': input byte budget exceeded')
    if signature(path) != before:
        raise BudgetFailure(str(path) + ': changed during bounded read')
    return raw, before


def check_inputs(validation, data, max_input_bytes):
    """Bind all normalized rows and coordinates to the declared endpoint artifacts."""
    files = {}

    def add(path, label, expected=None, bounded=True):
        path = Path(path)
        item = files.setdefault(path, {'path': str(path), 'uses': [], 'bounded': False, 'expected': []})
        item['uses'].append(label)
        item['bounded'] |= bounded
        if expected is not None:
            item['expected'].append(expected)

    add(validation['checkerInput']['file'], 'checker-input', validation['checkerInput']['declaredSha256'])
    for role, endpoint in validation['endpoints'].items():
        add(endpoint['file'], role + '-session', endpoint['declaredSha256'])
        if endpoint['sourceMap'] is not None:
            add(endpoint['sourceMap'], role + '-source-map', endpoint['declaredSourceMapSha256'])
            add(endpoint['source'], role + '-raw-source', endpoint['declaredSourceSha256'], bounded=False)
    total = 0
    for path, item in files.items():
        info = signature(path)
        if item['bounded']:
            total += info[2]
            if info[2] > max_input_bytes or total > max_input_bytes:
                raise BudgetFailure('normalized inputs/source maps exceed the aggregate byte budget')
    texts, consumed = {}, 0
    for path, item in files.items():
        if item['bounded']:
            raw, info = bounded_bytes(path, max_input_bytes - consumed)
            consumed += len(raw)
            actual = hashlib.sha256(raw).hexdigest()
            texts[path] = raw.decode('utf-8')
        else:
            actual, info = sha256_file(path)
        if any(expected != actual for expected in item['expected']):
            raise InputFailure(str(path) + ': declared SHA-256 mismatch')
        item.update(sha256=actual, bytes=info[2], signature=info)
        del item['expected']

    expected = {}
    declarations = {}
    # The unchanged helper reads bounded private copies, so an original file growing
    # after preflight cannot bypass this process's memory budget. No user artifact is written.
    with tempfile.TemporaryDirectory(prefix='lookahead-input-snapshots-') as directory:
        snapshots = Path(directory)
        for role, endpoint in validation['endpoints'].items():
            source = data['endpoints'][role]
            local = snapshots/(role + '.txt')
            local.write_text(texts[Path(endpoint['file'])])
            legacy = {key: source[key] for key in ['node', 'connection', 'generation', 'capture']}
            legacy['file'] = str(local)
            if 'sourceMap' in source:
                source_map = snapshots/(role + '.src')
                source_map.write_text(texts[Path(endpoint['sourceMap'])])
                legacy.update(source=source['source'], sourceMap=str(source_map))
            # Existing endpoint/event code validates headers, grammar and map count/order.
            declaration, rows, _ = PAIR.endpoint(legacy, role, snapshots, 'LeiosNotifyP')
            declarations[role] = declaration.split()
            if 'sourceMap' not in source:
                # Its default coordinates refer to the original normalized file, not our copy.
                declarations[role][-1] = PAIR.token(endpoint['file'], role + ' source path')
            expected[role] = [(int(row.split(maxsplit=2)[1]), row.split(maxsplit=2)[2]) for row in rows]
    checker_path = Path(validation['checkerInput']['file'])
    lines = texts[checker_path].splitlines()
    mode = validation['profile']['mode']
    if mode == 'paired':
        header = ['pair', 'LeiosNotifyP', validation['connection'], validation['session']]
        PAIR.token(validation['connection'], 'connection')
        PAIR.token(validation['session'], 'session')
        if len(lines) < 3 or lines[0].split() != header:
            raise InputFailure('paired checker input header differs from the manifest')
        if lines[1].split() != declarations['client'] or lines[2].split() != declarations['server']:
            raise InputFailure('paired endpoint identity/generation/source declarations differ from endpoint artifacts')
        actual = {'client': [], 'server': []}
        for number, line in enumerate(lines[3:], 4):
            fields = line.split(maxsplit=2)
            if len(fields) != 3 or fields[0] not in actual or not fields[1].isascii() or not fields[1].isdigit():
                raise InputFailure(f'{checker_path}:{number}: expected role/source-line/event')
            actual[fields[0]].append((int(fields[1]), PAIR.event(fields[2], 'LeiosNotifyP')))
        if actual != expected:
            raise InputFailure('paired normalized rows/source coordinates differ from the endpoint artifacts')
    else:
        role = 'client' if mode == 'localclient' else 'server'
        if not lines or lines[0] != 'role ' + role:
            raise InputFailure('local checker input role differs from the explicit profile')
        actual = [PAIR.event(line, 'LeiosNotifyP') for line in lines[1:]]
        if actual != [event for _, event in expected[role]]:
            raise InputFailure('local normalized rows differ from the endpoint artifact')
    for path, item in files.items():
        if signature(path) != item['signature']:
            raise BudgetFailure(str(path) + ': changed during input validation')
    return list(files.values())


def terminate_group(process):
    """Kill a timed-out/over-budget process group and reap the explicitly launched checker."""
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def execute(argv, timeout, max_output_bytes):
    """Bound elapsed time and captured output, terminating children on an inconclusive run."""
    started = time.monotonic()
    process = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    selector = selectors.DefaultSelector()
    output = {'stdout': bytearray(), 'stderr': bytearray()}
    for stream, label in [(process.stdout, 'stdout'), (process.stderr, 'stderr')]:
        selector.register(stream, selectors.EVENT_READ, label)
    failure = None
    try:
        while selector.get_map():
            remaining = timeout - (time.monotonic() - started)
            if remaining <= 0:
                failure = 'checker-timeout'
                terminate_group(process)
                break
            for key, _ in selector.select(min(remaining, 0.1)):
                chunk = os.read(key.fileobj.fileno(), 65536)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                available = max_output_bytes - sum(map(len, output.values()))
                output[key.data].extend(chunk[:max(0, available)])
                if len(chunk) > available:
                    failure = 'checker-output-budget'
                    terminate_group(process)
                    break
            if failure:
                break
        if failure is None:
            remaining = timeout - (time.monotonic() - started)
            try:
                process.wait(timeout=max(0, remaining))
            except subprocess.TimeoutExpired:
                failure = 'checker-timeout'
                terminate_group(process)
    finally:
        if process.poll() is None:
            terminate_group(process)
        selector.close()
        process.stdout.close()
        process.stderr.close()
    return {'code': process.returncode, 'stdout': output['stdout'].decode('utf-8', errors='replace'),
            'stderr': output['stderr'].decode('utf-8', errors='replace'),
            'seconds': round(time.monotonic() - started, 3), 'failure': failure,
            'outputByteLimit': max_output_bytes}


def run_replay(checker, manifest, timeout=60, heap='512M', max_input_bytes=16777216):
    """Run only the explicit checker after schema/evidence/artifact validation; return report and exit class."""
    result = {'status': 'invalid-input', 'exitCode': 2, 'protocolVerdict': None,
              'manifestValidation': None, 'inputs': [], 'checker': None, 'errors': [],
              'limits': {'timeoutSeconds': timeout if isinstance(timeout, (int, float)) and math.isfinite(timeout) else None,
                         'heap': heap, 'maxInputBytes': max_input_bytes},
              'limitations': ['Capture freshness/order/losslessness and deployment provenance remain declarations.',
                  'Source-map coordinates and normalized rows are checked against declared artifacts; raw capture events are not reparsed or authenticated.',
                  'Protocol outcomes concern the selected fresh-prefix model profile, not node-policy or implementation conformance.']}
    try:
        if not isinstance(timeout, (int, float)) or isinstance(timeout, bool) or not math.isfinite(timeout) or timeout <= 0:
            raise InputFailure('timeout must be finite and positive')
        if not isinstance(heap, str) or not re.fullmatch(r'[1-9][0-9]*[KMG]', heap):
            raise InputFailure('heap must be a positive K/M/G limit, for example 512M')
        if type(max_input_bytes) is not int or max_input_bytes <= 0:
            raise InputFailure('max-input-bytes must be a positive integer')
        manifest = Path(manifest).resolve()
        manifest_info = signature(manifest)
        if manifest_info[2] > max_input_bytes:
            raise BudgetFailure('manifest exceeds input byte budget')
        raw, manifest_info = bounded_bytes(manifest, max_input_bytes)
        data = json.loads(raw.decode('utf-8'), object_pairs_hook=MANIFEST.unique_keys,
                          parse_constant=MANIFEST.reject_constant)
        validation = MANIFEST.validate_manifest(data, manifest.parent)
        validation['manifest'] = str(manifest)
        validation['manifestSha256'] = hashlib.sha256(raw).hexdigest()
        result['manifestValidation'] = validation
        if validation['status'] != 'ready':
            result.update(status=validation['status'], exitCode={'invalid-input': 2, 'missing-capture-evidence': 3}[validation['status']])
            return result, result['exitCode']
        result['inputs'] = check_inputs(validation, data, max_input_bytes)
        checker = Path(checker).resolve()
        binary_hash, binary_info = sha256_file(checker)
        if not os.access(checker, os.X_OK):
            raise InputFailure('explicit checker is not executable')
        argv = [str(checker), *validation['checkerArguments'], '+RTS', '-M' + heap, '-RTS']
        result['checker'] = {'path': str(checker), 'sha256': binary_hash, 'arguments': argv[1:]}
        execution = execute(argv, timeout, max(1048576, 2*max_input_bytes))
        result['checker'].update(execution)
        if execution['failure']:
            raise BudgetFailure(execution['failure'])
        if signature(manifest) != manifest_info or signature(checker) != binary_info:
            raise BudgetFailure('manifest or checker changed during the run')
        for item in result['inputs']:
            if signature(Path(item['path'])) != item['signature']:
                raise BudgetFailure(item['path'] + ': input changed during the run')
        first = execution['stdout'].splitlines()
        matched = re.match(r'^(accepted-prefix|protocol-rejected|invalid-input|undetermined)(?=$|[:\s])', first[0]) if first else None
        tag = matched.group(1) if matched else None
        expected = {0: 'accepted-prefix', 1: 'protocol-rejected', 2: 'invalid-input'}
        if validation['profile']['observation'] == MANIFEST.SILENCED_OBSERVATION:
            # Only the silenced paired checker may be undetermined; it is inconclusive, never a rejection.
            expected[3] = 'undetermined'
        if expected.get(execution['code']) != tag or execution['code'] not in expected:
            result.update(status='checker-inconclusive', exitCode=4)
            result['errors'].append('checker exit code and first-line verdict tag do not agree')
        elif execution['code'] == 0:
            result.update(status='accepted-prefix', protocolVerdict='accepted-prefix', exitCode=0)
        elif execution['code'] == 1:
            result.update(status='protocol-rejected', protocolVerdict='protocol-rejected', exitCode=1)
        elif execution['code'] == 3:
            result.update(status='model-undetermined', exitCode=4)
        else:
            result.update(status='invalid-input', exitCode=2)
    except BudgetFailure as exc:
        result.update(status='resource-inconclusive', exitCode=4)
        result['errors'].append(str(exc))
    except (OSError, UnicodeError, ValueError, TypeError) as exc:
        result['errors'].append(str(exc))
        # Invocation failures cannot be mistaken for a rejected protocol trace.
        result.update(status='checker-inconclusive' if result['checker'] else 'invalid-input',
                      exitCode=4 if result['checker'] else 2)
    return result, result['exitCode']


def selftest():
    """Exercise the coordinator with explicit fake checkers; this is not actual Agda replay evidence."""
    cases = 0
    with tempfile.TemporaryDirectory(prefix='lookahead-runner-') as directory:
        base = Path(directory)
        binary = base/'fake-checker'
        manifest = base/'manifest.json'

        def assemble_pair(data):
            declarations, rows = [], []
            for role in ['client', 'server']:
                ep = data['endpoints'][role]
                legacy = {key: ep[key] for key in ['node','connection','generation','capture','file']}
                for key in ['source', 'sourceMap']:
                    if key in ep:
                        legacy[key] = ep[key]
                declaration, events, _ = PAIR.endpoint(legacy, role, base, 'LeiosNotifyP')
                declarations.append(declaration)
                rows.extend(events)
            (base/'pair.txt').write_text('\n'.join(['pair LeiosNotifyP example-AB example-0', *declarations, *rows]) + '\n')

        def prepare(mode='paired'):
            data = MANIFEST.example_manifest(mode)
            for role in data['endpoints']:
                (base/(role + '.txt')).write_text('role ' + role + '\n' +
                    ('Send RequestNext\nRecv Votes 11:23,1f:37,11:23\n' if role == 'client' else
                     'Recv RequestNext\nSend Votes 11:23,1f:37,11:23\n'))
            if mode == 'paired':
                assemble_pair(data)
            manifest.write_text(json.dumps(data))
            return data

        def fake(text, code=0):
            binary.write_text('#!' + sys.executable + '\nimport sys\nprint(' + repr(text) + ')\nsys.exit(' + str(code) + ')\n')
            binary.chmod(0o700)

        def run(expected, **kwargs):
            nonlocal cases
            report, code = run_replay(binary, manifest, **kwargs)
            assert code == expected, report
            if expected not in (0,1):
                assert report['protocolVerdict'] is None, report
            cases += 1
            return report

        for mode in ['localclient', 'localserver', 'paired']:
            prepare(mode); fake('accepted-prefix: fake-only')
            r = run(0)
            assert r['checker']['sha256'] and r['inputs']
        fake('protocol-rejected: fake-only', 1); run(1)
        fake('invalid-input: fake-only', 2); run(2)
        fake('protocol-rejected: mismatched code', 0); run(4)
        fake('accepted-prefix: mismatched code', 1); run(4)
        fake('protocol-rejected: crash', 137); run(4)
        fake('', 1); run(4)
        fake('unrecognized', 0); run(4)
        fake(':', 0); run(4)
        data = prepare(); data['endpoints']['client'].pop('capture'); manifest.write_text(json.dumps(data)); run(3)
        data = prepare(); data['depth']=4; manifest.write_text(json.dumps(data)); run(2)
        prepare(); fake('accepted-prefix: fake-only'); run(4, max_input_bytes=1)
        data=prepare(); data['checkerInput']['sha256']='0'*64; manifest.write_text(json.dumps(data)); run(2)
        data=prepare(); (base/'client.txt').write_text('role server\n'); run(2)
        prepare(); (base/'pair.txt').write_text((base/'pair.txt').read_text().replace('example-client','wrong-client')); run(2)
        prepare(); (base/'pair.txt').write_text((base/'pair.txt').read_text().replace('11:23,1f:37,11:23','11:23',1)); run(2)
        prepare(); lines=(base/'pair.txt').read_text().splitlines()
        (base/'pair.txt').write_text('\n'.join(lines[:3]+[lines[5],lines[3],lines[6],lines[4]])+'\n')
        fake('accepted-prefix: fake-only'); run(0)
        data=prepare()
        for role, endpoint in data['endpoints'].items():
            raw_path=base/(role+'.log'); raw_path.write_bytes(b'raw-capture-context\n'*10000)
            (base/(role+'.src')).write_text('101 original-time\n109 original-time\n')
            endpoint.update(source=role+'.log',sourceMap=role+'.src',sourceSha256=sha256_file(raw_path)[0])
        assemble_pair(data); manifest.write_text(json.dumps(data)); r=run(0,max_input_bytes=4096)
        assert len([item for item in r['inputs'] if not item['bounded'] and item['bytes']>4096])==2
        (base/'pair.txt').write_text((base/'pair.txt').read_text().replace('client 101 ', 'client 100 ')); run(2)
        assemble_pair(data); data['endpoints']['client']['sourceSha256']='0'*64
        manifest.write_text(json.dumps(data)); run(2)
        data['endpoints']['client']['sourceSha256']=sha256_file(base/'client.log')[0]
        manifest.write_text(json.dumps(data)); (base/'client.src').write_text('101 only-one-row\n'); run(2)
        prepare(); binary.write_text('#!' + sys.executable + '\nprint("x"*1048577)\n'); binary.chmod(0o700)
        run(4,max_input_bytes=4096)
        prepare(); binary.write_text('#!' + sys.executable + '\nimport time\ntime.sleep(30)\n'); binary.chmod(0o700); run(4, timeout=0.1)
        prepare(); fake('accepted-prefix: fake-only'); run(2, heap='512M -RTS')
        prepare(); binary.chmod(0o600); run(2)
        # The undetermined tag is accepted only for the silenced observation, and only as exit class 4.
        prepare(); fake('undetermined: fake-only', 3); r = run(4)
        assert r['status'] == 'checker-inconclusive', r
        for mode in ['localclient', 'localserver', 'paired']:
            data = prepare(mode); data['observation'] = MANIFEST.SILENCED_OBSERVATION; manifest.write_text(json.dumps(data))
            fake('accepted-prefix: fake-only'); r = run(0)
            assert r['checker']['arguments'][-6:-4] == ['--observation', MANIFEST.SILENCED_OBSERVATION], r
        fake('undetermined: fake-only', 3); r = run(4)
        assert r['status'] == 'model-undetermined' and r['protocolVerdict'] is None, r
        fake('undetermined: mismatched code', 1); r = run(4)
        assert r['status'] == 'checker-inconclusive', r
        fake('protocol-rejected: fake-only', 3); r = run(4)
        assert r['status'] == 'checker-inconclusive', r
    return {'selftest':'passed','cases':cases,'checker':'explicit fake executables only; no actual Agda replay or binary smoke test'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path)
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--timeout', type=float, default=60)
    parser.add_argument('--heap', default='512M')
    parser.add_argument('--max-input-bytes', type=int, default=16777216)
    parser.add_argument('--selftest', action='store_true')
    args = parser.parse_args()
    if args.selftest:
        if args.checker or args.manifest:
            parser.error('--selftest cannot execute a supplied checker or manifest')
        print(json.dumps(selftest(), indent=2))
        return
    if not args.checker or not args.manifest:
        parser.error('--checker and --manifest are required')
    report, code = run_replay(args.checker, args.manifest, args.timeout, args.heap, args.max_input_bytes)
    print(json.dumps(report, indent=2))
    raise SystemExit(code)


if __name__ == '__main__':
    main()
