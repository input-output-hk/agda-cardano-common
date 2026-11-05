#!/usr/bin/env python3
"""Rederive declared endpoint artifacts from raw JSON before bounded model replay.

Raw correspondence is an executable check of the supplied files and selectors.
It does not establish logger fidelity, freshness, pairing or deployed conformance.
The existing replay manifest schema and normalized runner remain unchanged.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def module_at(name, path):
    """Import fixed repository helpers; never load code named by an input file."""
    import importlib.util
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


RUNNER = module_at('raw_replay_runner', HERE / 'replay_lookahead.py')
VERSION = 'leiosnotify-lookahead-raw-bindings-v1'


def signature(path):
    """Include ctime when detecting changes across verification and execution."""
    RUNNER.signature(path)
    info = path.stat()
    return [info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns,
            info.st_ctime_ns]


def document(path, limit):
    """Read bounded strict JSON and retain its exact identity."""
    def finite_float(text):
        value = float(text)
        if not math.isfinite(value):
            raise RUNNER.InputFailure('JSON number exceeds finite range')
        return value

    before = signature(path)
    raw, _ = RUNNER.bounded_bytes(path, limit)
    try:
        data = json.loads(raw.decode('utf-8'),
                          object_pairs_hook=RUNNER.MANIFEST.unique_keys,
                          parse_constant=RUNNER.MANIFEST.reject_constant,
                          parse_float=finite_float)
    except RecursionError as exc:
        raise RUNNER.InputFailure(str(path) + ': JSON nesting exceeds parser limit') from exc
    if signature(path) != before:
        raise RUNNER.BudgetFailure(str(path) + ': changed during JSON read')
    return data, {'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
                  'bytes': len(raw), 'signature': before}


def fields(value, required, label):
    """Reject incomplete or ambiguous raw-binding declarations."""
    if not isinstance(value, dict) or set(value) != required:
        raise RUNNER.InputFailure(label + ': expected keys ' +
                                  ', '.join(sorted(required)))


def unchanged(watched, phase):
    """Disappearance or mutation after verification makes execution inconclusive."""
    for path, original in watched.items():
        try:
            current = signature(path)
        except OSError as exc:
            raise RUNNER.BudgetFailure(str(path) + ': unavailable ' + phase) from exc
        if current != original:
            raise RUNNER.BudgetFailure(str(path) + ': changed ' + phase)


def bindings_for(data, validation, base):
    """Bind raw selectors/maps to the exact endpoint files in the manifest."""
    fields(data, {'version', 'endpoints'}, 'raw bindings')
    if data['version'] != VERSION:
        raise RUNNER.InputFailure('unsupported raw bindings version')
    roles = set(validation['endpoints'])
    fields(data['endpoints'], roles, 'raw binding endpoints')
    selections = {}
    for role, endpoint in validation['endpoints'].items():
        binding = data['endpoints'][role]
        fields(binding, {'selector', 'detailedMap'}, role + ' raw binding')
        selector = binding['selector']
        fields(selector, {'host', 'connection', 'role', 'observedMuxGeneration',
                          'segmentAfterDone'}, role + ' selector')
        if selector['role'] != role:
            raise RUNNER.InputFailure(role + ': raw selector role mismatch')
        if not endpoint['source'] or not endpoint['sourceMap']:
            raise RUNNER.InputFailure(role + ': raw replay requires source and sourceMap')
        name = binding['detailedMap']
        if not isinstance(name, str) or not name.strip() or name != name.strip():
            raise RUNNER.InputFailure(role + ': detailedMap must name a file')
        selections[role] = {
            'raw': Path(endpoint['source']),
            'normalized': Path(endpoint['file']),
            'sourceMap': Path(endpoint['sourceMap']),
            'detailedMap': (base / name).resolve(), 'selector': selector}
    return selections


def run_raw_replay(checker, manifest, raw_bindings, *, timeout=60, heap='512M',
                   max_input_bytes=16777216, raw_limits=None):
    """Verify raw/artifact correspondence, then use the unchanged model runner."""
    result = {
        'status': 'invalid-input', 'exitCode': 2, 'protocolVerdict': None,
        'rawCorrespondence': {}, 'replay': None, 'errors': [],
        'limitations': [
            'Raw JSON correspondence is executable evidence, not an Agda logger refinement proof.',
            'Freshness/order/losslessness, endpoint pairing and deployed provenance remain declarations.',
            'Only the selected normalized summary fields are checked; unlogged native fields are unknown.',
            'File change checks are not authentication or a filesystem transaction.',
            'EOF is a model prefix, not successful whole-node completion.']}
    raw = None
    try:
        if type(max_input_bytes) is not int or max_input_bytes <= 0:
            raise RUNNER.InputFailure('max-input-bytes must be a positive integer')
        if (isinstance(timeout, bool) or not isinstance(timeout, (int, float)) or
                not math.isfinite(timeout) or timeout <= 0):
            raise RUNNER.InputFailure('timeout must be finite and positive')
        manifest = Path(manifest).resolve()
        raw_bindings = Path(raw_bindings).resolve()
        data, manifest_identity = document(manifest, max_input_bytes)
        validation = RUNNER.MANIFEST.validate_manifest(data, manifest.parent)
        result['manifestValidation'] = validation
        if validation['status'] != 'ready':
            result.update(status=validation['status'],
                          exitCode=3 if validation['status'] == 'missing-capture-evidence' else 2)
            return result, result['exitCode']
        declared, bindings_identity = document(raw_bindings, max_input_bytes)
        selections = bindings_for(declared, validation, raw_bindings.parent)
        result['manifest'] = manifest_identity
        result['rawBindings'] = bindings_identity
        watched = {manifest: manifest_identity['signature'],
                   raw_bindings: bindings_identity['signature']}
        metadata = {manifest, raw_bindings,
                    Path(validation['checkerInput']['file'])}
        for selected in selections.values():
            for key in ['raw', 'normalized', 'sourceMap', 'detailedMap']:
                path = selected[key]
                watched.setdefault(path, signature(path))
                if key != 'raw':
                    metadata.add(path)
        watched.setdefault(Path(validation['checkerInput']['file']),
                           signature(Path(validation['checkerInput']['file'])))
        if sum(signature(path)[2] for path in metadata) > max_input_bytes:
            raise RUNNER.BudgetFailure('aggregate manifests/normalized/maps exceed input byte budget')
        raw = module_at('lookahead_raw_correspondence',
                        HERE / 'raw-input' / 'lookahead_raw.py')
        for role, selected in selections.items():
            verified = raw.verify_selected(
                selected['raw'], selected['selector'], selected['normalized'],
                selected['sourceMap'], selected['detailedMap'], limits=raw_limits)
            if (verified.get('status') != 'correspondence-checked' or
                    verified.get('protocolVerdict') is not None):
                raise RUNNER.BudgetFailure('unexpected raw correspondence result')
            result['rawCorrespondence'][role] = verified
        unchanged(watched, 'during raw verification')
        replay, code = RUNNER.run_replay(checker, manifest, timeout, heap,
                                         max_input_bytes)
        result['replay'] = replay
        unchanged(watched, 'between raw verification and replay')
        result.update(status=replay['status'], exitCode=code,
                      protocolVerdict=replay['protocolVerdict'])
    except (RUNNER.BudgetFailure, MemoryError) as exc:
        result.update(status='resource-inconclusive', exitCode=4)
        result['errors'].append(str(exc) or 'memory allocation failed during raw replay')
    except (OSError, UnicodeError, ValueError, TypeError) as exc:
        limited = raw is not None and isinstance(exc, raw.ResourceLimitError)
        result.update(status='resource-inconclusive' if limited else 'invalid-input',
                      exitCode=4 if limited else 2)
        result['errors'].append(str(exc))
    return result, result['exitCode']


def main():
    """Keep raw correspondence opt-in and outside the existing manifest schema."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', required=True, type=Path)
    parser.add_argument('--manifest', required=True, type=Path)
    parser.add_argument('--raw-bindings', required=True, type=Path)
    parser.add_argument('--timeout', type=float, default=60,
                        help='checker execution seconds; raw scans have their own limits')
    parser.add_argument('--heap', default='512M')
    parser.add_argument('--max-input-bytes', type=int, default=16777216)
    parser.add_argument('--max-raw-bytes', type=int, default=17179869184)
    parser.add_argument('--max-raw-records', type=int, default=10000000)
    parser.add_argument('--max-raw-seconds', type=float, default=300)
    args = parser.parse_args()
    report, code = run_raw_replay(
        args.checker, args.manifest, args.raw_bindings, timeout=args.timeout,
        heap=args.heap, max_input_bytes=args.max_input_bytes,
        raw_limits={'max_raw_bytes': args.max_raw_bytes,
                    'max_records': args.max_raw_records,
                    'max_seconds': args.max_raw_seconds,
                    'max_artifact_bytes': args.max_input_bytes})
    print(json.dumps(report, indent=2))
    raise SystemExit(code)


if __name__ == '__main__':
    main()
