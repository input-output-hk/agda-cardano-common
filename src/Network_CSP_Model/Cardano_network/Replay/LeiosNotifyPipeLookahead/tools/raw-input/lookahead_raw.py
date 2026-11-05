#!/usr/bin/env python3
"""Bounded raw Notify normalization and executable artifact correspondence.

This checks a documented raw JSON schema and exact retained summaries. It does
not certify logger completeness, deployment identity or implementation refinement.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import shutil
import stat
import sys
import tempfile
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def module_at(name, path):
    """Reuse repository normalizers rather than introduce another message syntax."""
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


NORMAL = module_at('lookahead_raw_normal', HERE.parents[2]/'LogProcessing/normalize_logs.py')
PAIR = module_at('lookahead_raw_pair', HERE.parents[2]/'LogProcessing/paired_sessions.py')
DEFAULT_LIMITS = dict(max_line_bytes=1048576, max_raw_bytes=17179869184,
    max_records=10000000, max_states=100000, max_metadata_bytes=16777216, max_seconds=300,
    max_artifact_bytes=16777216)
SELECTOR_KEYS = {'host', 'connection', 'role', 'observedMuxGeneration', 'segmentAfterDone'}
MAP_VERSION = 'leiosnotify-raw-map-v1'


class RawInputError(ValueError):
    """Invalid input/correspondence is not a protocol rejection."""


class ResourceLimitError(RawInputError):
    """A bound or changing artifact prevents a complete correspondence result."""


def limits_with(overrides=None):
    """Bound each line, whole scan, lifecycle state and retained output separately."""
    if overrides is not None and not isinstance(overrides, dict):
        raise RawInputError('limits must be an object')
    limits = dict(DEFAULT_LIMITS)
    if overrides:
        if set(overrides)-set(limits):
            raise RawInputError('unknown limit keys')
        limits.update(overrides)
    for name, value in limits.items():
        if isinstance(value, bool) or not isinstance(value, (int, float)) or value <= 0:
            raise RawInputError(name + ' must be positive')
        if name == 'max_seconds':
            try:
                finite = math.isfinite(value)
            except OverflowError:
                finite = False
            if not finite:
                raise RawInputError('max_seconds must be finite')
        elif not isinstance(value, int):
            raise RawInputError(name + ' must be an integer')
    return limits


def file_signature(path):
    """Bind regular-file identity as well as size and modification metadata."""
    value = Path(path).stat()
    if not stat.S_ISREG(value.st_mode):
        raise RawInputError(str(path) + ': expected regular file')
    return [value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns, value.st_ctime_ns]


def unique_pairs(pairs):
    """Duplicate JSON keys cannot silently replace an observed field."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise RawInputError('duplicate JSON key: ' + key)
        result[key] = value
    return result


def strict_json(text):
    """Reject non-finite numbers and duplicate keys at every nesting level."""
    def nonfinite(value):
        raise RawInputError('non-JSON number: ' + value)
    def finite_float(value):
        number = float(value)
        if not math.isfinite(number):
            raise RawInputError('non-finite JSON numeric value')
        return number
    try:
        return json.loads(text, object_pairs_hook=unique_pairs,
                          parse_constant=nonfinite, parse_float=finite_float)
    except (ValueError, RecursionError) as error:
        raise RawInputError(str(error)) from error


def record_object(raw):
    """Support node JSON, journal prefixes and one supervisor message wrapper."""
    try:
        text = raw.decode('utf-8')
    except UnicodeDecodeError as error:
        raise RawInputError('raw line is not UTF-8') from error
    if not text.strip():
        return None
    start = text.find('{')
    if start < 0:
        raise RawInputError('expected structured JSON record')
    obj = strict_json(text[start:])
    if not isinstance(obj, dict):
        raise RawInputError('expected JSON object')
    if 'ns' not in obj:
        obj = obj.get('message')
        if isinstance(obj, str):
            start = obj.find('{')
            if start < 0:
                raise RawInputError('supervisor message has no JSON record')
            obj = strict_json(obj[start:])
    if not isinstance(obj, dict) or not isinstance(obj.get('ns'), str):
        raise RawInputError('expected string ns in node record or supervisor message')
    return obj


def literal_connection(data):
    """Retain literal socket spellings; do not infer NAT or endpoint equivalence."""
    found = []
    for parent in [data, data.get('peer'), data.get('bearer')]:
        if isinstance(parent, dict) and 'connectionId' in parent:
            value = parent['connectionId']
            if isinstance(value, dict):
                def endpoint(item):
                    if not isinstance(item, dict):
                        raise RawInputError('structured connection endpoint must be an object')
                    host, port = item.get('address', item.get('addr')), item.get('port')
                    if not isinstance(host, str) or not host or isinstance(port, bool):
                        raise RawInputError('structured connection needs address and port')
                    if not isinstance(port, (str, int)) or not str(port).isascii() or not str(port).isdigit() or not 0 <= int(port) <= 65535:
                        raise RawInputError('invalid structured connection port')
                    return ('['+host+']' if ':' in host and not host.startswith('[') else host)+':'+str(port)
                if not {'localAddress','remoteAddress'} <= set(value):
                    raise RawInputError('structured connection needs both endpoints')
                value = endpoint(value['localAddress'])+' '+endpoint(value['remoteAddress'])
            if not isinstance(value, str) or value.strip() != value or len(value.split()) != 2 or any(c in value for c in '\r\n\t'):
                raise RawInputError('connectionId must contain literal local and remote endpoints')
            found.append(value)
    if not found or len(set(found)) != 1:
        raise RawInputError('missing or contradictory connectionId')
    return found[0]


def validate_selector(selector):
    """Selection is explicit and never supplies a fresh-state assertion."""
    if not isinstance(selector, dict) or set(selector) != SELECTOR_KEYS:
        raise RawInputError('selector requires exactly '+', '.join(sorted(SELECTOR_KEYS)))
    for key in ['host', 'connection']:
        value = selector[key]
        if not isinstance(value, str) or not value or value.strip() != value or any(c in value for c in '\r\n\t'):
            raise RawInputError('selector '+key+' must be a nonempty literal string')
    if selector['role'] not in ['client', 'server']:
        raise RawInputError('selector role must be client or server')
    for key in ['observedMuxGeneration', 'segmentAfterDone']:
        if type(selector[key]) is not int or selector[key] < 0:
            raise RawInputError('selector '+key+' must be a natural number')
    return dict(selector)


def canonical_notify(obj):
    """Validate raw agency and all retained fields before using existing encoding."""
    ns = obj['ns']
    suffix = ns[len(NORMAL.LN):]
    if suffix not in NORMAL.NOTIFY_KINDS:
        raise RawInputError('unsupported Notify namespace '+ns)
    role, direction, kind = NORMAL.NOTIFY_KINDS[suffix]
    data = obj.get('data')
    if not isinstance(data, dict) or data.get('kind') != direction:
        raise RawInputError('Notify namespace/data direction mismatch')
    msg = data.get('msg')
    expected = 'MsgLeiosNotificationRequestNext' if kind == 'RequestNext' else ('Msg'+kind if kind in ['Quit','Canceled','Done'] else 'MsgLeios'+kind)
    if not isinstance(msg, dict) or msg.get('kind') != expected:
        raise RawInputError('Notify namespace/message kind mismatch')
    try:
        for key in ['ebHash']:
            if key in msg and (not isinstance(msg[key], str) or not re.fullmatch('[0-9a-fA-F]+', msg[key])):
                raise RawInputError('invalid hex field '+key)
        if kind == 'Votes':
            if not isinstance(msg.get('votes'), list):
                raise RawInputError('votes must be a list')
            for vote in msg['votes']:
                if not isinstance(vote, dict) or not isinstance(vote.get('rbHash'), str) or not re.fullmatch('[0-9a-fA-F]+', vote['rbHash']):
                    raise RawInputError('invalid vote hash or record')
                NORMAL.n(vote['voterId'])
        event = NORMAL.normalize_notify(direction, kind, msg)
        event = PAIR.event(event, 'LeiosNotifyP')
    except (KeyError, ValueError, TypeError, AttributeError) as error:
        raise RawInputError('invalid Notify summary: '+str(error)) from error
    return role, direction, kind, event


class RawScan:
    """One bounded streaming scan; summary becomes available only after EOF."""
    def __init__(self, path, limits=None):
        self.path = Path(path).resolve()
        self.limits = limits_with(limits)
        self.summary = None
        self.used = False

    def __iter__(self):
        if self.used:
            raise RawInputError('a RawScan can be consumed only once')
        self.used = True
        before = file_signature(self.path)
        if before[2] > self.limits['max_raw_bytes']:
            raise ResourceLimitError('raw byte budget exceeded')
        started, digest, offset, number = time.monotonic(), hashlib.sha256(), 0, 0
        generations, segments, counts, metadata_bytes = {}, {}, Counter(), 0
        with self.path.open('rb') as stream:
            while True:
                if time.monotonic()-started > self.limits['max_seconds']:
                    raise ResourceLimitError('raw scan time budget exceeded')
                raw = stream.readline(self.limits['max_line_bytes']+1)
                if not raw:
                    break
                number += 1
                if number > self.limits['max_records']:
                    raise ResourceLimitError('raw record budget exceeded')
                if len(raw) > self.limits['max_line_bytes']:
                    raise ResourceLimitError('raw line byte budget exceeded at line '+str(number))
                if offset+len(raw) > self.limits['max_raw_bytes']:
                    raise ResourceLimitError('raw byte budget exceeded')
                digest.update(raw)
                here = offset
                offset += len(raw)
                try:
                    obj = record_object(raw)
                    if obj is None:
                        counts['blankLines'] += 1
                        continue
                    counts['jsonRecords'] += 1
                    ns = obj['ns']
                    if ns != 'Net.Mux.Remote.NewMux' and ns != NORMAL.LN[:-1] and not ns.startswith(NORMAL.LN):
                        counts['otherRecords'] += 1
                        continue
                    if ns.startswith(NORMAL.LN+'Serialised.'):
                        counts['serialisedObservationsExcluded'] += 1
                        continue
                    host, data = obj.get('host'), obj.get('data')
                    if not isinstance(host, str) or not host or host.strip() != host or any(c in host for c in '\r\n\t') or not isinstance(data, dict):
                        raise RawInputError('Notify/NewMux requires host and data object')
                    connection = literal_connection(data)
                    key = host, connection
                    if key not in generations:
                        if len(generations)+len(segments) >= self.limits['max_states']:
                            raise ResourceLimitError('lifecycle state budget exceeded')
                        metadata_bytes += len(host.encode())+len(connection.encode())+64
                        if metadata_bytes > self.limits['max_metadata_bytes']:
                            raise ResourceLimitError('lifecycle metadata byte budget exceeded')
                        generations[key] = [0, None]
                    if ns == 'Net.Mux.Remote.NewMux':
                        generations[key][0] += 1
                        generations[key][1] = dict(line=number, byteOffset=here)
                        counts['newMuxRecords'] += 1
                        continue
                    role, direction, kind, event = canonical_notify(obj)
                    at = obj.get('at')
                    if not isinstance(at, str) or not at or len(at.split()) != 1 or at.strip() != at:
                        raise RawInputError('Notify requires a single-token timestamp string')
                    threads = {}
                    for prefix, source in [('', obj), ('data.', data)]:
                        for field in ['thread', 'threadId', 'thread_id']:
                            if field in source:
                                value = source[field]
                                if isinstance(value, bool) or not isinstance(value, (str,int)) or not str(value).strip():
                                    raise RawInputError('thread metadata must be a nonempty string or integer')
                                threads[prefix+field] = value
                    generation, boundary = generations[key]
                    skey = key+(generation,role)
                    if skey not in segments:
                        if len(generations)+len(segments) >= self.limits['max_states']:
                            raise ResourceLimitError('lifecycle state budget exceeded')
                        metadata_bytes += len(host.encode())+len(connection.encode())+len(role)+64
                        if metadata_bytes > self.limits['max_metadata_bytes']:
                            raise ResourceLimitError('lifecycle metadata byte budget exceeded')
                        segments[skey] = 0
                    row = dict(version=MAP_VERSION, sourceFile=str(self.path), line=number,
                        byteOffset=here, byteLength=len(raw), rawLineSha256=hashlib.sha256(raw).hexdigest(),
                        namespace=ns, kind=kind, direction=direction, event=event, host=host,
                        connection=connection, role=role, observedMuxGeneration=generation,
                        segmentAfterDone=segments[skey], precedingNewMux=boundary,
                        at=at, threads=threads)
                    counts['notifyRecords'] += 1
                    counts['withoutThreadMetadata'] += int(not threads)
                    if kind == 'Done':
                        segments[skey] += 1
                    yield row
                except ResourceLimitError:
                    raise
                except RawInputError as error:
                    raise RawInputError(f'{self.path}:{number} byte {here}: {error}') from error
        if file_signature(self.path) != before or offset != before[2]:
            raise ResourceLimitError('raw capture changed during scan')
        self.summary = dict(path=str(self.path),sha256=digest.hexdigest(),bytes=offset,
            signature=before,lines=number,counts=dict(sorted(counts.items())),
            lifecycleStates=len(generations)+len(segments),lifecycleMetadataBytes=metadata_bytes)


def scan_raw(path, *, limits=None):
    """Return a strict iterable shared by preflight and correspondence checks."""
    return RawScan(path, limits)


def selected_rows(scan, selector):
    """Apply endpoint selection only after each Notify record passes validation."""
    for row in scan:
        if all(row[key] == value for key, value in selector.items()):
            yield row


def compact_json(value):
    """Canonical map serialization preserves every exact observed row position."""
    return json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=True)+'\n'


def summary_report(scan, selector, rows, artifacts):
    """State the executable correspondence scope without elevating capture claims."""
    return dict(version='leiosnotify-raw-correspondence-v1',status='correspondence-checked',
        protocolVerdict=None,selector=selector,rows=rows,raw=scan.summary,artifacts=artifacts,
        limits=scan.limits,limitations=[
            'Supported JSON envelope and retained summary fields only; not full native body/header/signature fidelity.',
            'Observed NewMux generations and Done segments are coordinates, not proof of freshness or lossless capture.',
            'No pairing, NAT/DNS mapping, deployment identity, causal timestamp merge or protocol verdict is inferred.',
            'Executable rederivation checks artifacts against these raw bytes; Python and logger correspondence remain trust boundaries.'])


def artifact_info(path, maximum):
    """Hash a bounded regular artifact without retaining its contents."""
    path = Path(path).resolve()
    before = file_signature(path)
    if before[2] > maximum:
        raise ResourceLimitError('artifact byte budget exceeded')
    digest, length = hashlib.sha256(), 0
    with path.open('rb') as stream:
        for raw in iter(lambda:stream.read(65536),b''):
            length += len(raw)
            if length > maximum:
                raise ResourceLimitError('artifact byte budget exceeded')
            digest.update(raw)
    if file_signature(path) != before or length != before[2]:
        raise ResourceLimitError('artifact changed while hashing')
    return dict(path=str(path),sha256=digest.hexdigest(),bytes=length,signature=before)


def normalize_selected(raw_path, selector, output_dir, *, limits=None):
    """Publish a fresh local session and exact coordinate maps only after a full scan."""
    selector, limits = validate_selector(selector), limits_with(limits)
    out = Path(output_dir).resolve()
    if out.exists():
        raise RawInputError('output directory must be new')
    if not out.parent.is_dir():
        raise RawInputError('output parent directory must exist')
    work = Path(tempfile.mkdtemp(prefix='.'+out.name+'.',dir=out.parent))
    scan, count, total = scan_raw(raw_path,limits=limits), 0, 0
    try:
        with (work/'local.txt').open('wb') as local, (work/'local.src').open('wb') as source, (work/'map.jsonl').open('wb') as mapping:
            header = ('role '+selector['role']+'\n').encode()
            local.write(header); total += len(header)
            for row in selected_rows(scan,selector):
                chunks = [(row['event']+'\n').encode(), (str(row['line'])+' '+row['at']+'\n').encode(), compact_json(row).encode()]
                total += sum(map(len,chunks))
                if total > limits['max_artifact_bytes']:
                    raise ResourceLimitError('aggregate output artifact budget exceeded')
                for stream,chunk in zip([local,source,mapping],chunks):
                    stream.write(chunk)
                count += 1
        if not count:
            raise RawInputError('selector matched no Notify rows')
        if file_signature(scan.path) != scan.summary['signature']:
            raise ResourceLimitError('raw capture changed before output publication')
        (work/'selector.json').write_text(json.dumps(selector,indent=2)+'\n')
        # The selected outputs are small enough by construction; retaining their
        # signatures after publication also binds the final paths used by callers.
        os.rename(work,out)
        artifacts = {name:artifact_info(out/name,limits['max_artifact_bytes']) for name in ['local.txt','local.src','map.jsonl']}
        return summary_report(scan,selector,count,artifacts)
    except BaseException:
        shutil.rmtree(work,ignore_errors=True)
        raise


def verify_selected(raw_path, selector, normalized_path, source_map_path, detailed_map_path, *, limits=None):
    """Rederive every selected event and coordinate from raw bytes and compare all artifacts."""
    selector, limits = validate_selector(selector), limits_with(limits)
    paths = [Path(p).resolve() for p in [normalized_path,source_map_path,detailed_map_path]]
    infos = {name:artifact_info(path,limits['max_artifact_bytes']) for name,path in zip(['normalized','sourceMap','detailedMap'],paths)}
    if sum(item['bytes'] for item in infos.values()) > limits['max_artifact_bytes']:
        raise ResourceLimitError('aggregate artifact byte budget exceeded')
    count, scan = 0, scan_raw(raw_path,limits=limits)
    with paths[0].open('rb') as local, paths[1].open('rb') as source, paths[2].open('rb') as mapping:
        if local.readline(limits['max_line_bytes']+1) != ('role '+selector['role']+'\n').encode():
            raise RawInputError('normalized role header differs from selector')
        for row in selected_rows(scan,selector):
            count += 1
            expected = [(row['event']+'\n').encode(),(str(row['line'])+' '+row['at']+'\n').encode(),compact_json(row).encode()]
            # Detailed metadata can expand the original envelope, but remains
            # bounded by the aggregate artifact limit even for one large vote list.
            for label,stream,want in zip(['normalized','source map','detailed map'],[local,source,mapping],expected):
                got = stream.readline(limits['max_artifact_bytes']+1)
                if got != want:
                    raise RawInputError(f'{label} differs from raw rederivation at selected row {count}, raw line {row["line"]}')
        if not count:
            raise RawInputError('selector matched no Notify rows')
        if any(stream.read(1) for stream in [local,source,mapping]):
            raise RawInputError('artifact contains additional rows absent from selected raw input')
    for item in infos.values():
        if file_signature(item['path']) != item['signature']:
            raise ResourceLimitError('artifact changed during correspondence verification')
    if file_signature(scan.path) != scan.summary['signature']:
        raise ResourceLimitError('raw capture changed during artifact comparison')
    return summary_report(scan,selector,count,infos)


def main():
    """Normalize one explicitly selected endpoint, or verify supplied artifacts."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command',choices=['normalize','verify'])
    parser.add_argument('--raw',required=True,type=Path)
    parser.add_argument('--selector',required=True,type=Path)
    parser.add_argument('--out',type=Path)
    parser.add_argument('--normalized',type=Path)
    parser.add_argument('--source-map',type=Path)
    parser.add_argument('--detailed-map',type=Path)
    for name,default in DEFAULT_LIMITS.items():
        parser.add_argument('--'+name.replace('_','-'),type=float if name=='max_seconds' else int,default=default)
    args = parser.parse_args()
    try:
        limits = limits_with({key:getattr(args,key) for key in DEFAULT_LIMITS})
        selector_info = artifact_info(args.selector,limits['max_artifact_bytes'])
        with args.selector.open('rb') as stream:
            selector_bytes = stream.read(limits['max_artifact_bytes']+1)
        if len(selector_bytes) > limits['max_artifact_bytes'] or file_signature(args.selector) != selector_info['signature']:
            raise ResourceLimitError('selector exceeds bound or changed during read')
        selector = strict_json(selector_bytes.decode('utf-8'))
        if args.command == 'normalize':
            if args.out is None or any([args.normalized,args.source_map,args.detailed_map]):
                raise RawInputError('normalize requires --out and no supplied artifact paths')
            result = normalize_selected(args.raw,selector,args.out,limits=limits)
        else:
            if args.out is not None or not all([args.normalized,args.source_map,args.detailed_map]):
                raise RawInputError('verify requires --normalized, --source-map and --detailed-map')
            result = verify_selected(args.raw,selector,args.normalized,args.source_map,args.detailed_map,limits=limits)
        print(json.dumps(result,indent=2))
    except (ResourceLimitError,MemoryError) as error:
        print(json.dumps(dict(status='resource-inconclusive',protocolVerdict=None,error=str(error))))
        return 4
    except (RawInputError,OSError,UnicodeError) as error:
        print(json.dumps(dict(status='invalid-input',protocolVerdict=None,error=str(error))))
        return 2
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
