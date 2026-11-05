#!/usr/bin/env python3
"""Stream capture metadata/field/session-boundary evidence; never issue a replay verdict."""
import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import resource
import sys
import tempfile
import time

NS = re.compile(r'^LeiosNotify\.Remote\.(Send|Receive)\.([^.]+)$')
REQUESTS = {'RequestNext', 'NotificationRequestNext', 'Quit'}
REPLIES = {'BlockAnnouncement', 'BlockOffer', 'BlockTxsOffer', 'Votes', 'Canceled', 'Done'}
FIELDS = {'BlockAnnouncement': ('ebHash', 'ebSlot', 'ebBodySize'),
          'BlockOffer': ('ebHash', 'ebSlot', 'ebBytesSize'),
          'BlockTxsOffer': ('ebHash', 'ebSlot'), 'Votes': ('votes',)}
EXPECTED_KIND = {'RequestNext': 'MsgLeiosNotificationRequestNext',
                 'NotificationRequestNext': 'MsgLeiosNotificationRequestNext',
                 'Quit': 'MsgQuit', 'Canceled': 'MsgCanceled', 'Done': 'MsgDone'}


def connection(value):
    """Retain literal endpoint spellings; no NAT, DNS or endpoint identity is guessed."""
    if isinstance(value, str):
        return value
    if isinstance(value, dict) and set(value) >= {'localAddress', 'remoteAddress'}:
        def address(item):
            host, port = item.get('address'), item.get('port')
            if host is None or port is None:
                return None
            host = str(host)
            return ('['+host+']' if ':' in host and not host.startswith('[') else host) + ':' + str(port)
        local, remote = address(value['localAddress']), address(value['remoteAddress'])
        if local and remote:
            return local + ' ' + remote
    return None


def get_connection(data):
    for candidate in [data.get('peer', {}).get('connectionId') if isinstance(data.get('peer'), dict) else None,
                      data.get('bearer', {}).get('connectionId') if isinstance(data.get('bearer'), dict) else None,
                      data.get('connectionId')]:
        result = connection(candidate)
        if result:
            return result
    return None


def check_fields(kind, message):
    """Check the retained metadata grammar; this does not assert native header/body completeness."""
    issues = []
    for name in FIELDS.get(kind, ()):
        if name not in message or message[name] is None:
            issues.append('missing:' + name)
        elif name in {'ebSlot', 'ebBodySize', 'ebBytesSize'}:
            if isinstance(message[name], bool) or not isinstance(message[name], int) or message[name] < 0:
                issues.append('invalid-natural:' + name)
        elif name == 'ebHash' and (not isinstance(message[name], str) or not re.fullmatch('[0-9a-fA-F]+', message[name])):
            issues.append('invalid-hex:' + name)
        elif name == 'votes':
            if not isinstance(message[name], list):
                issues.append('invalid-list:votes')
            elif any(not isinstance(vote, dict) or 'rbHash' not in vote or 'voterId' not in vote
                     for vote in message[name]):
                issues.append('missing-vote-metadata')
    expected = EXPECTED_KIND.get(kind, 'MsgLeios' + kind)
    if message.get('kind') != expected:
        issues.append('namespace-message-kind-mismatch')
    return issues


def marker(line, offset, obj, direction=None, kind=None):
    """Coordinates refer to the unchanged file, without reordering or reconstructed events."""
    result = {'line': line, 'byte_offset': offset, 'at': obj.get('at')}
    if direction:
        result.update(direction=direction, kind=kind)
    return result


def audit(path, max_line_bytes=1024*1024, max_sessions=100000):
    """One binary streaming pass hashes all bytes while retaining only aggregate/session metadata."""
    path = Path(path).resolve()
    before = path.stat()
    digest, total_bytes, line_number = hashlib.sha256(), 0, 0
    counts, namespaces, kinds, fields, issues = Counter(), Counter(), Counter(), Counter(), Counter()
    hosts, thread_keys, timestamp_host_last = Counter(), Counter(), {}
    mux_generation, mux_first, mux_last = Counter(), {}, {}
    local_sessions, sequence = {}, Counter()
    revision_candidates = []
    first_record = last_record = None
    last_at = None
    previous_json = None
    with path.open('rb') as stream:
        while True:
            offset = total_bytes
            raw = stream.readline(max_line_bytes + 1)
            if not raw:
                break
            line_number += 1
            digest.update(raw); total_bytes += len(raw)
            counts['raw_notify_request_literal_mentions'] += int(b'MsgLeiosNotificationRequestNext' in raw)
            if len(raw) > max_line_bytes:
                counts['oversized_lines'] += 1
                while raw and not raw.endswith(b'\n'):
                    raw = stream.readline(max_line_bytes + 1)
                    digest.update(raw); total_bytes += len(raw)
                continue
            start = raw.find(b'{')
            if start < 0:
                counts['non_json_lines'] += 1
                continue
            try:
                obj = json.loads(raw[start:])
            except (json.JSONDecodeError, UnicodeDecodeError):
                counts['malformed_json_lines'] += 1
                continue
            if not isinstance(obj, dict):
                counts['non_object_json'] += 1
                continue
            counts['json_records'] += 1
            ns, at, host = obj.get('ns'), obj.get('at'), obj.get('host')
            if not isinstance(ns, str):
                counts['missing_namespace'] += 1
                continue
            namespaces[ns] += 1
            hosts[str(host)] += 1
            current = marker(line_number, offset, obj)
            if first_record is None:
                first_record = current
            last_record = current
            if isinstance(at, str):
                if last_at is not None:
                    counts['adjacent_equal_at'] += int(at == last_at)
                    counts['file_at_decreases'] += int(at < last_at)
                if host in timestamp_host_last:
                    counts['host_at_decreases'] += int(at < timestamp_host_last[host])
                timestamp_host_last[host] = at
                last_at = at
            if previous_json == raw[start:]:
                counts['adjacent_identical_json'] += 1
            previous_json = raw[start:]
            data = obj.get('data')
            if not isinstance(data, dict):
                continue
            lower_ns = ns.lower()
            if 'startup' in lower_ns or 'nodeinfo' in lower_ns:
                counts['startup_or_nodeinfo_records'] += 1
                for key, value in data.items():
                    if key.lower().replace('_', '') in {'gitrev', 'gitrevision', 'revision', 'commit', 'gitsha', 'version'}:
                        if isinstance(value, (str, int)) and len(str(value)) <= 256:
                            revision_candidates.append(dict(current, namespace=ns, field=key, value=value))
            conn = get_connection(data)
            if ns == 'Net.Mux.Remote.NewMux':
                counts['new_mux_records'] += 1
                if conn and isinstance(host, str):
                    key = host, conn
                    mux_generation[key] += 1
                    mux_first.setdefault(key, current)
                    mux_last[key] = current
                else:
                    counts['new_mux_missing_host_or_connection'] += 1
            match = NS.fullmatch(ns)
            if not match:
                continue
            counts['notify_records'] += 1
            direction, kind = match.groups()
            kinds[direction + '.' + kind] += 1
            message = data.get('msg')
            if not isinstance(message, dict):
                counts['notify_non_object_message'] += 1
                continue
            fields[kind + ':' + ','.join(sorted(message))] += 1
            for issue in check_fields(kind, message):
                issues[kind + ':' + issue] += 1
            if data.get('kind') != ('Send' if direction == 'Send' else 'Recv'):
                issues[kind + ':namespace-direction-mismatch'] += 1
            for thread_key in ['thread', 'threadId', 'thread_id']:
                if thread_key in obj:
                    thread_keys['top.' + thread_key] += 1
                if thread_key in data:
                    thread_keys['data.' + thread_key] += 1
            if not any(key in obj or key in data for key in ['thread','threadId','thread_id']):
                counts['notify_without_thread_metadata'] += 1
            if not isinstance(host, str) or not conn:
                counts['notify_missing_host_or_connection'] += 1
                continue
            if kind in REQUESTS:
                role = 'client' if direction == 'Send' else 'server'
            elif kind in REPLIES:
                role = 'server' if direction == 'Send' else 'client'
            else:
                role = 'unknown'
            generation = mux_generation[host, conn]
            base = host, conn, generation, role
            key = base + (sequence[base],)
            if key not in local_sessions:
                if len(local_sessions) >= max_sessions:
                    raise ValueError('session metadata limit exceeded; no complete audit report issued')
                local_sessions[key] = {'host': host, 'connection_id': conn, 'role_from_message_agency': role,
                    'observed_mux_generation': generation, 'segment_after_done': sequence[base],
                    'preceding_new_mux': mux_last.get((host, conn)), 'first': marker(line_number,offset,obj,direction,kind),
                    'last': None, 'events': 0, 'kinds': Counter(), 'done_observed': False}
            session = local_sessions[key]
            session['events'] += 1
            session['kinds'][direction + '.' + kind] += 1
            session['last'] = marker(line_number,offset,obj,direction,kind)
            if kind == 'Done':
                session['done_observed'] = True
                sequence[base] += 1
    after = path.stat()
    stable = (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns) == (after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns)
    if not stable or total_bytes != after.st_size:
        raise ValueError('capture changed during audit; no stable report issued')
    sessions = []
    starts = Counter()
    literal_endpoints = defaultdict(set)
    for session in local_sessions.values():
        session['kinds'] = dict(sorted(session['kinds'].items()))
        session['first_is_initial_command'] = session['first']['kind'] in REQUESTS
        session['fresh_start_candidate'] = bool(session['preceding_new_mux'] and session['first_is_initial_command'])
        session['start_status'] = ('initial-command-with-observed-new-mux' if session['fresh_start_candidate'] else
                                   'initial-command-without-observed-new-mux' if session['first_is_initial_command'] else
                                   'first-visible-event-is-reply-or-unknown')
        session['end_status'] = 'Done-observed' if session['done_observed'] else 'prefix-without-Done'
        starts[session['start_status']] += 1
        tokens = session['connection_id'].split()
        if len(tokens) == 2:
            literal_endpoints[tuple(tokens)].add(session['host'])
        sessions.append(session)
    reverse_candidates = []
    for (local, remote), endpoint_hosts in literal_endpoints.items():
        other_hosts = literal_endpoints.get((remote, local), set()) - endpoint_hosts
        if other_hosts and (local, remote) < (remote, local):
            reverse_candidates.append({'endpoints': [local, remote], 'hosts': sorted(endpoint_hosts | other_hosts)})
    return {'path': str(path), 'bytes': total_bytes, 'sha256': digest.hexdigest(), 'stable_during_audit': stable,
        'lines': line_number, 'first_record': first_record, 'last_record': last_record,
        'counts': dict(sorted(counts.items())), 'hosts': dict(sorted(hosts.items())),
        'notify_namespace_counts': dict(sorted(kinds.items())), 'notify_field_shapes': dict(sorted(fields.items())),
        'notify_message_totals': {kind: sum(kinds[direction+'.'+alias] for direction in ['Send','Receive']
            for alias in (['RequestNext','NotificationRequestNext'] if kind == 'RequestNext' else [kind]))
            for kind in ['RequestNext','Quit','BlockAnnouncement','BlockOffer','BlockTxsOffer','Votes','Canceled','Done']},
        'retained_metadata_issues': dict(sorted(issues.items())), 'thread_key_counts': dict(sorted(thread_keys.items())),
        'startup_source_identity_candidates': revision_candidates,
        'source_revision_status': 'not established by this capture audit',
        'session_count': len(sessions), 'session_start_summary': dict(sorted(starts.items())),
        'sessions_with_Done': sum(s['done_observed'] for s in sessions),
        'sessions_without_Done': sum(not s['done_observed'] for s in sessions),
        'literal_reverse_endpoint_candidates': reverse_candidates, 'sessions': sessions,
        'selected_namespace_counts': {ns: n for ns,n in sorted(namespaces.items()) if
            ns.startswith('Net.Mux.') or 'startup' in ns.lower() or 'nodeinfo' in ns.lower()},
        'limitations': ['Audit only; no model acceptance/rejection verdict.',
            'NewMux/initial-command observations are candidate boundaries, not proof of lossless capture.',
            'File order and byte/line coordinates are preserved; timestamps do not establish causal order.',
            'Literal reverse endpoints do not prove paired sessions; no NAT mapping, DNS or packet matching is inferred.',
            'Roles are assigned from target message agency; the deployed peer variant is not inferred.',
            'Metadata grammar checks do not establish availability of full native headers/bodies or a source revision.',
            'A prefix without Done is not successful completion; Done alone does not imply whole-node cleanup.']}


def selftest():
    with tempfile.TemporaryDirectory(prefix='notify-capture-audit-') as directory:
        path = Path(directory)/'fixture.log'
        def row(ns, data, at='2026-01-01T00:00:00.000000000Z', thread=None):
            obj = dict(at=at,ns=ns,data=data,host='h')
            if thread is not None:
                obj['thread'] = thread
            return ('prefix ' + json.dumps(obj,separators=(',',':'))+'\n').encode()
        conn = '127.0.0.1:1 127.0.0.2:2'
        wire = lambda kind: dict(kind='Send',msg=dict(kind=kind),peer=dict(connectionId=conn))
        content = row('Net.Mux.Remote.NewMux',dict(bearer=dict(connectionId=conn)))
        content += row('LeiosNotify.Remote.Send.NotificationRequestNext',wire('MsgLeiosNotificationRequestNext'),thread='t')
        content += row('LeiosNotify.Remote.Receive.Done',dict(kind='Recv',msg=dict(kind='MsgDone'),peer=dict(connectionId=conn)))
        content += row('LeiosNotify.Remote.Send.Quit',wire('MsgQuit'),at='2025-12-31T23:59:59.000000000Z')
        path.write_bytes(content)
        result = audit(path)
        assert result['sha256'] == hashlib.sha256(content).hexdigest()
        assert result['session_count'] == 2 and result['sessions_with_Done'] == 1
        assert result['sessions_without_Done'] == 1 and result['counts']['file_at_decreases'] == 1
        assert result['thread_key_counts'] == {'top.thread': 1}
        assert all(s['first']['line'] < s['last']['line'] or s['events'] == 1 for s in result['sessions'])
        assert check_fields('BlockOffer',dict(kind='MsgLeiosBlockOffer')) == ['missing:ebHash','missing:ebSlot','missing:ebBytesSize']
        assert result['source_revision_status'] == 'not established by this capture audit'
    return {'selftest': 'passed', 'checks': ['byte-exact hash','file coordinates','Done vs EOF prefix',
            'split after Done','timestamp decrease retained','thread preservation','missing metadata','no inferred revision']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', nargs='*', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--selftest', action='store_true')
    parser.add_argument('--full-sessions', action='store_true', help='retain every segment coordinate; default report contains bounded examples')
    parser.add_argument('--memory-mib', type=int, default=256, help='process address-space limit, default 256 MiB')
    parser.add_argument('--source-note', action='append', type=Path, default=[], help='hash nearby capture notes/scripts without executing them or attributing them to a capture')
    args = parser.parse_args()
    if args.out and args.out.resolve() in {path.resolve() for path in [*args.files,*args.source_note,Path(__file__)]}:
        parser.error('--out must not overwrite an input, context note or the auditor')
    if not 64 <= args.memory_mib <= 1024:
        parser.error('--memory-mib must be 64..1024')
    resource.setrlimit(resource.RLIMIT_AS, (args.memory_mib*1024*1024, args.memory_mib*1024*1024))
    resource.setrlimit(resource.RLIMIT_CPU, (300,300))
    started = time.monotonic()
    if args.selftest:
        print(json.dumps(selftest(),indent=2))
    if args.files:
        if args.out is None:
            parser.error('--out required for full reports')
        result = {'scope': 'T8.1 capture preparation, not certified replay',
            'audited_at_utc': datetime.now(timezone.utc).isoformat(),
            'command_argv': [part.decode() for part in Path('/proc/self/cmdline').read_bytes().split(b'\0') if part],
            'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'source_notes': [{'path': str(path.resolve()), 'bytes':path.stat().st_size,
                'sha256':hashlib.sha256(path.read_bytes()).hexdigest()} for path in args.source_note],
            'source_note_attribution': 'Nearby notes/scripts are context only; their use for these specific captures is not established.',
            'captures': [audit(path) for path in args.files]}
        if not args.full_sessions:
            for capture in result['captures']:
                examples = []
                selected = Counter()
                for session in capture.pop('sessions'):
                    key = (session['start_status'],session['end_status'])
                    if selected[key] < 3:
                        examples.append(session)
                        selected[key] += 1
                capture['segment_coordinate_examples'] = examples
                capture['full_segment_coordinates'] = 'rerun with --full-sessions; input files are unchanged'
        result['resources'] = {'address_space_limit_mib':args.memory_mib,'cpu_limit_seconds':300,
            'maximum_line_bytes':1024*1024,'maximum_session_metadata_records_per_file':100000,
            'peak_self_rss_kib_linux':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'elapsed_seconds':round(time.monotonic()-started,3)}
        args.out.write_text(json.dumps(result,indent=2)+'\n')
        for capture in result['captures']:
            print(capture['path'],capture['counts'].get('notify_records',0),'Notify records;',
                  capture['session_count'],'local role segments;',capture['sessions_with_Done'],'with Done')
    elif not args.selftest:
        parser.error('supply capture paths or --selftest')


if __name__ == '__main__':
    main()
