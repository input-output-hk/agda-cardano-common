#!/usr/bin/env python3
"""Assemble an explicitly declared fresh mini-protocol pair from normalized sessions.

No connection discovery, raw-log parsing, timestamp sorting or inferred restarts.
Relative paths in the JSON manifest are resolved against its directory.
"""
import argparse
import json
import re
from pathlib import Path

CHAIN_SYNC_KINDS = {'RequestNext', 'AwaitReply', 'RollForward', 'RollBackward',
         'FindIntersect', 'IntersectFound', 'IntersectNotFound', 'Done'}


def token(value, label):
    if not isinstance(value, str) or not value or len(value.split()) != 1 or value.strip() != value:
        raise ValueError(f'{label} must be a nonempty token without whitespace')
    return value


def fields(value, required, optional, label):
    if not isinstance(value, dict):
        raise ValueError(f'{label} must be an object')
    if set(value) - required - optional or required - set(value):
        raise ValueError(f'{label}: required keys {sorted(required)}, optional keys {sorted(optional)}')


def event(text, protocol):
    """Preserve payload tokens; the Agda parser remains the verdict authority."""
    words = text.split()
    namespace = {'ChainSync': 'ChainSync', 'LeiosNotifyP': 'LeiosNotify',
                 'LeiosFetchP': 'LeiosFetch'}[protocol]
    if words and '.' in words[0]:
        parts = words[0].split('.')
        if len(parts) == 4 and parts[:2] == [namespace, 'Remote']:
            direction = {'Send': 'Send', 'Receive': 'Recv'}.get(parts[2])
            kind = parts[3]
            if protocol == 'LeiosNotifyP' and kind == 'NotificationRequestNext':
                kind = 'RequestNext'
            words = [direction, kind] + words[1:]
    if len(words) < 2 or words[0] not in ('Send', 'Recv'):
        raise ValueError(f'unsupported normalized {protocol} event')
    kind, payload = words[1], words[2:]
    if protocol == 'ChainSync':
        valid = kind in CHAIN_SYNC_KINDS and not payload
    else:
        shapes = {
            'LeiosNotifyP': {'RequestNext': [()], 'Done': [()],
                'BlockAnnouncement': [('empty',), ('hex', 'dec', 'dec')],
                'BlockOffer': [('hex', 'dec', 'dec')],
                'BlockTxsOffer': [('hex', 'dec')], 'Votes': [('votes',)]},
            'LeiosFetchP': {'Done': [()], 'BlockRequest': [('hex', 'dec')],
                'Block': [('hex', 'dec')],
                'BlockTxsRequest': [('hex', 'dec', 'dec', 'bitmaps')],
                'BlockTxs': [('hex', 'dec', 'dec', 'dec', 'bitmaps')]},
        }
        patterns = {'hex': r'[0-9a-f]+', 'dec': r'[0-9]+', 'empty': r'-',
                    'votes': r'-|[0-9a-f]+:[0-9]+(?:,[0-9a-f]+:[0-9]+)*',
                    'bitmaps': r'-|[0-9]+:[0-9a-f]+(?:,[0-9]+:[0-9a-f]+)*'}
        valid = any(len(shape) == len(payload) and
                    all(re.fullmatch(patterns[t], value) for t, value in zip(shape, payload))
                    for shape in shapes[protocol].get(kind, []))
    if not valid:
        raise ValueError(f'unsupported normalized {protocol} event')
    return ' '.join(words)


def endpoint(value, role, base, protocol):
    required = {'node', 'connection', 'generation', 'capture', 'file'}
    fields(value, required, {'source', 'sourceMap'}, role)
    if value['capture'] != 'fresh':
        raise ValueError(f'{role}: capture must explicitly be fresh')
    info = [token(value[key], f'{role}.{key}') for key in ('node', 'connection', 'generation')]
    session = (base / token(value['file'], f'{role}.file')).resolve()
    lines = session.read_text().splitlines()
    if not lines or lines[0] != f'role {role}':
        raise ValueError(f'{session}: expected role {role} header')
    events = []
    for number, text in enumerate(lines[1:], 2):
        try:
            events.append(event(text, protocol))
        except ValueError as exc:
            raise ValueError(f'{session}:{number}: {exc}') from exc
    inputs = [session]
    if ('source' in value) != ('sourceMap' in value):
        raise ValueError(f'{role}: source and sourceMap must be provided together')
    if 'sourceMap' in value:
        source = token(value['source'], f'{role}.source')
        source_map = (base / token(value['sourceMap'], f'{role}.sourceMap')).resolve()
        inputs.append(source_map)
        positions = []
        for number, text in enumerate(source_map.read_text().splitlines(), 1):
            parts = text.split()
            if not parts or not parts[0].isascii() or not parts[0].isdigit():
                raise ValueError(f'{source_map}:{number}: expected decimal raw source line')
            positions.append(int(parts[0]))
        if len(positions) != len(events):
            raise ValueError(f'{role}: source-map count does not match event count')
    else:
        source = token(str(session), f'{role} source path')
        positions = list(range(2, len(events) + 2))
    if any(a >= b for a, b in zip([0] + positions, positions)):
        raise ValueError(f'{role}: source positions must be positive and strictly increasing')
    declaration = f'{role} {" ".join(info)} fresh {source}'
    rows = [f'{role} {line} {event}' for line, event in zip(positions, events)]
    return declaration, rows, inputs


def unique_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate manifest key: {key}')
        result[key] = value
    return result


def assemble(manifest_path):
    manifest_path = Path(manifest_path).resolve()
    data = json.loads(manifest_path.read_text(), object_pairs_hook=unique_keys)
    fields(data, {'protocol', 'connection', 'session', 'client', 'server'}, set(), 'manifest')
    if data['protocol'] not in ('ChainSync', 'LeiosNotifyP', 'LeiosFetchP'):
        raise ValueError('supported protocols: ChainSync, LeiosNotifyP, LeiosFetchP')
    connection = token(data['connection'], 'connection')
    session = token(data['session'], 'session')
    client, cs, client_inputs = endpoint(data['client'], 'client', manifest_path.parent, data['protocol'])
    server, ss, server_inputs = endpoint(data['server'], 'server', manifest_path.parent, data['protocol'])
    if data['client']['node'] == data['server']['node']:
        raise ValueError('client and server node identities must differ')
    # Grouping rows by endpoint supplies no cross-node chronological assertion.
    text = '\n'.join([f'pair {data["protocol"]} {connection} {session}', client, server] + cs + ss) + '\n'
    return text, [manifest_path] + client_inputs + server_inputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    try:
        text, inputs = assemble(args.manifest)
        if args.output.resolve() in inputs:
            raise ValueError('output must not overwrite a manifest, session or source map')
        args.output.write_text(text)
    except (ValueError, OSError, TypeError) as exc:
        parser.exit(2, f'insufficient evidence or malformed input: {exc}\n')
    print(f'wrote declared fresh mini-protocol pair: {args.output}')


if __name__ == '__main__':
    main()
