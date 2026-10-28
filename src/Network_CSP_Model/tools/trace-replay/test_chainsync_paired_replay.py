#!/usr/bin/env python3
"""Paired CLI, witness source mapping, explicit metadata and prefix regressions."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HEADER = ('pair ChainSync link-AB session-1\n'
          'client node-A local-17 generation-0 fresh client.log\n'
          'server node-B local-42 generation-3 fresh server.log\n')


def run_tests(binary, root):
    def check(text, depth='2', default=False):
        path = root / 'pair.txt'
        path.write_text(text)
        args = [str(binary), '--paired-chainsync', str(path)]
        if not default:
            args.append(depth)
        return subprocess.run(args, check=True, text=True, capture_output=True).stdout

    client = ['Send RequestNext', 'Send RequestNext', 'Recv AwaitReply',
              'Recv RollForward', 'Recv RollBackward', 'Send FindIntersect',
              'Recv IntersectFound', 'Send Done']
    server = ['Recv RequestNext', 'Send AwaitReply', 'Send RollForward',
              'Recv RequestNext', 'Send RollBackward', 'Recv FindIntersect',
              'Send IntersectFound', 'Recv Done']

    def rows(role, events, offset):
        return [f'{role} {offset+i*3} {event}' for i, event in enumerate(events)]

    cs = rows('client', client, 10)
    ss = rows('server', server, 200)
    # Listing the whole server input first does not make its receive occur first.
    output = check(HEADER + '\n'.join(ss + cs) + '\n')
    assert output.startswith('accepted paired prefix'), output
    assert 'in-flight client-to-server 0; server-to-client 0' in output
    witness = output.split('witness merge:\n')[1].strip().splitlines()
    assert [line.replace(' source-line ', ' ') for line in witness if line.startswith('client ')] == cs
    assert [line.replace(' source-line ', ' ') for line in witness if line.startswith('server ')] == ss
    assert witness[:2] == ['client source-line 10 Send RequestNext',
                           'client source-line 13 Send RequestNext']
    # Independently verify the returned wire matching and FIFO order.
    ctos, stoc = [], []
    for line in witness:
        role, _, position, direction, kind = line.split()
        queue = ctos if (role, direction) in [('client', 'Send'), ('server', 'Recv')] else stoc
        if direction == 'Send':
            queue.append(kind)
        else:
            assert queue and queue.pop(0) == kind
    assert not ctos and not stoc
    assert check(HEADER + '\n'.join(cs + ss) + '\n', '1').startswith('rejected paired trace:')
    assert check(HEADER + '\n'.join(cs + ss) + '\n', default=True).startswith('accepted paired prefix')
    mismatch_c = 'role client\nSend RequestNext\nRecv RollForward\n'
    mismatch_s = 'role server\nRecv RequestNext\nSend RollBackward\n'
    for role, text in [('client', mismatch_c), ('server', mismatch_s)]:
        local = root / f'local-{role}.txt'
        local.write_text(text)
        result = subprocess.run([str(binary), '--chainsync', str(local), '2'],
                                check=True, text=True, capture_output=True)
        assert result.stdout.startswith('accepted'), result.stdout
    mismatch = HEADER + ('client 2 Send RequestNext\nclient 3 Recv RollForward\n'
                         'server 8 Recv RequestNext\nserver 9 Send RollBackward\n')
    assert check(mismatch).startswith('rejected paired trace:')
    assert check(HEADER + 'server 8 Recv RequestNext\n').startswith('rejected paired trace:')
    assert check(HEADER + 'client 2 Send RequestNext\nclient 3 Send RequestNext\n').startswith('accepted paired prefix')
    assert 'in-flight client-to-server 2' in check(HEADER + 'client 2 Send RequestNext\nclient 3 Send RequestNext\n')
    assert check(HEADER).startswith('accepted paired prefix')
    zero = HEADER + ('client 2 Send FindIntersect\nclient 3 Recv IntersectNotFound\nclient 4 Send Done\n'
                     'server 2 Recv FindIntersect\nserver 3 Send IntersectNotFound\nserver 4 Recv Done\n')
    assert check(zero, '0').startswith('accepted paired prefix')
    assert check(HEADER + 'client 2 Send RequestNext\n', '0').startswith('rejected paired trace:')
    bad_inputs = [
        HEADER.replace(' fresh ', ' unknown ', 1),
        HEADER.replace('server node-B', 'server node-A'),
        HEADER.replace('ChainSync', 'BlockFetch', 1),
        HEADER + 'client 0 Send RequestNext\n',
        HEADER + 'client 3 Send RequestNext\nclient 3 Send RequestNext\n',
        HEADER + 'client 3 Send RequestNext\nclient 2 Send RequestNext\n',
        HEADER + 'client 3 Send RequestNext payload\n',
        HEADER + 'client 3 BlockFetch.Remote.Send.ClientDone\n',
        'role client\nSend RequestNext\n',
        HEADER + 'unknown 3 Send RequestNext\n',
    ]
    for text in bad_inputs:
        assert check(text).startswith('insufficient evidence or malformed paired input'), text
    # Explicit normalizer consumes adapter-compatible source maps without sorting.
    (root / 'client.txt').write_text(mismatch_c)
    (root / 'server.txt').write_text('role server\nRecv RequestNext\nSend RollForward\n')
    (root / 'client.src').write_text('301 later\n507 earlier\n')
    (root / 'server.src').write_text('101 earlier\n109 later\n')
    manifest = {
        'protocol': 'ChainSync', 'connection': 'link-AB', 'session': 'session-1',
        'client': {'node': 'A', 'connection': '17', 'generation': '0', 'capture': 'fresh',
                   'file': 'client.txt', 'source': 'client-raw.log', 'sourceMap': 'client.src'},
        'server': {'node': 'B', 'connection': '42', 'generation': '3', 'capture': 'fresh',
                   'file': 'server.txt', 'source': 'server-raw.log', 'sourceMap': 'server.src'},
    }
    manifest_path, pair = root / 'manifest.json', root / 'assembled.txt'
    manifest_path.write_text(json.dumps(manifest))
    normalizer = Path(__file__).with_name('chainsync_pair.py')
    def normalize():
        return subprocess.run([sys.executable, '-I', str(normalizer), str(manifest_path), str(pair)],
                              text=True, capture_output=True)
    result = normalize()
    assert result.returncode == 0, result.stderr
    output = check(pair.read_text())
    assert output.startswith('accepted paired prefix') and 'client source-line 301' in output
    assert 'client-raw.log' in output and 'server source-line 109' in output
    manifest['client']['capture'] = 'unknown'
    manifest_path.write_text(json.dumps(manifest))
    assert normalize().returncode == 2
    manifest['client']['capture'] = 'fresh'
    manifest_path.write_text(json.dumps(manifest))
    (root / 'client.src').write_text('301 t\n')
    assert normalize().returncode == 2
    manifest_path.write_text('{"protocol":"ChainSync","protocol":"BlockFetch"}')
    assert normalize().returncode == 2
    print('paired ChainSync CLI, witness, metadata and source-map regressions passed')


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: test_chainsync_paired_replay.py /path/to/Main')
    with tempfile.TemporaryDirectory(prefix='paired-chainsync-cli-') as directory:
        run_tests(Path(sys.argv[1]).resolve(), Path(directory))
