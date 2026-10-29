#!/usr/bin/env python3
"""BlockFetch/TxSubmission2 paired CLI, control matching and source-map regressions."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile


MODES = {'BlockFetch': '--paired-blockfetch', 'TxSubmission2': '--paired-txsubmission2'}


def run_tests(binary, root):
    def header(protocol):
        return (f'pair {protocol} AB generation-0\n'
                'client node-A c17 generation-0 fresh client.log\n'
                'server node-B c42 generation-7 fresh server.log\n')

    def rows(role, events):
        offset = 100 if role == 'client' else 500
        return ''.join(f'{role} {offset + 3*i} {event}\n' for i, event in enumerate(events))

    def check_text(protocol, text, depth=None, expected='accepted paired prefix'):
        path = root / 'pair.txt'
        path.write_text(text)
        args = [str(binary), MODES[protocol], str(path)]
        if depth is not None:
            args.append(str(depth))
        output = subprocess.run(args, check=True, text=True, capture_output=True).stdout
        assert output.startswith(expected), (protocol, output, text)
        return output

    def check(protocol, cs, ss, depth=None, expected='accepted paired prefix'):
        # Cross-endpoint file order does not constrain the searched merge.
        return check_text(protocol, header(protocol) + rows('server', ss) + rows('client', cs),
                          depth, expected)

    def local(protocol, role, events):
        path = root / f'{role}-local.txt'
        path.write_text(f'role {role}\n' + '\n'.join(events) + '\n')
        mode = '--blockfetch' if protocol == 'BlockFetch' else '--txsubmission2'
        output = subprocess.run([str(binary), mode, str(path), '2'],
                                check=True, text=True, capture_output=True).stdout
        assert output.startswith('accepted'), output

    def witness(output, cs, ss):
        queues = {'client': [], 'server': []}
        seen = {'client': [], 'server': []}
        for line in output.split('witness merge:\n', 1)[1].strip().splitlines():
            role, marker, position, direction, message = line.split(maxsplit=4)
            assert marker == 'source-line'
            seen[role].append((int(position), direction + ' ' + message))
            if direction == 'Send':
                queues[role].append(message)
            else:
                queue = queues['server' if role == 'client' else 'client']
                assert queue and queue.pop(0) == message, line
        assert seen['client'] == [(100 + 3*i, e) for i, e in enumerate(cs)]
        assert seen['server'] == [(500 + 3*i, e) for i, e in enumerate(ss)]
        assert not any(queues.values())

    bf_client = ['Send RequestRange', 'Send RequestRange', 'Recv StartBatch',
                 'Recv Block', 'Recv Block', 'Recv BatchDone', 'Recv NoBlocks', 'Send ClientDone']
    bf_server = ['Recv RequestRange', 'Send StartBatch', 'Send Block', 'Send Block',
                 'Send BatchDone', 'Recv RequestRange', 'Send NoBlocks', 'Recv ClientDone']
    ts_client = ['Send Init', 'Recv RequestTxIds NonBlocking', 'Send ReplyTxIds Empty',
                 'Recv RequestTxs', 'Send ReplyTxs', 'Recv RequestTxIds Blocking', 'Send Done']
    ts_server = ['Recv Init', 'Send RequestTxIds NonBlocking', 'Send RequestTxs',
                 'Recv ReplyTxIds Empty', 'Recv ReplyTxs', 'Send RequestTxIds Blocking', 'Recv Done']

    for protocol, cs, ss in [('BlockFetch', bf_client, bf_server),
                             ('TxSubmission2', ts_client, ts_server)]:
        output = check(protocol, cs, ss, 2)
        assert 'in-flight client-to-server 0; server-to-client 0' in output
        witness(output, cs, ss)
        check(protocol, cs, ss)  # existing standalone defaults apply to paired mode
        check(protocol, cs, ss, 1, 'rejected paired trace:')
        check(protocol, [], [])
        for depth in ('oops', '-1'):
            check(protocol, [], [], depth, 'usage:')
        for extra in ([], [str(root / 'pair.txt'), '2', 'extra']):
            output = subprocess.run([str(binary), MODES[protocol]] + extra,
                                    check=True, text=True, capture_output=True).stdout
            assert output.startswith('usage:'), output
        check_text(protocol, header(protocol).replace(' fresh ', ' unknown ', 1),
                   expected='insufficient evidence or malformed paired input')
        check_text(protocol, header(protocol).replace('server node-B', 'server node-A'),
                   expected='insufficient evidence or malformed paired input')
        check_text(protocol, header(protocol) + 'client 0 Send Done\n',
                   expected='insufficient evidence or malformed paired input')

        # Namespaced normalization with explicit raw-line maps must preserve witness coordinates.
        namespace = 'BlockFetch' if protocol == 'BlockFetch' else 'TxSubmission'
        def namespaced(event):
            direction, message = event.split(' ', 1)
            if protocol == 'TxSubmission2' and message == 'Init':
                message = 'MsgInit'
            return f'{namespace}.Remote.{"Send" if direction == "Send" else "Receive"}.{message}'
        for role, events in [('client', cs), ('server', ss)]:
            (root / f'{role}.txt').write_text(f'role {role}\n' +
                '\n'.join(namespaced(e) for e in events) + '\n')
            (root / f'{role}.src').write_text(''.join(f'{1000 + i*11} unsorted-time\n'
                                                    for i in range(len(events))))
        manifest = {'protocol': protocol, 'connection': 'AB', 'session': 'fresh-0'}
        for role, node in [('client', 'A'), ('server', 'B')]:
            manifest[role] = {'node': node, 'connection': role + '-local', 'generation': '0',
                              'capture': 'fresh', 'file': role + '.txt',
                              'source': role + '-raw.log', 'sourceMap': role + '.src'}
        mf, assembled = root / 'manifest.json', root / 'assembled.txt'
        def assemble():
            mf.write_text(json.dumps(manifest))
            return subprocess.run([sys.executable, '-I', str(Path(__file__).with_name('paired_sessions.py')),
                                   str(mf), str(assembled)], capture_output=True, text=True)
        result = assemble()
        assert result.returncode == 0, result.stderr
        output = check_text(protocol, assembled.read_text(), 2)
        assert 'client source client-raw.log' in output and 'server source server-raw.log' in output
        assert 'client source-line 1000 Send ' in output and 'server source-line 1000 Recv ' in output
        # The Agda parser also accepts the exact namespace grammar without the assembler.
        check(protocol, [namespaced(e) for e in cs], [namespaced(e) for e in ss], 2)
        bad_events = (['Send RequestRange payload', 'Send NoBlocks extra',
                       'ChainSync.Remote.Send.RequestNext'] if protocol == 'BlockFetch' else
                      ['Recv RequestTxIds', 'Send ReplyTxIds', 'Recv RequestTxIds Unknown',
                       'Send ReplyTxIds Unknown', 'TxSubmission2.Remote.Send.MsgInit',
                       'TxSubmission.Remote.Send.Init', 'Send Init extra'])
        for bad in bad_events:
            check_text(protocol, header(protocol) + f'client 2 {bad}\n',
                       expected='insufficient evidence or malformed paired input')
            (root / 'client.txt').write_text('role client\n' + bad + '\n')
            (root / 'client.src').write_text('1000 t\n')
            assert assemble().returncode == 2, bad

    # Locally legal endpoints disagree about the actual batch outcome or block count.
    for c, s in [(['Send RequestRange', 'Recv NoBlocks'],
                  ['Recv RequestRange', 'Send StartBatch', 'Send BatchDone']),
                 (['Send RequestRange', 'Recv StartBatch', 'Recv Block', 'Recv BatchDone'],
                  ['Recv RequestRange', 'Send StartBatch', 'Send BatchDone']),
                 (['Send RequestRange', 'Send RequestRange', 'Recv NoBlocks',
                   'Recv StartBatch', 'Recv BatchDone'],
                  ['Recv RequestRange', 'Send StartBatch', 'Send BatchDone',
                   'Recv RequestRange', 'Send NoBlocks'])]:
        local('BlockFetch', 'client', c)
        local('BlockFetch', 'server', s)
        check('BlockFetch', c, s, 2, 'rejected paired trace:')
    check('BlockFetch', ['Send ClientDone'], ['Recv ClientDone'], 0)
    check('BlockFetch', ['Send RequestRange'], [], 0, 'rejected paired trace:')
    check('BlockFetch', [], ['Recv RequestRange'], 2, 'rejected paired trace:')
    output = check('BlockFetch', ['Send RequestRange', 'Send RequestRange'], [], 2)
    assert 'in-flight client-to-server 2; server-to-client 0' in output
    output = check('BlockFetch', ['Send RequestRange'], ['Recv RequestRange', 'Send NoBlocks'], 2)
    assert 'in-flight client-to-server 0; server-to-client 1' in output
    check('BlockFetch', ['Send RequestRange', 'Send RequestRange'],
          ['Recv RequestRange', 'Recv RequestRange'], 2, 'rejected paired trace:')

    # Both control distinctions and FIFO family order matter across TxSubmission2 endpoints.
    for c, s in [(['Send Init', 'Recv RequestTxIds NonBlocking', 'Send ReplyTxIds NonEmpty'],
                  ['Recv Init', 'Send RequestTxIds NonBlocking', 'Recv ReplyTxIds Empty']),
                 (['Send Init', 'Recv RequestTxIds Blocking', 'Send ReplyTxIds NonEmpty'],
                  ['Recv Init', 'Send RequestTxIds NonBlocking', 'Recv ReplyTxIds NonEmpty']),
                 (['Send Init', 'Recv RequestTxs', 'Send ReplyTxs',
                   'Recv RequestTxIds NonBlocking', 'Send ReplyTxIds Empty'],
                  ['Recv Init', 'Send RequestTxIds NonBlocking', 'Send RequestTxs',
                   'Recv ReplyTxIds Empty', 'Recv ReplyTxs'])]:
        local('TxSubmission2', 'client', c)
        local('TxSubmission2', 'server', s)
        check('TxSubmission2', c, s, 2, 'rejected paired trace:')
    check('TxSubmission2', ['Send Init', 'Recv RequestTxIds Blocking', 'Send Done'],
          ['Recv Init', 'Send RequestTxIds Blocking', 'Recv Done'], 0)
    check('TxSubmission2', ['Send Init'], ['Recv Init', 'Send RequestTxs'],
          0, 'rejected paired trace:')
    check('TxSubmission2', [], ['Recv Init'], 2, 'rejected paired trace:')
    output = check('TxSubmission2', ['Send Init'], ['Recv Init', 'Send RequestTxs'], 2)
    assert 'in-flight client-to-server 0; server-to-client 1' in output
    check('TxSubmission2', ['Send Init', 'Recv RequestTxIds NonBlocking', 'Recv RequestTxs'],
          ['Recv Init', 'Send RequestTxIds NonBlocking', 'Send RequestTxs'], 100, 'rejected paired trace:')
    check('TxSubmission2', ['Send Init', 'Recv RequestTxIds Blocking', 'Send ReplyTxIds Empty'],
          ['Recv Init', 'Send RequestTxIds Blocking', 'Recv ReplyTxIds Empty'], 2, 'rejected paired trace:')
    check('TxSubmission2', ['Send Init', 'Recv RequestTxIds NonBlocking', 'Send Done'],
          ['Recv Init', 'Send RequestTxIds NonBlocking', 'Recv Done'], 2, 'rejected paired trace:')
    print('paired BlockFetch/TxSubmission2 CLI, FIFO, bounds, evidence and source-map regressions passed')


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: test_control_paired_replay.py /path/to/Main')
    with tempfile.TemporaryDirectory(prefix='paired-control-cli-') as directory:
        run_tests(Path(sys.argv[1]).resolve(), Path(directory))
