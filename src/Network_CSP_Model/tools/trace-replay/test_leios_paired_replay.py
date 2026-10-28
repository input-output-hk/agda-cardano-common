#!/usr/bin/env python3
"""Paired LeiosNotifyP/LeiosFetchP CLI, payload, witness and manifest regressions."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def run_tests(binary, root):
    def header(protocol):
        return (f'pair {protocol} link-AB session-0\n'
                'client node-A c17 generation-0 fresh client.log\n'
                'server node-B c42 generation-3 fresh server.log\n')

    def rows(role, events):
        return ''.join(f'{role} {20 + 7*i} {e}\n' for i, e in enumerate(events))

    def check(protocol, cs, ss, depth=None, expected='accepted paired prefix'):
        text = header(protocol) + rows('server', ss) + rows('client', cs)
        return check_text(protocol, text, depth, expected)

    def check_text(protocol, text, depth=None, expected='accepted paired prefix'):
        path = root / 'pair.txt'
        path.write_text(text)
        mode = '--paired-notify' if protocol == 'LeiosNotifyP' else '--paired-fetch'
        args = [str(binary), mode, str(path)] + ([] if depth is None else [str(depth)])
        output = subprocess.run(args, check=True, capture_output=True, text=True).stdout
        assert output.startswith(expected), (protocol, text, output)
        return output

    def opposite(events):
        return [('Recv' + e[4:] if e.startswith('Send') else 'Send' + e[4:]) for e in events]

    def local(protocol, role, events, depth=2):
        path = root / f'local-{role}.txt'
        path.write_text(f'role {role}\n' + '\n'.join(events) + '\n')
        mode = ['--notify'] if protocol == 'LeiosNotifyP' else []
        output = subprocess.run([str(binary)] + mode + [str(path), str(depth)],
                                check=True, capture_output=True, text=True).stdout
        assert output.startswith('accepted'), output

    for protocol in ('LeiosNotifyP', 'LeiosFetchP'):
        notify = protocol == 'LeiosNotifyP'
        request = 'RequestNext' if notify else 'BlockRequest ab 3'
        response = 'BlockOffer ab 3 20' if notify else 'Block ab 20'
        cs = [f'Send {request}', f'Recv {response}', 'Send Done']
        ss = opposite(cs)
        output = check(protocol, cs, ss)
        assert 'in-flight client-to-server 0; server-to-client 0' in output
        # Verify exact source order and message matching independently of Agda.
        witness = output.split('witness merge:\n')[1].strip().splitlines()
        queues = {'client': [], 'server': []}
        seen = {'client': [], 'server': []}
        for line in witness:
            role, _, position, direction, payload = line.split(maxsplit=4)
            seen[role].append((int(position), f'{direction} {payload}'))
            if direction == 'Send':
                queues[role].append(payload)
            else:
                queue = queues['server' if role == 'client' else 'client']
                assert queue and queue.pop(0) == payload, line
        assert not any(queues.values())
        # Printers pad hexadecimal hashes; compare source coordinates separately.
        assert [p for p, _ in seen['client']] == [20, 27, 34]
        assert [p for p, _ in seen['server']] == [20, 27, 34]
        # Numeric values, rather than textual zero padding, define message equality.
        if not notify:
            check(protocol, ['Send BlockRequest 00ab 03', 'Recv Block 0ab 020'],
                  ['Recv BlockRequest ab 3', 'Send Block ab 20'])
        check(protocol, [], [])
        check(protocol, ['Send Done'], ['Recv Done'], 0)
        check(protocol, [f'Send {request}'], [], 0, 'rejected paired trace:')
        check(protocol, [], [f'Recv {request}'], expected='rejected paired trace:')
        check(protocol, [f'Send {request}', 'Send Done'], [], expected='rejected paired trace:')
        out = check(protocol, [f'Send {request}'], [])
        assert 'in-flight client-to-server 1' in out
        out = check(protocol, [f'Send {request}'], [f'Recv {request}', f'Send {response}'])
        assert 'server-to-client 1' in out
        piped = [f'Send {request}', f'Send {request}', f'Recv {response}', f'Recv {response}', 'Send Done']
        serial = [f'Recv {request}', f'Send {response}', f'Recv {request}', f'Send {response}', 'Recv Done']
        check(protocol, piped, serial, 2)
        check(protocol, piped, serial, 1, 'rejected paired trace:')
        if notify:
            check(protocol, piped, opposite(piped), 2)
        else:
            # Fetch responder remains sequential even with a larger client bound.
            check(protocol, piped, opposite(piped), 4, 'rejected paired trace:')
        for bad in [header(protocol).replace(' fresh ', ' unknown ', 1),
                    header(protocol).replace('node-B', 'node-A'),
                    header(protocol).replace(protocol, 'ChainSync'),
                    header(protocol) + f'client 0 Send {request}\n',
                    header(protocol) + f'client 9 Send {request}\nclient 8 Send {request}\n',
                    header(protocol) + f'client 9 Send {request}\nclient 9 Send {request}\n',
                    header(protocol) + 'client 9 Send NotAMessage\n']:
            check_text(protocol, bad, expected='insufficient evidence or malformed paired input')
        check_text(protocol, header(protocol), 'oops', 'usage:')
        check_text(protocol, header(protocol), '-1', 'usage:')

        # Each response mismatch is legal locally, but impossible on the paired FIFO.
        mismatches = ([('BlockAnnouncement -', 'BlockAnnouncement ab 3 20'),
                       ('BlockOffer ab 3 20', 'BlockOffer cd 3 20'),
                       ('BlockOffer ab 3 20', 'BlockOffer ab 4 20'),
                       ('BlockOffer ab 3 20', 'BlockOffer ab 3 21'),
                       ('BlockTxsOffer ab 3', 'BlockTxsOffer cd 3'),
                       ('Votes ab:2,cd:4', 'Votes cd:4,ab:2'),
                       ('Votes ab:2', 'Votes ab:3'),
                       ('Votes ab:2,ab:2', 'Votes ab:2')]
                      if notify else [('Block ab 20', 'Block ab 21')])
        for left, right in mismatches:
            c = [f'Send {request}', f'Recv {left}']
            s = [f'Recv {request}', f'Send {right}']
            local(protocol, 'client', c)
            local(protocol, 'server', s)
            check(protocol, c, s, expected='rejected paired trace:')
        if not notify:
            txreq = 'BlockTxsRequest ab 3 2 0:ff,1:aa'
            txreply = 'BlockTxs ab 3 2 80 0:ff,1:aa'
            for reply in [txreply, 'BlockTxs ab 3 9 90 -']:
                # Reply count/bitmap need not echo a request, but must match its send.
                check(protocol, [f'Send {txreq}', f'Recv {reply}'],
                      [f'Recv {txreq}', f'Send {reply}'])
            for field in ['BlockTxs ab 3 3 80 0:ff,1:aa',
                          'BlockTxs ab 3 2 81 0:ff,1:aa',
                          'BlockTxs ab 3 2 80 1:aa,0:ff',
                          'BlockTxs ab 3 2 80 0:fe,1:aa']:
                c, s = [f'Send {txreq}', f'Recv {txreply}'], [f'Recv {txreq}', f'Send {field}']
                local(protocol, 'client', c)
                local(protocol, 'server', s)
                check(protocol, c, s, expected='rejected paired trace:')
            check(protocol, ['Send BlockRequest ab 3', 'Recv Block cd 20'],
                  ['Recv BlockRequest ab 3', 'Send Block ab 20'], expected='rejected paired trace:')
            check(protocol, ['Send BlockRequest ab 3'], ['Recv BlockRequest ab 4'],
                  expected='rejected paired trace:')
        if notify:
            check(protocol,
                  ['Send RequestNext', 'Send RequestNext', 'Recv Votes -', 'Recv Votes ab:2'],
                  ['Recv RequestNext', 'Recv RequestNext', 'Send Votes ab:2', 'Send Votes -'],
                  2, 'rejected paired trace:')
        # Exact protocol namespaces, alias expansion and original source maps.
        ns = 'LeiosNotify' if notify else 'LeiosFetch'
        req_kind = 'NotificationRequestNext' if notify else 'BlockRequest ab 3'
        (root / 'client.txt').write_text(f'role client\n{ns}.Remote.Send.{req_kind}\n'
                                         f'{ns}.Remote.Receive.{response}\n')
        (root / 'server.txt').write_text(f'role server\n{ns}.Remote.Receive.{req_kind}\n'
                                         f'{ns}.Remote.Send.{response}\n')
        (root / 'client.src').write_text('301 later\n507 earlier\n')
        (root / 'server.src').write_text('101 earlier\n109 later\n')
        manifest = {'protocol': protocol, 'connection': 'AB', 'session': '0'}
        for role, node in [('client', 'A'), ('server', 'B')]:
            manifest[role] = {'node': node, 'connection': role + '-local', 'generation': '0',
                              'capture': 'fresh', 'file': role + '.txt',
                              'source': role + '.log', 'sourceMap': role + '.src'}
        mp, pair = root / 'manifest.json', root / 'assembled.txt'
        normalizer = Path(__file__).with_name('paired_sessions.py')
        def normalize():
            mp.write_text(json.dumps(manifest))
            return subprocess.run([sys.executable, '-I', str(normalizer), str(mp), str(pair)],
                                  capture_output=True, text=True)
        result = normalize()
        assert result.returncode == 0, result.stderr
        output = check_text(protocol, pair.read_text())
        assert 'client source-line 301' in output and 'server source-line 109' in output
        # Normalization retains all payload tokens without timestamps or sorting.
        assert f'client 507 Recv {response}' in pair.read_text()
        overwrite = subprocess.run([sys.executable, '-I', str(normalizer), str(mp),
                                    str(root / 'client.txt')], capture_output=True, text=True)
        assert overwrite.returncode == 2
        for malformed in [f'role server\nSend {request}\n',
                          f'role client\nSend {request} extra\n']:
            (root / 'client.txt').write_text(malformed)
            assert normalize().returncode == 2
        (root / 'client.txt').write_text(f'role client\nSend {request}\nRecv {response}\n')
        manifest['client']['capture'] = 'unknown'
        assert normalize().returncode == 2
        manifest['client']['capture'] = 'fresh'
        (root / 'client.src').write_text('507 t\n301 t\n')
        assert normalize().returncode == 2
        (root / 'client.src').write_text('301 t\n507 t\n')
        (root / 'client.txt').write_text('role client\nChainSync.Remote.Send.RequestNext\n')
        assert normalize().returncode == 2
    print('paired LeiosNotifyP/LeiosFetchP CLI, exact fields, witnesses and manifests passed')


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: test_leios_paired_replay.py /path/to/Main')
    with tempfile.TemporaryDirectory(prefix='paired-leios-cli-') as directory:
        run_tests(Path(sys.argv[1]).resolve(), Path(directory))
