#!/usr/bin/env python3
"""Regression tests for evidence-based devnet connection generation tracking."""
import csv
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
SCRIPT = Path(__file__).with_name('normalize_logs.py')
_spec = importlib.util.spec_from_file_location('normalizer', SCRIPT)
adapter = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(adapter)

A = {'localAddress': {'address': '127.2.0.1', 'port': '3001'},
     'remoteAddress': {'address': '127.2.0.2', 'port': '3002'}}
B = {'localAddress': {'address': '127.2.0.1', 'port': '3001'},
     'remoteAddress': {'address': '127.2.0.3', 'port': '3003'}}
A_TEXT = '127.2.0.1:3001 127.2.0.2:3002'
B_TEXT = '127.2.0.1:3001 127.2.0.3:3003'


def lifecycle(ns, handler, cid=A, wrapped=False):
    record = {'at': 't', 'ns': ns, 'thread': handler, 'data': {'connectionId': cid}}
    raw = json.dumps(record)
    return json.dumps({'message': raw, 'process': 'Node1'}) if wrapped else raw


def handshake(handler, cid=A, **kwargs):
    return lifecycle(adapter.HANDSHAKE, handler, cid, **kwargs)


def cleanup(handler, cid=A):
    return lifecycle(adapter.CLEANUP, handler, cid)


def wire(suffix='Send.MsgInit', thread='100', cid=A_TEXT, prefix=adapter.TS):
    return json.dumps({'at': 't', 'ns': prefix + suffix, 'thread': thread,
                       'data': {'peer': {'connectionId': cid}, 'msg': {}}})


class ConnectionLifecycleTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def split(self, lines, **options):
        return adapter.split(lines, self.root, include_notify=True, include_control=True,
                             include_txsubmission2=True, connection_lifecycle=True, **options)

    def records(self, name):
        with (self.root / name).open() as stream:
            return list(csv.DictReader(stream, delimiter='\t'))

    def test_reconnect_is_a_new_generation_with_original_source_coordinates(self):
        lines = [handshake('10', wrapped=True), wire(),
                 wire('Send.FindIntersect', '101', prefix=adapter.CS), cleanup('10'),
                 handshake('20'), wire(thread='200'),
                 wire('Send.FindIntersect', '201', prefix=adapter.CS)]
        rows = self.split(lines)
        self.assertEqual(len(rows), 4)
        self.assertEqual([r[6] for r in rows], ['connection', 'connection', 'eof', 'eof'])
        index = self.records('index.tsv')
        self.assertEqual([r['connectionGeneration'] for r in index], ['0', '0', '1', '1'])
        self.assertEqual([r['handlerThread'] for r in index], ['10', '10', '20', '20'])
        self.assertEqual([r['handshakeLine'] for r in index], ['1', '1', '5', '5'])
        self.assertEqual((self.root / 'interleaved.src').read_text(), '2 t 0\n3 t 1\n6 t 2\n7 t 3\n')
        connections = self.records('connections.tsv')
        self.assertEqual(connections[0]['cleanupLine'], '4')
        self.assertEqual(connections[1]['cleanupLine'], '')

    def test_cleanup_closes_both_roles_and_other_connections_remain_open(self):
        rows = self.split([handshake('10'), handshake('11', B), wire(),
                           wire('Receive.MsgInit', '101'), wire(thread='110', cid=B_TEXT),
                           cleanup('10'), handshake('20'), wire(thread='200'),
                           wire('Send.Done', '110', cid=B_TEXT)])
        self.assertEqual([r[3] for r in rows], [1, 1, 2, 1])
        self.assertEqual([r[6] for r in rows], ['connection', 'connection', 'done', 'eof'])

    def test_duplicate_handshake_does_not_hide_repeated_init(self):
        rows = self.split([handshake('10'), wire(), handshake('10'), wire()])
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0][3], 2)
        self.assertEqual(len(self.records('connections.tsv')), 1)

    def test_overlapping_handlers_are_rejected_not_split(self):
        with self.assertRaisesRegex(ValueError, 'line 3: ambiguous overlapping'):
            self.split([handshake('10'), wire(), handshake('20')])

    def test_unknown_cleanup_cannot_authorize_a_new_generation(self):
        with self.assertRaisesRegex(ValueError, 'ambiguous overlapping'):
            self.split([handshake('10'), wire(), cleanup('99'), handshake('20')])

    def test_stale_cleanup_cannot_close_a_newer_generation(self):
        rows = self.split([handshake('10'), wire(), cleanup('10'), handshake('20'),
                           wire(thread='200'), cleanup('10'), wire(thread='200')])
        self.assertEqual([r[3] for r in rows], [1, 2])
        self.assertEqual(rows[1][6], 'eof')

    def test_wire_after_cleanup_requires_a_new_handshake(self):
        with self.assertRaisesRegex(ValueError, 'follows connection cleanup'):
            self.split([handshake('10'), wire(), cleanup('10'), wire()])

    def test_known_old_wire_thread_cannot_be_assigned_to_new_generation(self):
        with self.assertRaisesRegex(ValueError, 'earlier generation'):
            self.split([handshake('10'), wire(), cleanup('10'), handshake('20'), wire()])

    def test_wire_before_observed_handshake_fails_with_source_line(self):
        with self.assertRaisesRegex(ValueError, 'line 1:.*no preceding successful handshake'):
            self.split([wire()])

    def test_missing_thread_and_malformed_addresses_are_not_guessed(self):
        for lines in [[handshake(None)], [handshake('10'), wire(thread=None)],
                      [handshake('10', {'localAddress': {}})]]:
            with self.subTest(lines=lines), self.assertRaisesRegex(ValueError, 'line [12]:'):
                self.split(lines)

    def test_mux_and_handler_errors_are_not_generation_boundaries(self):
        errors = [json.dumps({'ns': adapter.MUX + suffix, 'at': 't',
                              'data': {'bearer': {'connectionId': A_TEXT}}})
                  for suffix in ['State', 'ExceptionExit', 'NewMux']]
        rows = self.split([handshake('10'), wire(), *errors,
                           lifecycle(adapter.CONNECTION + 'ConnectionHandler.Error', '10'), wire()])
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0][3], 2)

    def test_ipv6_endpoint_forms_and_numeric_ports_match(self):
        cid = {'localAddress': {'addr': '2001:0db8::1', 'port': 3001},
               'remoteAddress': {'address': '2001:db8::2', 'port': '03002'}}
        text = '[2001:db8::1]:3001 [2001:0db8::2]:3002'
        rows = self.split([handshake('10', cid), wire(cid=text), cleanup('10', cid)])
        self.assertEqual(rows[0][1], '[2001:db8::1]:3001 [2001:db8::2]:3002')
        self.assertEqual(rows[0][6], 'connection')

    def test_legacy_mode_does_not_change_its_boundary_policy(self):
        rows = adapter.split([handshake('10'), wire(), cleanup('10'), handshake('20'), wire(thread='200')],
                             self.root, include_txsubmission2=True)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0][3], 2)
        self.assertFalse((self.root / 'connections.tsv').exists())
        self.assertEqual(self.records('index.tsv')[0]['end'], 'eof')

    def test_cli_and_fetch_only_mode(self):
        raw = self.root / 'node.log'
        raw.write_text('\n'.join([handshake('10'), wire('Send.BlockRequest', prefix=adapter.LF)]) + '\n')
        # A request still needs real payload evidence: generation tracking must not invent it.
        command = [sys.executable, '-I', str(SCRIPT.resolve()), str(raw), str(self.root / 'out')]
        result = subprocess.run(command + ['--connection-lifecycle'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn('line 2:', result.stderr)
        self.assertNotIn('Traceback', result.stderr)
        record = json.loads(wire('Send.BlockRequest', prefix=adapter.LF))
        record['data']['msg'] = {'ebHash': 'ab', 'ebSlot': 3}
        raw.write_text(handshake('10') + '\n' + json.dumps(record) + '\n')
        result = subprocess.run(command + ['--connection-lifecycle', '--fetch-only'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((self.root / 'out/interleaved.txt').read_text(), 'sessions client\n0 Send BlockRequest ab 3\n')
        result = subprocess.run(command + ['--connection-lifecycle', '--no-mux-split'], capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn('cannot be combined', result.stderr)


if __name__ == '__main__':
    unittest.main()
