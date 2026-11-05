#!/usr/bin/env python3
"""Synthetic end-to-end correspondence regressions; no deployed-log verdict."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('lookahead_raw',HERE/'lookahead_raw.py')
RAW = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RAW)
CONNECTION = '10.0.0.1:3001 10.0.0.2:3001'


def notify(suffix, message, *, host='node-a', thread='receiver-λ', direction=None):
    """Retain literal JSON metadata and exact data/message agency fields."""
    return dict(ns='LeiosNotify.Remote.'+suffix,at='t1',host=host,thread=thread,
        data=dict(kind=direction or ('Send' if suffix.startswith('Send.') else 'Recv'),
                  peer=dict(connectionId=CONNECTION),msg=message))


def mux():
    return dict(ns='Net.Mux.Remote.NewMux',at='t0',host='node-a',
                data=dict(bearer=dict(connectionId=CONNECTION)))


def row(obj):
    return (json.dumps(obj,ensure_ascii=False)+'\n').encode()


def selector(role='client',generation=1,segment=0):
    return dict(host='node-a',connection=CONNECTION,role=role,
                observedMuxGeneration=generation,segmentAfterDone=segment)


def fixture():
    """Client includes every message kind, exact optional data and duplicate Votes."""
    return [mux(),notify('Send.NotificationRequestNext',dict(kind='MsgLeiosNotificationRequestNext')),
        notify('Receive.BlockAnnouncement',dict(kind='MsgLeiosBlockAnnouncement')),
        notify('Send.RequestNext',dict(kind='MsgLeiosNotificationRequestNext')),
        notify('Receive.BlockAnnouncement',dict(kind='MsgLeiosBlockAnnouncement',ebHash='AB',ebSlot=7,ebBodySize=19)),
        notify('Receive.BlockOffer',dict(kind='MsgLeiosBlockOffer',ebHash='cD',ebSlot=8,ebBytesSize=20)),
        notify('Receive.BlockTxsOffer',dict(kind='MsgLeiosBlockTxsOffer',ebHash='Ef',ebSlot=9)),
        notify('Receive.Votes',dict(kind='MsgLeiosVotes',votes=[dict(rbHash='AA',voterId=3),dict(rbHash='bb',voterId=4),dict(rbHash='AA',voterId=3)])),
        notify('Receive.Votes',dict(kind='MsgLeiosVotes',votes=[])),
        notify('Send.Quit',dict(kind='MsgQuit')),
        notify('Receive.Canceled',dict(kind='MsgCanceled')),
        notify('Receive.Canceled',dict(kind='MsgCanceled')),
        notify('Receive.Done',dict(kind='MsgDone'))]


class RawCorrespondenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='lookahead-raw-tests-')
        self.base = Path(self.temp.name)
        self.source = self.base/'capture.log'

    def tearDown(self):
        self.temp.cleanup()

    def write(self,objects):
        self.source.write_bytes(b''.join(row(obj) for obj in objects))

    def normalized(self,objects=None,selection=None):
        self.write(fixture() if objects is None else objects)
        out = self.base/'normalized'
        report = RAW.normalize_selected(self.source,selector() if selection is None else selection,out)
        return out,report

    def verify(self,out,selection=None,**options):
        return RAW.verify_selected(self.source,selector() if selection is None else selection,
            out/'local.txt',out/'local.src',out/'map.jsonl',**options)

    def test_all_kinds_optional_announcement_and_duplicate_votes(self):
        out,report = self.normalized()
        expected = ['role client','Send RequestNext','Recv BlockAnnouncement -','Send RequestNext',
            'Recv BlockAnnouncement ab 7 19','Recv BlockOffer cd 8 20',
            'Recv BlockTxsOffer ef 9','Recv Votes aa:3,bb:4,aa:3','Recv Votes -',
            'Send Quit','Recv Canceled','Recv Canceled','Recv Done']
        self.assertEqual((out/'local.txt').read_text().splitlines(),expected)
        self.assertEqual(report['rows'],12)
        self.assertIsNone(report['protocolVerdict'])
        verified = self.verify(out)
        self.assertEqual(verified['rows'],12)
        self.assertEqual(verified['raw']['sha256'],hashlib.sha256(self.source.read_bytes()).hexdigest())
        self.assertEqual(verified['status'],'correspondence-checked')

    def test_exact_multibyte_coordinates_raw_hash_and_threads(self):
        out,_ = self.normalized()
        rows = [json.loads(text) for text in (out/'map.jsonl').read_text().splitlines()]
        original = self.source.read_bytes().splitlines(keepends=True)
        self.assertEqual(rows[1]['byteOffset'],sum(map(len,original[:2])))
        for item in rows:
            line = original[item['line']-1]
            self.assertEqual(item['byteLength'],len(line))
            self.assertEqual(item['rawLineSha256'],hashlib.sha256(line).hexdigest())
            self.assertEqual(item['threads'],{'thread':'receiver-λ'})
            self.assertEqual(item['precedingNewMux'],{'line':1,'byteOffset':0})

    def test_both_server_agencies(self):
        records = [mux(),notify('Receive.RequestNext',dict(kind='MsgLeiosNotificationRequestNext')),
            notify('Send.BlockOffer',dict(kind='MsgLeiosBlockOffer',ebHash='a',ebSlot=1,ebBytesSize=2)),
            notify('Receive.Quit',dict(kind='MsgQuit')),notify('Send.Canceled',dict(kind='MsgCanceled')),
            notify('Send.Done',dict(kind='MsgDone'))]
        out,_ = self.normalized(records,selector('server'))
        self.assertEqual((out/'local.txt').read_text().splitlines(),[
            'role server','Recv RequestNext','Send BlockOffer a 1 2','Recv Quit','Send Canceled','Send Done'])
        self.verify(out,selector('server'))

    def test_done_and_newmux_are_separate_observed_coordinates(self):
        records = [mux(),notify('Send.Quit',dict(kind='MsgQuit')),notify('Receive.Done',dict(kind='MsgDone')),
            notify('Send.RequestNext',dict(kind='MsgLeiosNotificationRequestNext')),mux(),
            notify('Send.RequestNext',dict(kind='MsgLeiosNotificationRequestNext'))]
        self.write(records)
        scan = RAW.scan_raw(self.source)
        rows = list(scan)
        self.assertEqual([(r['observedMuxGeneration'],r['segmentAfterDone']) for r in rows],[(1,0),(1,0),(1,1),(2,0)])
        self.assertEqual(scan.summary['counts']['newMuxRecords'],2)

    def test_no_mux_is_generation_zero_without_freshness_claim(self):
        out,report = self.normalized([notify('Send.Quit',dict(kind='MsgQuit'))],selector(generation=0))
        item = json.loads((out/'map.jsonl').read_text())
        self.assertIsNone(item['precedingNewMux'])
        self.assertNotIn('fresh',report)
        self.verify(out,selector(generation=0))

    def test_wrappers_and_journal_prefixes_preserve_outer_coordinates(self):
        self.source.write_bytes(row(mux())+b'journal-prefix '+row(notify('Send.Quit',dict(kind='MsgQuit')))+
            row(dict(message=json.dumps(notify('Receive.Done',dict(kind='MsgDone'))))))
        scan=RAW.scan_raw(self.source); result=list(scan)
        self.assertEqual([r['line'] for r in result],[2,3])
        self.assertEqual(result[1]['event'],'Recv Done')

    def test_structured_connection_keeps_literal_ipv6(self):
        obj=notify('Send.Quit',dict(kind='MsgQuit'))
        obj['data']['peer']['connectionId']=dict(localAddress=dict(address='2001:0db8::1',port='03001'),remoteAddress=dict(address='127.0.0.1',port=3002))
        self.write([obj]); result=list(RAW.scan_raw(self.source))
        self.assertEqual(result[0]['connection'],'[2001:0db8::1]:03001 127.0.0.1:3002')

    def test_data_thread_and_missing_thread_preserved(self):
        a=notify('Send.Quit',dict(kind='MsgQuit')); del a['thread'];a['data']['thread_id']=17
        b=notify('Receive.Done',dict(kind='MsgDone'));del b['thread']
        self.write([a,b]);scan=RAW.scan_raw(self.source);rows=list(scan)
        self.assertEqual(rows[0]['threads'],{'data.thread_id':17})
        self.assertEqual(rows[1]['threads'],{})
        self.assertEqual(scan.summary['counts']['withoutThreadMetadata'],1)

    def test_timestamp_order_not_sorted(self):
        records=fixture();records[1]['at']='z';records[2]['at']='a'
        out,_=self.normalized(records)
        self.assertEqual((out/'local.src').read_text().splitlines()[:2],['2 z','3 a'])

    def test_serialised_observation_excluded_explicitly(self):
        self.write([dict(ns='LeiosNotify.Remote.Serialised.Send',data={}),notify('Send.Quit',dict(kind='MsgQuit'))])
        scan=RAW.scan_raw(self.source);rows=list(scan)
        self.assertEqual(len(rows),1)
        self.assertEqual(scan.summary['counts']['serialisedObservationsExcluded'],1)

    def test_unknown_notify_even_outside_endpoint_selection(self):
        records=fixture()+[notify('Send.Unknown',dict(kind='MsgUnknown'),host='other-node')]
        self.write(records)
        with self.assertRaisesRegex(RAW.RawInputError,'unsupported Notify'):
            RAW.normalize_selected(self.source,selector(),self.base/'bad')
        self.assertFalse((self.base/'bad').exists())

    def test_malformed_summary_controls(self):
        cases=[('Receive.BlockOffer',dict(kind='MsgLeiosBlockOffer',ebHash='xz',ebSlot=1,ebBytesSize=2)),
            ('Receive.BlockOffer',dict(kind='MsgLeiosBlockOffer',ebHash=12,ebSlot=1,ebBytesSize=2)),
            ('Receive.BlockOffer',dict(kind='MsgLeiosBlockOffer',ebHash='a',ebSlot=True,ebBytesSize=2)),
            ('Receive.BlockOffer',dict(kind='MsgLeiosBlockOffer',ebHash='a',ebSlot=-1,ebBytesSize=2)),
            ('Receive.BlockOffer',dict(kind='MsgLeiosBlockOffer',ebHash='a',ebSlot=1.0,ebBytesSize=2)),
            ('Receive.BlockAnnouncement',dict(kind='MsgLeiosBlockAnnouncement',ebHash='a')),
            ('Receive.BlockAnnouncement',dict(kind='MsgLeiosBlockAnnouncement',ebHash=None,ebSlot=None,ebBodySize=None)),
            ('Receive.Votes',dict(kind='MsgLeiosVotes',votes=[dict(rbHash='GG',voterId=0)])),
            ('Receive.Votes',dict(kind='MsgLeiosVotes',votes=[dict(rbHash='a',voterId=False)])),
            ('Receive.Votes',dict(kind='MsgLeiosVotes',votes=[dict(rbHash='a')])),
            ('Receive.Votes',dict(kind='MsgLeiosVotes',votes={})),
            ('Send.Quit',{}),('Send.Quit',dict(kind='MsgDone'))]
        for suffix,msg in cases:
            with self.subTest(suffix=suffix,msg=msg):
                self.write([notify(suffix,msg)])
                with self.assertRaises(RAW.RawInputError):list(RAW.scan_raw(self.source))

    def test_malformed_envelope_controls(self):
        for mutate in [lambda o:o['data'].update(kind='Recv'),lambda o:o.pop('host'),
                       lambda o:o['data'].pop('peer'),lambda o:o.update(at='bad timestamp'),
                       lambda o:o.update(thread=False),lambda o:o.update(ns='LeiosNotify.Remote'),
                       lambda o:o['data'].update(connectionId='other:1 peer:2')]:
            obj=notify('Send.Quit',dict(kind='MsgQuit'));mutate(obj);self.write([obj])
            with self.subTest(record=obj):
                with self.assertRaises(RAW.RawInputError):list(RAW.scan_raw(self.source))

    def test_strict_json_controls(self):
        for raw in [b'{"ns":"LeiosNotify.Remote.Send.Quit",\n',b'{"ns":"x","ns":"y"}\n',
                    b'{"ns":"x","ignored":NaN}\n',b'{"ns":"x","ignored":1e999}\n',
                    b'not structured JSON\n',b'{"ns":true}\n',b'{"message":"broken"}\n',b'\xff\n']:
            self.source.write_bytes(raw)
            with self.subTest(raw=raw):
                with self.assertRaises(RAW.RawInputError):list(RAW.scan_raw(self.source))

    def test_raw_and_artifact_resource_controls(self):
        self.write(fixture())
        controls=[dict(max_raw_bytes=1),dict(max_line_bytes=10),dict(max_records=2),dict(max_states=1),dict(max_metadata_bytes=1),dict(max_seconds=1e-12)]
        for limits in controls:
            with self.subTest(limits=limits):
                with self.assertRaises(RAW.ResourceLimitError):list(RAW.scan_raw(self.source,limits=limits))
        with self.assertRaises(RAW.ResourceLimitError):RAW.normalize_selected(self.source,selector(),self.base/'small',limits=dict(max_artifact_bytes=20))
        self.assertFalse((self.base/'small').exists())

    def test_artifact_tampering_and_extra_rows(self):
        out,_=self.normalized()
        for name in ['local.txt','local.src','map.jsonl']:
            path=out/name; original=path.read_bytes()
            for modified in [original.replace(b'2 ',b'999 ',1),original+b'extra\n',original[:-1]]:
                if modified==original:continue
                path.write_bytes(modified)
                with self.subTest(artifact=name):
                    with self.assertRaises(RAW.RawInputError):self.verify(out)
            path.write_bytes(original)
        self.verify(out)

    def test_raw_payload_tampering_is_not_just_hash_check(self):
        out,_=self.normalized()
        content=self.source.read_bytes().replace(b'"ebBodySize": 19',b'"ebBodySize": 18')
        self.source.write_bytes(content)
        with self.assertRaisesRegex(RAW.RawInputError,'normalized differs'):self.verify(out)

    def test_thread_only_tampering_detected_by_detailed_map(self):
        out,_=self.normalized()
        self.source.write_bytes(self.source.read_bytes().replace('receiver-λ'.encode(),'sender-λ'.encode()))
        with self.assertRaisesRegex(RAW.RawInputError,'detailed map differs'):self.verify(out)

    def test_wrong_or_empty_selector_rejected(self):
        self.write(fixture())
        for item in [{},dict(selector(),extra=True),dict(selector(),role='unknown'),dict(selector(),observedMuxGeneration=True)]:
            with self.subTest(selector=item):
                with self.assertRaises(RAW.RawInputError):RAW.normalize_selected(self.source,item,self.base/'empty')
        with self.assertRaisesRegex(RAW.RawInputError,'matched no'):RAW.normalize_selected(self.source,dict(selector(),host='wrong'),self.base/'empty')

    def test_existing_outputs_not_overwritten(self):
        out,_=self.normalized();before=(out/'local.txt').read_bytes()
        with self.assertRaises(RAW.RawInputError):RAW.normalize_selected(self.source,selector(),out)
        self.assertEqual((out/'local.txt').read_bytes(),before)

    def test_scan_reuse_and_mutation_do_not_issue_summary(self):
        self.write(fixture());scan=RAW.scan_raw(self.source);iterator=iter(scan);next(iterator)
        self.source.write_bytes(self.source.read_bytes()+row(dict(ns='Other',data={})))
        with self.assertRaises(RAW.ResourceLimitError):list(iterator)
        self.assertIsNone(scan.summary)
        with self.assertRaises(RAW.RawInputError):list(scan)

    def test_limit_validation(self):
        for limits in [dict(max_raw_bytes=True),dict(max_seconds=float('inf')),dict(max_records=1.5),dict(unknown=1),dict(max_states=0)]:
            with self.subTest(limits=limits):
                with self.assertRaises(RAW.RawInputError):RAW.limits_with(limits)

    def test_cli_normalize_verify_and_invalid_exit_classes(self):
        self.write(fixture());selection=self.base/'selector.json';selection.write_text(json.dumps(selector()))
        command=[sys.executable,'-I','-B',str(HERE/'lookahead_raw.py')]
        out=self.base/'cli-out'
        created=subprocess.run(command+['normalize','--raw',str(self.source),'--selector',str(selection),'--out',str(out)],capture_output=True,text=True)
        self.assertEqual(created.returncode,0,created.stderr+created.stdout)
        checked=subprocess.run(command+['verify','--raw',str(self.source),'--selector',str(selection),'--normalized',str(out/'local.txt'),'--source-map',str(out/'local.src'),'--detailed-map',str(out/'map.jsonl')],capture_output=True,text=True)
        self.assertEqual(checked.returncode,0,checked.stderr+checked.stdout)
        invalid=subprocess.run(command+['normalize','--raw',str(self.source),'--selector',str(selection),'--out',str(out)],capture_output=True,text=True)
        self.assertEqual(invalid.returncode,2)
        limited=subprocess.run(command+['normalize','--raw',str(self.source),'--selector',str(selection),'--out',str(self.base/'limited'),'--max-records','1'],capture_output=True,text=True)
        self.assertEqual(limited.returncode,4)


if __name__ == '__main__':
    unittest.main(verbosity=2)
