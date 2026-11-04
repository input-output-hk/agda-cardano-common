#!/usr/bin/env python3
"""Bounded T5.2.2 barrier/fault/credit experiments, not arbitrary-log replay or liveness proofs."""
import argparse
import importlib.util
import json
from pathlib import Path
import platform

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'src/csp-ptree.agda-lib').is_file())
CASES = ['blocked-next-quit', 'held-send-release', 'held-send-cancel', 'send-exception',
         'next-exception', 'admission-exception', 'handler-exception', 'handler-init-exception',
         'checkdone-exception', 'held-handler-release', 'held-handler-cancel',
         'capacity-empty', 'capacity-queued', 'credit-queue-drain']
SUCCESS = {'blocked-next-quit', 'held-send-release', 'held-handler-release', 'capacity-empty',
           'capacity-queued', 'credit-queue-drain'}


def helpers():
    spec = importlib.util.spec_from_file_location('history_helpers', HERE / 'completion_history.py')
    h = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(h)
    return h


def build(args, out, opt, h):
    f = h.load_fixture()
    original = f.prepare
    audit = {}

    def prepare(arguments, destination):
        src, typed, network = original(arguments, destination)
        source = (HERE / 'Main.hs').read_text()
        h.require(source.count('module Main where') == 1, 'unexpected base fixture module')
        (src / 'FixtureBase.hs').write_text(source.replace('module Main where', 'module FixtureBase where'))
        audit['base_helper_sha256'] = h.file_hash(src / 'FixtureBase.hs')
        pins = json.loads((ROOT / 'src/Cardano_network/LeiosNotifyPipeLookahead/sources.json').read_text())
        paths = {'node-wiring': 'ouroboros-consensus-diffusion/src/ouroboros-consensus-diffusion/Ouroboros/Consensus/Network/NodeToNode.hs',
                 'announcement-enqueue': 'ouroboros-consensus/src/ouroboros-consensus/LeiosDemoLogic/Announcements.hs'}
        for tag, path in paths.items():
            data = f.git_bytes(args.consensus, f.CONSENSUS, path)
            target = out / (tag + '.hs')
            target.write_bytes(data)
            h.require(h.file_hash(target) == next(p['sha256'] for p in pins if p['source'] == tag), 'callback source pin mismatch')
            audit[tag + '_sha256'] = h.file_hash(target)
        return src, typed, network

    def command(argv, log, cwd=None, timeout=300):
        if str(argv[0]) == 'ghc':
            argv = [opt if x == '-O0' else x for x in argv]
        result = h.bounded_command(argv, log, cwd=cwd, timeout=timeout)
        if str(argv[0]) == 'ghc':
            (out / 'ghc-command.json').write_text(json.dumps(result['argv'], indent=2) + '\n')
        return result

    out.mkdir(parents=True, exist_ok=False)
    f.prepare, f.command = prepare, command
    compiler = f.build(args, out, main_source=HERE / 'FailureSchedules.hs', executable='failure-schedules')
    return {'compiler': compiler, 'optimization': opt, **audit,
            'command_sha256': h.file_hash(out / 'ghc-command.json'),
            'exported_sources_sha256': h.file_hash(out / 'source-hashes.json')}


def validate(path, case, h):
    events, snapshots, passed, final_credit = [], {}, 0, None
    for row in path.read_text().splitlines():
        parts = row.split('\t')
        if parts == ['PASS']:
            passed += 1
        elif parts[0] == 'M':
            h.require(len(parts) == 4, 'bad snapshot row')
            _, phase, key, value = parts
            fields = snapshots.setdefault(phase, {})
            h.require(key not in fields, 'duplicate snapshot metric')
            fields[key] = int(value)
        else:
            h.require(len(parts) == 6 and parts[0] == case and int(parts[1]) == len(events), 'bad event row')
            _, _, actor, kind, payload, thread = parts
            h.require(final_credit is None, 'event after final credit')
            if kind == 'FinalCredit':
                final_credit = int(payload)
            else:
                events.append((actor, kind, payload))
    h.require(passed == 1 and final_credit is not None, 'missing PASS/final credit')
    final = snapshots.get('final', {})
    keys = {'admitted', 'free', 'enqueued', 'taken', 'queued', 'rejected', 'handler_entered', 'handler_exited', 'handled'}
    for fields in snapshots.values():
        h.require(set(fields) == keys and min(fields.values()) >= 0, 'invalid snapshot fields')
        h.require(fields['free'] + fields['enqueued'] == fields['admitted'] and
                  fields['queued'] == fields['enqueued'] - fields['taken'] and
                  fields['handler_exited'] <= fields['handler_entered'], 'credit/queue/handler conservation mismatch')
    n = 1000 if case.startswith('capacity-') else 1
    enqueued = 1000 if case == 'capacity-queued' else int(case in {
        'held-send-release', 'held-send-cancel', 'send-exception', 'handler-exception', 'handler-init-exception',
        'held-handler-release', 'held-handler-cancel', 'credit-queue-drain'})
    taken = 0 if case == 'capacity-queued' else enqueued
    admits = 0 if case == 'admission-exception' else n
    enters = int(case in {'handler-exception', 'held-handler-release', 'held-handler-cancel', 'credit-queue-drain'})
    handled = int(case in {'held-handler-release', 'credit-queue-drain'})
    expected = dict(zip(['admitted', 'free', 'enqueued', 'taken', 'queued', 'rejected', 'handler_entered', 'handler_exited', 'handled'],
                        [admits, admits-enqueued, enqueued, taken, enqueued-taken, 2 if case == 'capacity-queued' else 1, enters, enters, handled]))
    h.require(final == expected and final_credit == final['free'], 'wrong final ledger')
    def count(actor, kind, payload):return events.count((actor, kind, payload))
    def has(actor, kind, payload):h.require(count(actor, kind, payload) == 1, 'missing/nonunique event: '+str((actor,kind,payload)))
    def pos(actor, kind, payload):has(actor,kind,payload);return events.index((actor,kind,payload))
    has('controller', 'Cleanup', 'QueueContentsChecked')
    has('controller', 'Snapshot', 'final')
    normal = int(case in {'held-send-release', 'handler-exception', 'handler-init-exception',
                         'held-handler-release', 'held-handler-cancel', 'credit-queue-drain'})
    canceled = n if case in {'blocked-next-quit', 'capacity-empty', 'capacity-queued'} else 0
    quit_sent = int(case in SUCCESS or case in {'held-send-cancel', 'send-exception', 'held-handler-cancel'})
    done_sent = int(case in SUCCESS or case == 'held-handler-cancel')
    done_recv = int(case in SUCCESS)
    expected_wire = {('client','Send','RequestNext'):n, ('server','Recv','RequestNext'):n,
                     ('client','Send','Quit'):quit_sent, ('server','Recv','Quit'):quit_sent,
                     ('server','Send','Canceled'):canceled, ('client','Recv','Canceled'):canceled,
                     ('server','Send','Offer:1:1:53'):normal, ('client','Recv','Offer:1:1:53'):normal,
                     ('server','Send','Done'):done_sent, ('client','Recv','Done'):done_recv}
    for key, value in expected_wire.items():h.require(count(*key) == value, 'wrong wire count: '+str(key))
    h.require(sum(v for v in expected_wire.values()) == sum(k in ['Send','Recv'] for _,k,_ in events), 'unexpected wire message')
    if case in SUCCESS:has('controller','Outcome','BothDone')
    fault_map = {'admission-exception':('server','admission'), 'next-exception':('server','next'),
                 'send-exception':('server','send'), 'checkdone-exception':('client','checkdone'),
                 'handler-exception':('client','handler'), 'handler-init-exception':('client','handler-init')}
    if case in fault_map:
        actor, marker = fault_map[case]
        has(actor,'Outcome','Fault:'+marker)
        has('client' if actor == 'server' else 'server', 'Outcome', 'ControllerCanceled')
    if case == 'held-send-cancel':
        for actor in ['server','client']:has(actor,'Outcome','ControllerCanceled')
    if case == 'held-handler-cancel':has('client','Outcome','ControllerCanceled')
    if case != 'admission-exception':has('controller','Cleanup','SenderExited')
    if enters:has('controller','Cleanup','ReceiverExited')
    if case in {'blocked-next-quit','next-exception','checkdone-exception','capacity-empty','capacity-queued'}:
        has('controller','Checkpoint','NextBlocked')
    if case.startswith('held-send-') or case == 'send-exception':
        points=[('server','Hook','SelectedBeforeCommit'),('controller','Checkpoint','SendBlocked'),
                ('server','Hook','QuitEffectCompleted'),('controller','Checkpoint','SendStillBlockedAfterFlag'),
                ('controller','Snapshot','held-after-flag')]
        indices=[pos(*key) for key in points]
        h.require(indices == sorted(indices), 'held-send barrier ordering mismatch')
        h.require(snapshots['held-after-flag']['taken'] == 1 and snapshots['held-after-flag']['handled'] == 0, 'wrong held-send checkpoint')
        if case != 'held-send-cancel':
            h.require(pos('controller','Release','Gate') > indices[-1], 'gate released before checkpoint')
        if case == 'held-send-release':
            h.require(pos('server','Send','Offer:1:1:53') > pos('controller','Release','Gate'), 'send before release')
    if case in {'held-handler-release','held-handler-cancel'}:
        h.require(pos('client','Hook','HandlerEntered') < pos('controller','Checkpoint','HandlerBlocked') <
                  pos('server','Hook','QuitEffectCompleted') < pos('server','Outcome','ServerDoneWhileHandlerHeld') <
                  pos('controller','Checkpoint','HandlerStillBlockedAfterServerReturn'), 'held-handler barrier ordering mismatch')
        h.require(snapshots['server-returned-handler-held']['handler_exited'] == 0, 'handler exited at held checkpoint')
        if case == 'held-handler-release':
            h.require(pos('controller','Release','Gate') < pos('client','Hook','HandlerExited'), 'handler exited before release')
    return {'wire_rows':sum(expected_wire.values()), 'final_ledger':final, 'snapshots':snapshots,
            'outcomes':[list(e) for e in events if e[1]=='Outcome'],
            'checkpoint_labels':[e[2] for e in events if e[1]=='Checkpoint']}


def negatives(report, out, h):
    result=[]
    for name, case, old, new in [
        ('missing-pass','blocked-next-quit','PASS\n',''),
        ('false-empty-queue','capacity-queued','M\tfinal\tqueued\t1000\n','M\tfinal\tqueued\t0\n'),
        ('missing-worker-cleanup','held-send-cancel','\tCleanup\tSenderExited\t','\tCleanup\tOther\t'),
        ('failure-as-success','send-exception','\tOutcome\tFault:send\t','\tOutcome\tBothDone\t')]:
        sample=next((r for r in report['runs'] if r['case']==case),None)
        if sample is None:continue
        data=(out/(sample['name']+'.tsv')).read_text();changed=data.replace(old,new,1)
        h.require(changed!=data,'negative did not mutate capture')
        path=out/('negative-'+name+'.tsv');path.write_text(changed)
        try:validate(path,case,h)
        except ValueError as error:result.append({'name':name,'fixture_validation_rejected':True,'reason':str(error),'capture_sha256':h.file_hash(path)})
        else:raise ValueError('corrupted capture accepted: '+name)
    return result


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--consensus',type=Path,required=True);ap.add_argument('--typed-protocols',type=Path,required=True)
    ap.add_argument('--network-archive',type=Path,required=True)
    ap.add_argument('--package-db',type=Path,default=Path.home()/'.cabal/store/ghc-9.6.7/package.db')
    ap.add_argument('--build-packages',type=Path,default=HERE/'build-packages.json')
    ap.add_argument('--optimizations',nargs='+',choices=['O0','O2'],default=['O0','O2'])
    ap.add_argument('--capabilities',nargs='+',type=int,choices=[1,2],default=[1,2])
    ap.add_argument('--cases',nargs='+',choices=CASES,default=CASES);ap.add_argument('--repeat',type=int,default=3)
    ap.add_argument('--out',type=Path,required=True);args=ap.parse_args();h=helpers();out=args.out.resolve()
    h.require(not out.is_relative_to(ROOT),'artifacts must stay outside repository');h.require(args.repeat>0,'repeat must be positive')
    for xs in [args.optimizations,args.capabilities,args.cases]:h.require(len(set(xs))==len(xs),'duplicate sweep input')
    out.mkdir(parents=True,exist_ok=False)
    sources=[Path(__file__),HERE/'FailureSchedules.hs',HERE/'Main.hs',HERE/'run.py',HERE/'completion_history.py',args.build_packages]
    report={'scope':'T5.2.2 controlled source/driver behavior; no whole-node cleanup, permanent-deadlock or refinement claim',
            'system':platform.platform(),'source_hashes':{str(p.resolve().relative_to(ROOT)):h.file_hash(p) for p in sources},
            'builds':[],'runs':[],'complete':False}
    for opt in args.optimizations:
        directory=out/opt;report['builds'].append(build(args,directory,'-'+opt,h))
        for caps in args.capabilities:
            for case in args.cases:
                for repeat in range(args.repeat):
                    name=f'{opt}-N{caps}-{case}-r{repeat}';log=out/(name+'.tsv')
                    resources=h.bounded_command([directory/'failure-schedules',case,'+RTS',f'-N{caps}','-M256M','-K64M','-RTS'],log,timeout=40)
                    report['runs'].append({'name':name,'case':case,'optimization':'-'+opt,'capabilities':caps,'repeat':repeat,
                        'resources':resources,'capture_sha256':h.file_hash(log),**validate(log,case,h)})
                    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
                print(f'{opt} N{caps} {case}: passed',flush=True)
    report['negative_controls']=negatives(report,out,h);report['complete']=True
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('report:',out/'report.json',flush=True)


if __name__=='__main__':main()
