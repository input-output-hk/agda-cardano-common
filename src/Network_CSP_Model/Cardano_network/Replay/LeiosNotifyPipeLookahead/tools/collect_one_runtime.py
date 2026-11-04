#!/usr/bin/env python3
"""T6.3.1 fresh baseline/CollectOne actual-driver comparisons; no arbitrary-log certificate."""
import argparse
import difflib
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import statistics

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / 'src/csp-ptree.agda-lib').is_file())
VARIANTS = ('baseline', 'collect-one')


def load(name):
    spec = importlib.util.spec_from_file_location('collect_one_' + name, HERE / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError('fixture source boundary changed: ' + old)
    return source.replace(old, new)


def selected(source, variant):
    if variant == 'collect-one':
        source = replace_once(source, 'leiosNotifyServerPeerLookahead (', 'leiosNotifyServerPeerLookaheadCollectOne (')
    return source


def build(args, out, opt, variant, fixture, h, profile, design):
    """Fresh isolated sources; keep original entry points and select the candidate in fixture copies."""
    f = h.load_fixture()
    original_prepare = f.prepare
    kind = 'profile' if fixture == 'diagnostic' else fixture
    filename = {'schedules': 'Main.hs', 'failures': 'FailureSchedules.hs',
                'history': 'CompletionHistory.hs', 'profile': 'CompletionProfile.hs'}[kind]
    out.mkdir(parents=True, exist_ok=False)
    source = selected((HERE / filename).read_text(), variant)
    if fixture == 'diagnostic' and variant == 'collect-one':
        # Unlike the original history counter, completed tokens are consumed early.
        # This readiness waits for at least one retirement, not necessarily the last one.
        source = replace_once(source,
            'STM.check (waiting == 0 && completed == fromIntegral (target lab))',
            'STM.check (waiting == 0 && completed <= 1005 &&\n'
            '    (if target lab == 0 then completed == 0 else completed > 0))')
        source = replace_once(source,
            'unless (w == 0 && c == fromIntegral n && w\' == 0 && c\' == 0)',
            'unless (w == 0 && c <= 1005 && (if n == 0 then c == 0 else c > 0) && w\' == 0 && c\' == 0)')
    main = out / 'FixtureMain.hs'
    main.write_text(source)
    (out / 'fixture.patch').write_text(''.join(difflib.unified_diff(
        (HERE / filename).read_text().splitlines(True), source.splitlines(True),
        fromfile='original/' + filename, tofile='selected/FixtureMain.hs')))
    provenance = {}

    def prepare(arguments, destination):
        src, typed, network = original_prepare(arguments, destination)
        peer = src / 'LeiosDemoOnlyTestNotify.hs'
        driver = typed / 'src/Network/TypedProtocol/Driver.hs'
        provenance.update(original_peer_sha256=h.file_hash(peer), original_driver_sha256=h.file_hash(driver))
        if variant == 'collect-one':
            (out / 'candidate.patch').write_text(design.candidate(peer))
        if fixture == 'diagnostic':
            (out / 'diagnostic-driver.patch').write_text(profile.diagnostic_driver(driver))
        if fixture == 'failures':
            base = selected((HERE / 'Main.hs').read_text(), variant)
            (src / 'FixtureBase.hs').write_text(replace_once(base, 'module Main where', 'module FixtureBase where'))
        provenance.update(compiled_peer_sha256=h.file_hash(peer), compiled_driver_sha256=h.file_hash(driver))
        return src, typed, network

    def command(argv, log, cwd=None, timeout=300):
        if str(argv[0]) == 'ghc':
            argv = [('-' + opt) if x == '-O0' else x for x in argv]
            if fixture == 'diagnostic':
                argv += ['-DCOMPLETION_DIAGNOSTIC']
        result = h.bounded_command(argv, log, cwd=cwd, timeout=timeout)
        if str(argv[0]) == 'ghc':
            (out / 'ghc-command.json').write_text(json.dumps(result['argv'], indent=2) + '\n')
        return result

    f.prepare, f.command = prepare, command
    compiler = f.build(args, out, main_source=main, executable='fixture')
    if variant == 'baseline':
        h.require(provenance['original_peer_sha256'] == provenance['compiled_peer_sha256'], 'baseline peer changed')
    if fixture != 'diagnostic':
        h.require(provenance['original_driver_sha256'] == provenance['compiled_driver_sha256'], 'quiet driver changed')
    return dict(optimization=opt, variant=variant, fixture=fixture, compiler=compiler,
                executable=str(out / 'fixture'), executable_sha256=h.file_hash(out / 'fixture'),
                main_sha256=h.file_hash(main), command_sha256=h.file_hash(out / 'ghc-command.json'),
                source_manifest_sha256=h.file_hash(out / 'source-hashes.json'), **provenance)


def streams(rows):
    """Retain exact per-endpoint wire order; independent interleavings need not match globally."""
    return {actor + '-' + kind: hashlib.sha256(''.join(
        payload + '\n' for a, k, payload, *_ in rows if a == actor and k == kind).encode()).hexdigest()
        for actor in ('client', 'server') for kind in ('Send', 'Recv')}


def history_validate(path, n, depth, observed, variant, h):
    phases, wire, passed = {}, [], 0
    for line in path.read_text().splitlines():
        parts = line.split('\t')
        if parts == ['PASS']:
            passed += 1
        elif len(parts) == 4 and parts[0] == 'S':
            _, phase, key, value = parts
            h.require(key not in phases.setdefault(phase, {}), 'duplicate history snapshot field')
            phases[phase][key] = int(value)
        else:
            h.require(len(parts) == 5 and parts[0] == 'W' and int(parts[1]) == len(wire), 'invalid history row')
            wire.append(tuple(parts[2:]))
    h.require(passed == 1 and len(wire) == 4*n+4, 'incomplete history capture')
    for actor, kind in [('client','Send'),('server','Recv'),('server','Send'),('client','Recv')]:
        request = (actor, kind) in [('client','Send'),('server','Recv')]
        expected = (['RequestNext']*n + ['Quit']) if request else ([f'Offer:{i}:{i}:53' for i in range(1,n+1)] + ['Done'])
        h.require([p for a,k,p in wire if (a,k)==(actor,kind)] == expected, 'wrong endpoint history or exact payload')
    final = phases.get('final', {})
    h.require(all(final.get(k) == n for k in ['request_sends','request_receives','reply_sends','reply_receives','handled'])
              and final.get('free_credits') == 0, 'bad final history ledger')
    if observed:
        h.require(set(phases) == {'client-before-quit','server-recv-quit','final'}, 'missing observer checkpoint')
        before, received = phases['client-before-quit'], phases['server-recv-quit']
        for snapshot in (before, received):
            h.require(snapshot['registered_jobs'] == n, 'wrong registration count')
            if variant == 'baseline':
                h.require(snapshot['flush_entered'] == snapshot['flush_returned'] == 0, 'baseline early collection')
            else:
                h.require(snapshot['flush_entered'] == max(0,n-1) and
                          0 <= snapshot['flush_returned'] <= snapshot['flush_entered'] and
                          n-snapshot['flush_returned'] <= 1005, 'bad candidate poll/inventory accounting')
        h.require(before['flush_returned'] == received['flush_returned'], 'collection between Quit checkpoints')
        early = before['flush_returned']
        attempts = before['flush_entered']
        h.require(final['registered_jobs'] == final['flush_returned'] == n and
                  final['flush_entered'] == attempts+n-early, 'wrong complete collection accounting')
        marker = int(before['client_outstanding'] > 0)
        h.require(final['client_jobs'] == final['client_results'] == n+marker and final['client_outstanding'] == 0,
                  'receiver/marker accounting mismatch')
        limit = 1 if depth == 1 else 2
        h.require(final['peak_before_quit'] <= limit and final['peak_overall'] <= limit+1, 'client occupancy changed')
        accounting = dict(early_attempts=attempts, early_hits=early, early_misses=attempts-early,
                          registered_unflushed_before_quit=n-early, final_flushes=n-early)
    else:
        h.require(set(phases) == {'final'} and all(final[k] == 0 for k in
            ['registered_jobs','flush_entered','flush_returned','client_jobs','client_results']), 'observer in wire-only control')
        accounting = None
    return dict(snapshots=phases, endpoint_stream_sha256=streams(wire), wire_rows=len(wire), accounting=accounting)


def profile_validate(path, n, depth, diagnostic, variant, h, profile):
    """Quiet validation is identical; candidate diagnostic has an explicitly different retirement gate."""
    if not diagnostic or variant == 'baseline':
        return profile.validate(path, n, depth, 'diagnostic' if diagnostic else 'baseline', h)
    rows = [line.split('\t') for line in path.read_text().splitlines()]
    h.require(rows.count(['PASS']) == 1 and rows.count(['BUILD','diagnostic']) == 1, 'missing diagnostic outcome')
    fields = [r for r in rows if r[0] == 'M']
    h.require(all(len(r) == 3 for r in fields) and len(fields) == len({r[1] for r in fields}), 'duplicate diagnostic metric')
    values = {key:int(value) for _,key,value in fields}
    h.require(values['exchanges'] == n and values['depth'] == depth, 'wrong diagnostic configuration')
    h.require(all(values[k] == n for k in ['request_sends','request_receives','reply_sends','reply_receives','handled']), 'incomplete diagnostic')
    h.require(values['free_credits'] == 0 and values['shutdown_ns'] > 0 and
              values['allocated_post_bytes'] >= values['allocated_pre_bytes'] and
              values['shutdown_allocated_bytes'] == values['allocated_post_bytes']-values['allocated_pre_bytes'], 'bad diagnostic accounting')
    h.require(values['pre_gc_generation'] == values['post_gc_generation'] == 1 and
              values['post_major_gcs'] > values['pre_major_gcs'] >= 1 and
              values['max_live_bytes'] >= max(values['pre_live_bytes'],values['post_live_bytes']), 'bad diagnostic GC sample')
    h.require(values['private_pre_waiting'] == values['private_post_waiting'] == values['private_post_completed'] == 0 and
              (values['private_pre_completed'] == 0 if n == 0 else 1 <= values['private_pre_completed'] <= min(n,1005)),
              'candidate private counter bound/drain failed')
    return values


def summarize_profiles(runs):
    summary = []
    keys = sorted({(r['optimization'],r['variant'],r['diagnostic'],r['capabilities'],r['depth'],r['exchanges']) for r in runs})
    for opt, variant, diagnostic, caps, depth, n in keys:
        samples = [r['measurements'] for r in runs if
                   (r['optimization'],r['variant'],r['diagnostic'],r['capabilities'],r['depth'],r['exchanges']) ==
                   (opt,variant,diagnostic,caps,depth,n)]
        row = dict(optimization=opt,variant=variant,diagnostic=diagnostic,capabilities=caps,depth=depth,exchanges=n,samples=len(samples))
        for field in ['pre_live_bytes','post_live_bytes','shutdown_ns','shutdown_allocated_bytes','allocated_post_bytes']:
            values = [s[field] for s in samples]
            row[field] = dict(min=min(values),median=statistics.median(values),max=max(values))
        summary.append(row)
    return summary


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--consensus', type=Path, required=True)
    ap.add_argument('--typed-protocols', type=Path, required=True)
    ap.add_argument('--network-archive', type=Path, required=True)
    ap.add_argument('--package-db', type=Path, default=Path.home()/'.cabal/store/ghc-9.6.7/package.db')
    ap.add_argument('--build-packages', type=Path, default=HERE/'build-packages.json')
    ap.add_argument('--optimizations', nargs='+', choices=['O0','O2'], default=['O0','O2'])
    ap.add_argument('--capabilities', nargs='+', type=int, choices=[1,2], default=[1,2])
    ap.add_argument('--depths', nargs='+', type=int, choices=[1,1000], default=[1,1000])
    ap.add_argument('--history-counts', nargs='+', type=int, default=[0,1,10,1000,10000])
    ap.add_argument('--profile-counts', nargs='+', type=int, default=[0,1000,10000,100000])
    ap.add_argument('--repeat', type=int, default=3)
    ap.add_argument('--stages', nargs='+', choices=['schedules','failures','history','profiles'], default=['schedules','failures','history','profiles'])
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    h, failure, profile, design = [load(n) for n in ('completion_history','failure_schedules','completion_profile','collect_one_design')]
    f = h.load_fixture()
    out = args.out.resolve()
    h.require(not out.is_relative_to(ROOT) and args.repeat > 0, 'invalid artifact directory/repeat')
    for xs in (args.optimizations,args.capabilities,args.depths,args.history_counts,args.profile_counts,args.stages):
        h.require(xs and len(set(xs)) == len(xs), 'empty/duplicate sweep input')
    h.require(all(0 <= n <= 1000000 for n in args.history_counts+args.profile_counts), 'invalid exchange count')
    out.mkdir(parents=True, exist_ok=False)
    (out/'runs').mkdir(); (out/'controls').mkdir()
    sources = [Path(__file__),*(HERE/(n+'.py') for n in ['run','completion_history','completion_profile','failure_schedules','collect_one_design']),
               *(HERE/(n+'.hs') for n in ['Main','FailureSchedules','CompletionHistory','CompletionProfile']),args.build_packages]
    report = dict(scope='T6.3.1 finite actual pinned-driver comparison; no new Agda certificate, Haskell refinement or arbitrary-log verdict',
        system=dict(platform=platform.platform(),cpu_count=os.cpu_count(),load_before=os.getloadavg(),GHCRTS=os.environ.get('GHCRTS')),
        source_hashes={str(p.resolve().relative_to(ROOT)):h.file_hash(p) for p in sources},
        configuration={k:v for k,v in vars(args).items() if k in ['optimizations','capabilities','depths','history_counts','profile_counts','repeat','stages']},
        builds=[],schedules=[],failures=[],histories=[],profiles=[],negative_controls=[],complete=False)

    def save():
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')

    def binary(opt, variant, fixture):
        item = build(args,out/'builds'/opt/variant/fixture,opt,variant,fixture,h,profile,design)
        report['builds'].append(item); save()
        print(f'built {opt} {variant} {fixture}',flush=True)
        return Path(item['executable'])

    def capture(executable, argv, label, timeout=150, stats=False):
        log = out/'runs'/(label+'.tsv')
        caps = argv[-1]; inputs = argv[:-1]
        resources = h.bounded_command([executable,*inputs,'+RTS',f'-N{caps}',*(['-T'] if stats else []),
                                        '-M256M','-K64M','-RTS'],log,timeout=timeout)
        return log,dict(name=label,capture_sha256=h.file_hash(log),resources=resources)

    def reject(name, data, validator):
        path = out/'controls'/(name+'.tsv');path.write_text(data)
        try:
            validator(path)
        except ValueError as error:
            report['negative_controls'].append(dict(name=name,rejected=True,reason=str(error),capture_sha256=h.file_hash(path)))
        else:
            raise ValueError('corruption control accepted: '+name)

    save()
    for opt in args.optimizations:
        if 'schedules' in args.stages:
            binaries = {v:binary(opt,v,'schedules') for v in VARIANTS}
            for caps in args.capabilities:
                for repetition in range(args.repeat):
                    compared = {}
                    for variant in VARIANTS:
                        log,item = capture(binaries[variant],[caps],f'{opt}-{variant}-schedules-N{caps}-r{repetition}',75)
                        cases = f.parse(log.read_text()); checked = f.validate(cases,{})
                        projections = {case:streams(rows) for case,rows in cases.items()}
                        compared[variant] = projections
                        report['schedules'].append(dict(item,optimization=opt,variant=variant,capabilities=caps,repeat=repetition,
                                                       cases=checked,endpoint_stream_sha256=projections))
                        # Use the fresh baseline exact rows as controls for deliberately ordered cases.
                        if variant == 'baseline':
                            expected = {case:[row[:3] for row in cases[case] if row[1] in ('Send','Recv')] for case in f.MODEL_CASES}
                            report['negative_controls'].append(dict(name=f'{opt}-N{caps}-r{repetition}-schedule-wire-controls',
                                                                 rejected=f.negative_controls(cases,expected)))
                        save()
                    h.require(compared['baseline'] == compared['collect-one'],'baseline/candidate schedule endpoint streams differ')
            print(f'{opt}: all eight paired/adversarial schedule comparisons passed',flush=True)
        if 'failures' in args.stages:
            binaries = {v:binary(opt,v,'failures') for v in VARIANTS}
            for caps in args.capabilities:
                for case in failure.CASES:
                    for repetition in range(args.repeat):
                        for variant in VARIANTS:
                            log,item = capture(binaries[variant],[case,caps],f'{opt}-{variant}-{case}-N{caps}-r{repetition}',40)
                            checked = failure.validate(log,case,h)
                            report['failures'].append(dict(item,optimization=opt,variant=variant,capabilities=caps,case=case,repeat=repetition,**checked))
                            if repetition == 0 and caps == args.capabilities[0] and case == 'held-send-cancel':
                                data = log.read_text();changed=data.replace('\tCleanup\tSenderExited\t','\tCleanup\tOther\t',1)
                                h.require(changed!=data,'unchanged failure control')
                                reject(f'{opt}-{variant}-missing-worker-cleanup',changed,lambda p:failure.validate(p,case,h))
                            save()
                    print(f'{opt} N{caps} {case}: baseline/candidate passed',flush=True)
        if 'history' in args.stages:
            binaries = {v:binary(opt,v,'history') for v in VARIANTS}
            for caps in args.capabilities:
                for depth in args.depths:
                    for n in args.history_counts:
                        for repetition in range(args.repeat):
                            projections = []
                            for variant in VARIANTS:
                                for mode in ('observed','wire-only'):
                                    log,item=capture(binaries[variant],[n,depth,mode,caps],f'{opt}-{variant}-history-N{caps}-d{depth}-n{n}-r{repetition}-{mode}')
                                    checked=history_validate(log,n,depth,mode=='observed',variant,h)
                                    projections.append(checked['endpoint_stream_sha256'])
                                    report['histories'].append(dict(item,optimization=opt,variant=variant,capabilities=caps,depth=depth,
                                        exchanges=n,repeat=repetition,mode=mode,**checked))
                                    if n>0 and repetition==0 and caps==args.capabilities[0] and depth==args.depths[0] and mode=='observed':
                                        changed=log.read_text().replace('Offer:1:1:53','Offer:1:1:54',1)
                                        reject(f'{opt}-{variant}-history-payload-n{n}',changed,lambda p:history_validate(p,n,depth,True,variant,h))
                                    save()
                            h.require(all(p==projections[0] for p in projections),'observed/wire-only/baseline/candidate histories differ')
                        print(f'{opt} N{caps} depth={depth} history={n}: accounting/endpoint controls passed',flush=True)
        if 'profiles' in args.stages:
            binaries={(v,d):binary(opt,v,'diagnostic' if d else 'profile') for v in VARIANTS for d in (False,True)}
            for caps in args.capabilities:
                for depth in args.depths:
                    for n in args.profile_counts:
                        for repetition in range(args.repeat):
                            variants = VARIANTS if repetition%2==0 else tuple(reversed(VARIANTS))
                            for diagnostic in (False,True):
                                for variant in variants:
                                    log,item=capture(binaries[variant,diagnostic],[n,depth,caps],
                                        f'{opt}-{variant}-profile-N{caps}-d{depth}-n{n}-r{repetition}-diag{int(diagnostic)}',stats=True)
                                    values=profile_validate(log,n,depth,diagnostic,variant,h,profile)
                                    report['profiles'].append(dict(item,optimization=opt,variant=variant,capabilities=caps,depth=depth,
                                        exchanges=n,repeat=repetition,diagnostic=diagnostic,measurements=values))
                                    if repetition==0 and caps==args.capabilities[0] and depth==args.depths[0] and n==args.profile_counts[0]:
                                        changed='\n'.join('M\tshutdown_ns\t-1' if x.startswith('M\tshutdown_ns\t') else x for x in log.read_text().splitlines())+'\n'
                                        reject(f'{opt}-{variant}-negative-time-diag{int(diagnostic)}',changed,
                                               lambda p:profile_validate(p,n,depth,diagnostic,variant,h,profile))
                                    save()
                        print(f'{opt} N{caps} depth={depth} profile={n}: quiet/diagnostic baseline/candidate passed',flush=True)
    report['profile_summary']=summarize_profiles(report['profiles'])
    report['system']['load_after']=os.getloadavg()
    report['diagnostic_readiness']='Baseline waits for doneVar=n. Candidate waits for waiting=0 and, for n>0, 1<=doneVar<=1005; the last retirement may still be pending. Diagnostic performance is not compared. Quiet variants have identical readiness and no getter/peer observer.'
    report['complete']=True;save()
    print('report:',out/'report.json',flush=True)


if __name__ == '__main__':
    main()
