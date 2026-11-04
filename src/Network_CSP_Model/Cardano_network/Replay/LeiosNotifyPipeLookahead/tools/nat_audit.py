#!/usr/bin/env python3
"""Audit saved Nat closure chains and actual pinned-Core arithmetic in separate diagnostics.

No shipped peer or Agda model changes. Strict busy-loop forcing is a diagnostic
counterfactual; this does not certify a repair or seeded-edge reachability.
"""
import argparse
import difflib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / "src/csp-ptree.agda-lib").is_file())


def load_profile():
    spec = importlib.util.spec_from_file_location("profile_helpers", HERE / "completion_profile.py")
    p = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(p)
    return p


def observed_peer(path, strict):
    """Append a copied server with a lazy observer; force its argument only in strict mode."""
    source = path.read_text()
    name, new = "leiosNotifyServerPeerLookahead", "leiosNotifyServerPeerLookaheadObserved"
    start, end = source.index(name + " ::"), source.index("data ExnLeiosNotifyExcessiveRequests")
    body = source[start:end].replace(name, new)
    signature = "  (MonadThrow m, MonadSTM m) =>\n"
    assert body.count(signature) == 1
    body = body.replace(signature, signature + "  (forall k. Nat k -> m ()) ->\n")
    body = body.replace(new + " incr next =", new + " observeNat incr next =")
    begin, finish = body.index("  busy quitVar n =\n"), body.index("  -- on termination")
    block = body[begin:finish]
    original_rhs = block.removeprefix("  busy quitVar n =\n").rstrip("\n")
    replacement = "  busy quitVar " + ("!n" if strict else "n") + " = Effect $ do\n"
    replacement += "    observeNat n\n    pure $\n" + "\n".join("  " + line for line in original_rhs.splitlines()) + "\n\n"
    body = body[:begin] + replacement + body[finish:]
    export = "  , " + name + "\n"
    assert source.count(export) == 1
    patched = source.replace(export, export + "  , " + new + "\n")
    patched += "\n-- Separate Nat-root diagnostic; the original server remains unchanged.\n" + body
    assert patched.replace("  , " + new + "\n", "").split("\n-- Separate Nat-root diagnostic;")[0] == source
    path.write_text(patched)
    return "".join(difflib.unified_diff(source.splitlines(True), patched.splitlines(True),
                                        fromfile="pinned/Peer.hs", tofile="observed/Peer.hs"))


def build(args, out, opt, strict, p, h):
    fixture = h.load_fixture()
    original_prepare = fixture.prepare
    provenance = {}

    def prepare(arguments, destination):
        src, typed, network = original_prepare(arguments, destination)
        peer, driver = src / "LeiosDemoOnlyTestNotify.hs", typed / "src/Network/TypedProtocol/Driver.hs"
        provenance.update(original_peer_sha256=h.file_hash(peer), original_driver_sha256=h.file_hash(driver))
        (out / "peer-diagnostic.patch").write_text(observed_peer(peer, strict))
        (out / "driver-diagnostic.patch").write_text(p.diagnostic_driver(driver))
        # Reuse the earlier callbacks/limits configuration without changing its recorded source.
        quiet = (HERE / "CompletionProfile.hs").read_text()
        assert quiet.count("module Main where") == 1
        (src / "QuietProfile.hs").write_text(quiet.replace("module Main where", "module QuietProfile where"))
        provenance.update(compiled_peer_sha256=h.file_hash(peer), compiled_driver_sha256=h.file_hash(driver),
                          quiet_helper_sha256=h.file_hash(src / "QuietProfile.hs"))
        return src, typed, network

    def command(argv, log, cwd=None, timeout=300):
        compiler = str(argv[0]) == "ghc"
        if compiler:
            argv = [opt if x == "-O0" else x for x in argv]
            argv += ["-package", "ghc-heap", "-DCOMPLETION_DIAGNOSTIC"]
            if strict:
                argv += ["-DSTRICT_AUDIT"]
        result = h.bounded_command(argv, log, cwd=cwd, timeout=timeout)
        if compiler:
            (out / "ghc-command.json").write_text(json.dumps(result["argv"], indent=2) + "\n")
        return result

    out.mkdir(parents=True, exist_ok=False)
    fixture.prepare, fixture.command = prepare, command
    compiler = fixture.build(args, out, main_source=HERE / "NatAudit.hs", executable="nat-audit")
    provenance.update(compiler=compiler, optimization=opt, strict_busy=strict,
                      command_sha256=h.file_hash(out / "ghc-command.json"),
                      peer_patch_sha256=h.file_hash(out / "peer-diagnostic.patch"),
                      driver_patch_sha256=h.file_hash(out / "driver-diagnostic.patch"))
    # Compile the scalar arithmetic checks against the unmodified pinned Core from the same export.
    argv = json.loads((out / "ghc-command.json").read_text())
    argv = argv[:argv.index("+RTS")]
    argv[argv.index("-outputdir") + 1] = str(out / "arithmetic-build")
    argv[argv.index("-o") + 1] = str(out / "nat-arithmetic")
    argv[argv.index(str(HERE / "NatAudit.hs"))] = str(HERE / "NatArithmetic.hs")
    arithmetic = h.bounded_command(argv, out / "arithmetic-build.log")
    provenance["arithmetic_command_sha256"] = h.file_hash(out / "arithmetic-build.log.resources.json")
    return provenance


def measurements(path, h):
    result, builds, passed = {}, [], 0
    for line in path.read_text().splitlines():
        parts = line.split("\t")
        if parts == ["PASS"]:
            passed += 1
        elif parts[0] == "BUILD" and len(parts) == 2:
            builds.append(parts[1])
        else:
            h.require(len(parts) == 3 and parts[0] == "M" and parts[1] not in result, "bad heap sample row")
            result[parts[1]] = int(parts[2])
    h.require(passed == 1 and len(builds) == 1, "incomplete heap sample")
    return result, builds[0]


def validate(path, n, strict, force, h):
    x, mode = measurements(path, h)
    h.require(mode == ("strict-diagnostic" if strict else "lazy-diagnostic") and x['exchanges'] == n, "wrong heap sample configuration")
    h.require(x['completed_before'] == n and x['completed_after_intervention'] == n and x['completed_after_close'] == 0,
              "intervention changed completed bookkeeping")
    expected = 0 if strict or n == 0 else n - 1
    h.require(x['pre_dynamic_thunks'] == expected and x['inspected_dynamic_thunks'] == expected,
              "unexpected chain or heap inspection forced it")
    h.require(x['post_dynamic_thunks'] == (0 if force else expected), "wrong post-intervention thunk count")
    h.require(x['forced_value'] == (n - 1 if force and n else -1), "forced Nat value mismatch")
    for phase in ['pre', 'inspected', 'post']:
        h.require(x[phase+'_boxed_ints'] + x[phase+'_zero_pointer_thunk_leaves'] == (1 if n else 0), "unexpected terminal heap value")
        h.require(x[phase+'_dynamic_thunk_bytes'] == 24 * x[phase+'_dynamic_thunks'], "unexpected raw successor thunk size")
    if n and (strict or force):
        h.require(x['post_terminal_int'] == n - 1 and x['post_boxed_ints'] == 1, "wrong forced terminal Int")
    else:
        h.require(x['post_terminal_int'] in [0, -1], "wrong unforced base leaf")
    return x


def arithmetic(path, h):
    rows = {}
    for line in path.read_text().splitlines():
        if line == 'PASS':continue
        parts = line.split('\t')
        h.require(len(parts)==3 and parts[1] not in rows, "bad arithmetic output")
        rows[parts[1]] = parts[0], parts[2]
    bits=int(rows['int_bits'][1]); maximum=2**(bits-1)-1; minimum=-2**(bits-1)
    expected={'int_max':maximum,'int_min':minimum,'nat_succ_3':4,'nat_succ_max_minus_one':maximum,
              'raw_int_plus_one_max':minimum,'raw_int_minus_one_min':maximum,'nat_negative_predecessor':-2}
    for name,value in expected.items():h.require(rows[name]==('V',str(value)), "arithmetic value mismatch: "+name)
    for name,needle in [('nat_succ_max','succ'),('nat_min_predecessor','pred'),('force_bottom','heap_probe_bottom')]:
        h.require(rows[name][0]=='E' and needle in rows[name][1], "arithmetic exception mismatch: "+name)
    for name in ['delayed_nat_succ','bottom_not_forced']:
        h.require(rows[name][0]=='H' and rows[name][1].startswith('THUNK'), "inspection forced delayed input")
    h.require(path.read_text().splitlines()[-1]=='PASS', "arithmetic fixture incomplete")
    return {'bits':bits,'results':rows}


def negative_controls(report, out, h):
    """Reject fabricated chain sizes, forced inspection and changed completed work."""
    source = next((x for x in report['runs'] if not x['strict_busy'] and not x['force_checkpoint'] and x['exchanges'] > 1), None)
    if source is None:
        return []
    data = (out / (source['name'] + '.tsv')).read_text()
    results = []
    for name, field, replacement in [
        ('extra-thunk', 'pre_dynamic_thunks', source['exchanges']),
        ('wrong-object-size', 'pre_dynamic_thunk_bytes', 0),
        ('inspection-forced-root', 'inspected_dynamic_thunks', 0),
        ('changed-completion-count', 'completed_after_intervention', 0),
    ]:
        prefix = 'M\t' + field + '\t'
        mutated = '\n'.join(prefix + str(replacement) if row.startswith(prefix) else row
                            for row in data.splitlines()) + '\n'
        h.require(mutated != data, 'negative control did not change its capture')
        path = out / ('negative-' + name + '.tsv')
        path.write_text(mutated)
        try:
            validate(path, source['exchanges'], False, False, h)
        except ValueError as error:
            results.append({'name': name, 'fixture_validation_rejected': True, 'reason': str(error),
                            'capture_sha256': h.file_hash(path)})
        else:
            raise ValueError('negative control accepted: ' + name)
    return results


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--consensus',type=Path,required=True);ap.add_argument('--typed-protocols',type=Path,required=True)
    ap.add_argument('--network-archive',type=Path,required=True)
    ap.add_argument('--package-db',type=Path,default=Path.home()/'.cabal/store/ghc-9.6.7/package.db')
    ap.add_argument('--build-packages',type=Path,default=HERE/'build-packages.json')
    ap.add_argument('--counts',nargs='+',type=int,default=[0,1,2,10,1000,10000,100000])
    ap.add_argument('--optimizations',nargs='+',choices=['O0','O2'],default=['O0','O2'])
    ap.add_argument('--capabilities',nargs='+',type=int,choices=[1,2],default=[1,2])
    ap.add_argument('--repeat',type=int,default=3);ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args();p=load_profile();h=p.helpers();out=args.out.resolve()
    h.require(not out.is_relative_to(ROOT),'artifacts must stay outside repository')
    h.require(args.repeat>0 and args.counts and all(0<=n<=100000 for n in args.counts),'invalid audit input')
    for xs in [args.counts,args.optimizations,args.capabilities]:h.require(len(xs)==len(set(xs)),'duplicate sweep input')
    out.mkdir(parents=True,exist_ok=False)
    paths=[Path(__file__),HERE/'NatAudit.hs',HERE/'NatArithmetic.hs',HERE/'CompletionProfile.hs',HERE/'completion_profile.py',HERE/'completion_history.py',HERE/'run.py',args.build_packages]
    report={'scope':'T5.2.1 diagnostic object attribution and synthetic arithmetic; no repair/refinement claim',
            'source_hashes':{str(z.resolve().relative_to(ROOT)) if z.resolve().is_relative_to(ROOT) else str(z.resolve()):h.file_hash(z) for z in paths},
            'builds':[],'runs':[],'arithmetic':[],'complete':False}
    for opt in args.optimizations:
        binaries={}
        for strict in [False,True]:
            label='strict' if strict else 'lazy';d=out/f'{label}-{opt}'
            report['builds'].append(build(args,d,'-'+opt,strict,p,h));binaries[strict]=d/'nat-audit'
            log=d/'arithmetic.tsv';resources=h.bounded_command([d/'nat-arithmetic','+RTS','-M256M','-K64M','-RTS'],log,timeout=30)
            report['arithmetic'].append({'optimization':'-'+opt,'strict_build':strict,'resources':resources,**arithmetic(log,h)})
        for caps in args.capabilities:
            for n in args.counts:
                for repeat in range(args.repeat):
                    for strict,force in [(False,False),(False,True),(True,False)]:
                        name=f'{opt}-N{caps}-n{n}-r{repeat}-'+('strict' if strict else 'force' if force else 'peek')
                        log=out/(name+'.tsv');resources=h.bounded_command([binaries[strict],n,1000,'force' if force else 'peek',
                            '+RTS',f'-N{caps}','-T','-M256M','-K64M','-RTS'],log,timeout=150)
                        x=validate(log,n,strict,force,h)
                        report['runs'].append({'name':name,'optimization':'-'+opt,'capabilities':caps,'exchanges':n,'repeat':repeat,
                            'strict_busy':strict,'force_checkpoint':force,'measurements':x,'resources':resources,'capture_sha256':h.file_hash(log)})
                        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
                print(f'{opt} N{caps} n={n}: peek/force/strict checks passed',flush=True)
    report['negative_controls'] = negative_controls(report, out, h)
    report['complete']=True;(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'report: {out / "report.json"}',flush=True)


if __name__=='__main__':main()
