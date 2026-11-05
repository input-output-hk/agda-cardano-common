#!/usr/bin/env python3
"""Measure actual basis/ready/menu/ordering functions without protocol verdicts.

Uses a subset of exact committed cost-profile fixtures. Completed old/gated
pairs must retain counts and forcing sums; kernel equality is separate evidence.
Time/resource exhaustion is inconclusive and cannot mean model rejection.
"""
import argparse
from collections import Counter
from datetime import datetime,timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
TOOLS=HERE.parent
def load(name,path):
    """Reuse immutable fixture and resource producers without their entrypoints."""
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
PROFILE=load('menu_old_profile',TOOLS/'cost-profile/cost_profile.py')
COST,ROOT=PROFILE.COST,PROFILE.ROOT
SNAPSHOTS=('initial','claimed','selected','after-quit','closed','inactive-reader-claimed')
PAIRS=(('raw-ready','ready-gated'),('raw-menu','menu-gated'),('ordered-old','ordered-gated'))
MODES=('basis-only',)+tuple(mode for pair in PAIRS for mode in pair)
INPUT=re.compile(r'client-events=(\d+);server-events=(\d+);forcing-sum=(\d+)')
BASIS=re.compile(r'basis-count=(\d+);basis-sum=(\d+)')
RESULT=re.compile(r'stage=([^;]+);snapshot=([^;]+);requested-iterations=(\d+);executed-iterations=(\d+);targets=(\d+);state-sum=(\d+);position-sum=(\d+)')


def fixtures():
    """Use exact pipeline inputs at progressive sizes, without adding protocol records."""
    frozen={row['name']:row for row in json.loads((TOOLS/'cost-profile/fixtures-20261105.json').read_text())['cases']}
    generated=[]
    for count in (64,128,256,512,1024):
        for payloads in ('repeated','distinct'):
            if count==1024 and payloads=='distinct':continue
            name='pipeline_'+payloads+'_'+format(count,'06d')
            data=COST.workload('pipeline',count,payloads);text=COST.case_text(data,'paired')
            digest=hashlib.sha256(text.encode()).hexdigest();assert digest==frozen[name]['fixture_sha256']
            generated.append(dict(name=name,count=count,payloads=payloads,input=text,fixture_sha256=digest))
    return generated


def protect_old():
    """Freeze old tool evidence; do not reassert a historical production-import snapshot."""
    paths=[]
    for name in ('precheck','search-stress','shutdown-stress','cost-profile'):
        paths += sorted((TOOLS/name).iterdir())
    paths += [TOOLS/'replay_cost.py',TOOLS/'test_lookahead_cli.py']
    result={}
    for path in paths:
        if not path.is_file():raise ValueError('unexpected non-file in old evidence area')
        relative=str(path.relative_to(ROOT));committed=subprocess.check_output(['git','-C',str(ROOT),'show','a1b7b948:'+relative])
        digest=hashlib.sha256(committed).hexdigest()
        if COST.sha256(path)!=digest:raise ValueError('old evidence changed: '+relative)
        result[relative]=digest
    return result


def protect_agda():
    """Before microprofiling, every existing Agda source must match the committed baseline."""
    records=subprocess.check_output(['git','-C',str(ROOT),'ls-tree','-rz','a1b7b948','--','src']).split(b'\0')
    result={}
    for record in records:
        if not record:continue
        header,name=record.split(b'\t',1)
        if not name.endswith(b'.agda'):continue
        path=name.decode();data=(ROOT/path).read_bytes()
        actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if actual!=header.decode().split()[2]:raise ValueError('existing Agda source changed before authorized integration: '+path)
        result[path]=hashlib.sha256(data).hexdigest()
    return result


def classify(measured,stdout,mode,snapshot,iterations):
    """Only exact completed diagnostic output is usable; no source membership verdict exists."""
    if measured['inconclusive_reason'] not in (None,'missing-or-unknown-status-tag'):
        return 'inconclusive',measured['inconclusive_reason'],None
    lines=stdout.splitlines()
    if lines and lines[0]=='invalid-input':
        return ('invalid-input',None,None) if measured['exit_code']==2 else ('inconclusive','exit-mismatch',None)
    if measured['exit_code']!=0 or len(lines)!=8 or lines[0]!='typed-input-ready' or lines[2]!='basis-ready' or lines[4]!='menu-probe-complete':
        return 'inconclusive','menu-diagnostic-output-mismatch',None
    a,b,c=INPUT.fullmatch(lines[1]),BASIS.fullmatch(lines[3]),RESULT.fullmatch(lines[5])
    if not a or not b or not c or lines[6]!='context=whole-input-ranking-only':
        return 'inconclusive','menu-diagnostic-fields-mismatch',None
    if c.group(1)!=mode or c.group(2)!=snapshot or int(c.group(3))!=iterations:
        return 'inconclusive','menu-diagnostic-argument-mismatch',None
    if int(c.group(4))!=(0 if mode=='basis-only' else iterations):
        return 'inconclusive','menu-diagnostic-iteration-mismatch',None
    expected_scope=('nonce-scope=all-nonces-arbitrary-raw' if snapshot=='inactive-reader-claimed' else
                    'nonce-scope=anchor-0-source-witnessed;positive-nonces-arbitrary-raw')
    if lines[7]!=expected_scope:return 'inconclusive','menu-diagnostic-scope-mismatch',None
    summary=dict(input=dict(zip(('client_events','server_events','forcing_sum'),map(int,a.groups()))),
        basis_count=int(b.group(1)),basis_sum=int(b.group(2)),executed_iterations=int(c.group(4)),
        targets=int(c.group(5)),state_sum=int(c.group(6)),position_sum=int(c.group(7)),nonce_scope=lines[7])
    return 'menu-probe-complete',None,summary


def comparable(summary):
    """Counts/sums are operational checks, not a replacement for exact list-equality proofs."""
    return {key:summary[key] for key in ('input','basis_count','basis_sum','executed_iterations','targets','state_sum','position_sum','nonce_scope')}


def selftest():
    """Check immutable input hashes and classifier/resource controls without model processes."""
    inputs=fixtures();old=protect_old();agda=protect_agda();assert len(inputs)==9
    base=dict(status='inconclusive',inconclusive_reason='missing-or-unknown-status-tag',exit_code=0)
    def output(mode='raw-ready',snapshot='initial',n=100):
        return 'typed-input-ready\nclient-events=1;server-events=1;forcing-sum=3\nbasis-ready\nbasis-count=2;basis-sum=7\nmenu-probe-complete\nstage='+mode+';snapshot='+snapshot+';requested-iterations='+str(n)+';executed-iterations='+str(0 if mode=='basis-only' else n)+';targets=0;state-sum=0;position-sum=0\ncontext=whole-input-ranking-only\nnonce-scope=anchor-0-source-witnessed;positive-nonces-arbitrary-raw\n'
    assert classify(base,output(),'raw-ready','initial',100)[0]=='menu-probe-complete'
    assert classify(dict(base,inconclusive_reason='timeout'),output(),'raw-ready','initial',100)[0]=='inconclusive'
    assert classify(dict(base,inconclusive_reason='runtime-resource-failure'),output(),'raw-ready','initial',100)[0]=='inconclusive'
    assert classify(base,output(),'ordered-old','initial',100)[0]=='inconclusive'
    assert classify(base,output(n=2),'raw-ready','initial',100)[0]=='inconclusive'
    assert classify(dict(base,exit_code=2),'invalid-input\nparse error\n','raw-ready','initial',100)[0]=='invalid-input'
    assert len({row['fixture_sha256'] for row in inputs})==9
    return dict(selftest='passed',immutable_input_hashes=9,protected_old_files=len(old),
        protected_agda_sources=len(agda),
        default_iterations=100,snapshots=len(SNAPSHOTS),old_gated_pairs=3,
        planned_positive_mode_slots=9*(1+6*len(SNAPSHOTS)),checker_processes_launched=0)


def main():
    """Run a progressive fixed matrix with at most ninety seconds of serial model execution."""
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary',type=Path);parser.add_argument('--expected-sha256')
    parser.add_argument('--out',type=Path);parser.add_argument('--iterations',type=int,default=100)
    parser.add_argument('--selftest',action='store_true');args=parser.parse_args()
    if args.selftest:
        if args.binary or args.out:parser.error('pure selftest does not launch a model')
        print(json.dumps(selftest(),indent=2));return 0
    if not args.binary or not args.expected_sha256 or not args.out:parser.error('explicit binary/hash/out are required')
    if not 1<=args.iterations<=4096:parser.error('iterations must be in [1,4096]')
    binary,out=args.binary.resolve(),args.out.resolve()
    if not binary.is_file() or not os.access(binary,os.X_OK) or COST.sha256(binary)!=args.expected_sha256:parser.error('binary missing or hash mismatch')
    if out.exists() or out.is_relative_to(ROOT):parser.error('--out must be new and outside repository')
    old=protect_old();agda=protect_agda();pure=selftest();out.mkdir(parents=True);(out/'fixtures').mkdir()
    agda_path=out/'old-agda-sha256.json';agda_path.write_text(json.dumps(agda,indent=2)+'\n')
    sources=[Path(__file__).resolve(),TOOLS.parent/'MenuProbe.agda',TOOLS.parent/'MenuProbeTests.agda',
        TOOLS.parent/'MenuProbeMain.agda',TOOLS.parent/'ReadyGateOrder.agda',TOOLS.parent/'DriverDecide.agda']
    hashes={str(path.relative_to(ROOT)):COST.sha256(path) for path in sources}
    report=dict(schema='lookahead-menu-profile-v1',started_at_utc=datetime.now(timezone.utc).isoformat(),
        binary=str(binary),binary_sha256=args.expected_sha256,source_sha256=hashes,old_evidence_sha256=old,
        old_agda_manifest=dict(path=str(agda_path),sha256=COST.sha256(agda_path),files=len(agda)),
        pure_selftest=pure,protocolVerdict=None,cases=[],paired_comparisons=[],
        limits=dict(seconds_per_case=2,total_seconds=90,heap='512M',sampled_group_rss_kib=3*1024*1024,output_bytes=65536,iterations=args.iterations),
        qualifications=['Whole-process timing includes startup, parsing/forcing and shared basis construction; markers may be buffered.',
            'Actual basis is forced once before iterations; generated Haskell sharing must be checked separately.',
            'Iterations count source-level calls with varied nonce state arguments; zero-target results may not force nonce fields, and physical evaluation count or universal anti-hoisting is not proved.',
            'No exact per-call CPU subtraction is claimed; matched whole-process allocations/times and full replay comparisons determine practical benefit.',
            'Counter/sum fingerprints can collide; exact old/gated list equality is a separate kernel theorem.',
            'Positive nonce snapshots and inactive-reader-claimed are arbitrary diagnostic states, not fresh-run claims.',
            'No protocol membership verdict, universal cost bound, acquisition or deployed conformance is claimed.'])
    started,blocked,done=time.monotonic(),set(),{};unexpected=False
    for data in fixtures():
        fixture=out/'fixtures'/(data['name']+'.txt');fixture.write_text(data['input'])
        plans=[('basis-only','initial',1)]+[(mode,snapshot,args.iterations) for snapshot in SNAPSHOTS for pair in PAIRS for mode in pair]
        for mode,snapshot,iterations in plans:
            name=data['name']+'_'+snapshot+'_'+mode
            row=dict(name=name,input_name=data['name'],count=data['count'],payloads=data['payloads'],
                mode=mode,snapshot=snapshot,iterations=iterations,fixture_sha256=data['fixture_sha256'],protocolVerdict=None)
            series=(data['payloads'],snapshot,mode)
            if unexpected:row.update(status='not-run',inconclusive_reason='unexpected-completed-output')
            elif series in blocked:row.update(status='not-run',inconclusive_reason='earlier-series-inconclusive')
            elif 90-(time.monotonic()-started)<2.25:row.update(status='not-run',inconclusive_reason='total-budget-before-full-case')
            else:
                argv=[str(binary),'--stage',mode,'--snapshot',snapshot,'--iterations',str(iterations),str(fixture),
                    '--next-contract','node-next','--observation','driver-log','--assume-fresh','+RTS','-M512M','-s','-RTS']
                measured=COST.measure(argv,out,name,timeout=2,rss_limit_kib=3*1024*1024,output_limit=65536)
                stdout=Path(measured['logs']['stdout']['path']).read_text();stderr=Path(measured['logs']['stderr']['path']).read_text()
                status,reason,summary=classify(measured,stdout,mode,snapshot,iterations)
                row.update(measured);row.update(status=status,inconclusive_reason=reason,summary=summary,
                    legacy_classifier=dict(status=measured['status'],reason=measured['inconclusive_reason']),rts=PROFILE.rts_allocations(stderr))
                if status=='inconclusive':blocked.add(series)
                elif status!='menu-probe-complete':unexpected=True
                if status=='menu-probe-complete':
                    key=(data['name'],snapshot,mode);done[key]=row
                    for old_mode,new_mode in PAIRS:
                        a,b=done.get((data['name'],snapshot,old_mode)),done.get((data['name'],snapshot,new_mode))
                        if mode==new_mode and a and b:
                            same=comparable(a['summary'])==comparable(b['summary'])
                            report['paired_comparisons'].append(dict(input=data['name'],snapshot=snapshot,old=old_mode,gated=new_mode,equal=same))
                            if not same:unexpected=True
            row['expectation_met']=row['status']=='menu-probe-complete';report['cases'].append(row)
            if row['status']!='not-run':
                (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
            print(name,row['status'],row.get('seconds'),flush=True)
    report['seconds']=round(time.monotonic()-started,6);report['counts']=dict(Counter(row['status'] for row in report['cases']))
    report['all_expected']=all(row['expectation_met'] for row in report['cases'])
    report['all_completed_pairs_equal']=all(row['equal'] for row in report['paired_comparisons'])
    report['unexpected_completed_output']=unexpected
    report['sources_unchanged']=all(COST.sha256(ROOT/path)==digest for path,digest in hashes.items())
    report['old_evidence_unchanged']=all(COST.sha256(ROOT/path)==digest for path,digest in old.items())
    report['old_agda_unchanged']=all(COST.sha256(ROOT/path)==digest for path,digest in agda.items())
    report['binary_unchanged']=COST.sha256(binary)==args.expected_sha256
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(report=str(out/'report.json'),counts=report['counts'],paired=len(report['paired_comparisons']),all_pairs_equal=report['all_completed_pairs_equal']),indent=2))
    return 0 if report['all_expected'] and report['all_completed_pairs_equal'] and report['sources_unchanged'] and report['old_evidence_unchanged'] and report['old_agda_unchanged'] and report['binary_unchanged'] else 1


if __name__=='__main__':raise SystemExit(main())
