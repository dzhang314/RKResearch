#!/usr/bin/env python3
"""Run only in a separately authorized, cold public checkout with pinned dependencies prepared.
Capture true exits for the Data/Tall/Positive/Upper targets and exact typed audits.
This script is not itself a proof or a receipt. No synthetic log is accepted by the CLI.
"""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import time

from check_cut import A, L, MATHLIB, P, R, U, W, args, check, local, need

C = 'RKResearch.Certified.'
T = C + W + 'Upper.'
K = C + 'P10AugmentedRender.'
EXISTS = C + 'exists_twenty_seven_stage_rational_strictSDIRK_exact_ten'
SCHEDULE = [
    (R+W+'Data', A+'Data', [T+x for x in ('actInt_eq','outInt_eq','shared_scale')]),
    (R+W+'Tall', A+'Tall', [T+x for x in ('eleventh_tall_weight','not_order_eleven')]),
    (P+'Positive', A+'AugmentedPositive', [K+'literalReceipts',K+'checked_order_ten']),
    (U, A+'Upper', [T+'order_ten',T+'eleventh_tall_weight',T+'not_order_eleven',EXISTS])]
PERMITTED = {'propext','Classical.choice','Quot.sound'}
REPORT = re.compile(r"(?:(?:[^\n]*?:\d+:\d+: )?(?:info|information):\s*)?"
    r"'([A-Za-z_][A-Za-z_0-9.]*)'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\.?")


def parse_reports(data, expected):
    text = data.decode('utf-8').strip()
    out = []
    for full in expected:
        match = REPORT.match(text)
        need(match is not None, 'missing/unrecognized named axiom report for '+full)
        need(match[1]==full, 'wrong/duplicate/out-of-order named axiom report: '+match[1]+'; expected '+full)
        names = [] if not (match[2] or '').strip() else [n.strip() for n in match[2].split(',')]
        need(len(set(names))==len(names) and set(names)<=PERMITTED, 'unexpected/duplicate axiom in '+full+': '+repr(names))
        out.append({'declaration':full,'axioms':sorted(names)})
        text = text[match.end():].strip()
    need(not text, 'unexpected extra report, warning, error or truncated/unparsed output: '+text[:180])
    return out


def invocation_plan(repo):
    """The exact build/audit argv templates consumed by both planning and real replay."""
    root=repo.resolve(); work=root/L
    for mod,audit,expected in SCHEDULE:
        provider=L+mod.replace('.', '/')+'.lean'; audit_file=audit+'.lean'
        need(local(root,provider).is_file() and local(root,L+audit_file).is_file(),
             'required provider/audit missing at project-relative path for '+audit)
        yield {'module':mod,'provider_path':provider,'cwd':str(work),
               'audit_repo_path':L+audit_file,'audit_name':audit,'axiom_query_names':expected,
               'build_argv':['lake','build','+'+mod],
               'audit_argv':['lake','env','lean','-Dpp.fullNames=true','-Dpp.width=2000',audit_file]}


def runs(a):
    root = a.repo.resolve()
    work = root / L
    rec = a.record_dir.resolve()
    need(not rec.is_relative_to(root), 'put logs in a fresh directory outside the checkout')
    rec.mkdir(exist_ok=False)
    summary = {'status':'STARTED_NOT_ACCEPTED','preparation_base':a.preparation_base,'commands':[]}
    def save(): (rec/'result.json').write_text(json.dumps(summary, sort_keys=True, indent=2)+'\n', encoding='utf8')
    save()
    env = os.environ.copy()
    need(not any(env.get(k) for k in ('LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','ELAN_TOOLCHAIN',
        'LEAN_OPTS','LEAN_ARGS','LAKE_BUILD_DIR','LAKE_PKG_URL_MAP')), 'foreign Lean/Lake environment override')
    env.update(NO_COLOR='1',TERM='dumb')
    def run(label, command, cwd=work):
        target = rec/(label+'.log'); t = time.monotonic()
        with target.open('xb') as f:
            p = subprocess.run(command,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,check=False)
        b=target.read_bytes()
        summary['commands'].append({'label':label,'command':command,'exit':p.returncode,
            'elapsed_seconds':round(time.monotonic()-t,3),'log':target.name,'log_sha256':sha256(b).hexdigest()})
        save(); need(p.returncode==0,'nonzero exit at '+label+'; see '+target.name)
        return b
    def equal_check(): return check(root,a.manifest,a.manifest_sha256,a.existing)
    try:
        summary['source_before'] = equal_check(); save()
        for project in (root,work):
            need(not (project/'.lake/build').exists(), 'project build output already exists; use a different cold checkout')
        for project in (root/'RKResearch',work/'RKCert'):
            need(not any(project.rglob('*.olean*')), 'object shadow in project sources')
        need(re.fullmatch(r'[0-9a-f]{40}',a.preparation_base), 'expected exact reviewed preparation commit')
        head=run('head',['git','rev-parse','HEAD'],root).decode().strip()
        need(re.fullmatch(r'[0-9a-f]{40}',head),'not a single full Git revision')
        summary['observed_head']=head
        run('check-base',['git','merge-base','--is-ancestor',a.preparation_base,'HEAD'],root)
        v=run('lean-version',['lake','env','lean','--version']).decode().strip()
        need(re.search(r'\bLean \(version 4\.36\.0(?:[,)]|\s)',v), 'wrong Lean toolchain')
        run('lake-version',['lake','--version'])
        system=Path(run('toolchain-prefix',['lake','env','lean','--print-prefix']).decode().strip()).resolve()
        path=run('lean-path',['lake','env','printenv','LEAN_PATH']).decode().strip()
        allowed_pkg = {(root/'.lake/build/lib/lean').resolve(),(work/'.lake/build/lib/lean').resolve()}
        locks=json.loads((work/'lake-manifest.json').read_text())['packages']
        revs={pkg['rev'] for pkg in locks if pkg.get('type')=='git' and pkg.get('rev')}
        seen_roots=set(); searched=set()
        for n,raw in enumerate(path.split(os.pathsep)):
            need(bool(raw),'empty LEAN_PATH component')
            rp=(work/raw).resolve(); searched.add(rp)
            if rp in allowed_pkg or rp==(system/'lib/lean').resolve(): continue
            need(rp.parts[-4:]==('.lake','build','lib','lean'), 'unexpected package/foreign object path: '+str(rp))
            package=rp.parents[3]
            rev=run('dependency-head-'+str(n),['git','rev-parse','HEAD'],package).decode().strip()
            need(rev in revs, 'resolved dependency tree is not a pinned Git revision: '+str(rp))
            dirty=run('dependency-clean-'+str(n),['git','status','--porcelain','--untracked-files=normal'],package)
            need(not dirty.strip(), 'resolved dependency checkout has unreviewed changes: '+str(package))
            need(not any((rp/k).exists() for k in ('RKCert','RKCert.olean','RKResearch','RKResearch.olean')), 'foreign project namespace in dependency build')
            seen_roots.add(rev)
        need(allowed_pkg<=searched and MATHLIB in seen_roots,'missing expected package roots or pinned Mathlib provider')
        for inc in invocation_plan(root):
            audit=inc['audit_name']; cw=Path(inc['cwd'])
            run('build-'+audit,inc['build_argv'],cw)
            raw=run('audit-'+audit,inc['audit_argv'],cw)
            summary['commands'][-1]['typed_and_axiom_reports']=parse_reports(raw,inc['axiom_query_names']); save()
        summary['source_after']=equal_check()
        summary['status']='COLD_PROJECT_TARGETS_AND_EXACT_AUDITS_EXIT_ZERO'
        save(); print(summary['status'])
    except BaseException as e:
        summary['status']='STOP_NOT_ACCEPTED'; summary['stop']=str(e); save(); raise


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__); args(parser)
    parser.add_argument('--preparation-base',help='independently selected full Git revision for a real run')
    parser.add_argument('--record-dir',type=Path,help='NEW leaf directory outside checkout for a real run')
    parser.add_argument('--print-plan',action='store_true',help='source verify and show paths/argv only; NO subprocesses')
    a=parser.parse_args()
    if a.print_plan:
        if a.preparation_base or a.record_dir: parser.error('--print-plan is source-only; omit real-run arguments')
        source=check(a.repo,a.manifest,a.manifest_sha256,a.existing)
        print(json.dumps({'status':'SOURCE_ONLY_INVOCATION_PLAN_NO_COMMANDS_RUN','source':source,
                          'planned':list(invocation_plan(a.repo))},indent=2))
    else:
        if not a.preparation_base or not a.record_dir: parser.error('real replay requires both --preparation-base and --record-dir')
        runs(a)
