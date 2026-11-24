#!/usr/bin/env python3
"""Build exactly one locked release pair in a NEW directory; never edit the input checkout."""
import argparse, hashlib, json, os, re, shutil, subprocess, sys
from pathlib import Path
H=Path(__file__).resolve().parent
def sh(x):return hashlib.sha256(x).hexdigest()
def manifest(m):return dict((n,h) for h,n in (line.split('  ',1) for line in m.read_text().splitlines()))
def sources(path):
 names={}
 for top,ds,fs in os.walk(path):
  ds[:]=[d for d in ds if d not in ('.lake','.git')]
  for n in fs:
   if n.endswith('.lean'):
    p=Path(top)/n
    if p.is_symlink():raise SystemExit(f'source symlink rejected: {p}')
    names[p.relative_to(path).as_posix()]=sh(p.read_bytes())
 return names
def verify(ok,msg):
 if not ok:raise SystemExit(msg)
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--project',type=Path,required=True,help='source root containing RKCert.lean; read-only')
parser.add_argument('--version',required=True,choices=list(json.loads((H/'versions.json').read_text())))
parser.add_argument('--output',type=Path,required=True,help='new external work directory, must not exist')
parser.add_argument('--lean-bin',type=Path,help='optional directory containing the exact Lean release binaries; otherwise use current PATH')
parser.add_argument('--prepare-only',action='store_true',help='verify and copy source and locks; perform no downloads or builds')
parser.add_argument('--kernel',choices=['none','focus','all'],default='focus',help='per-module kernel replay; focus checks eight principal endpoints')
a=parser.parse_args(); source=a.project.resolve(); w=a.output.resolve();v=a.version
verify(not w.exists() and source!=w and source not in w.parents and w not in source.parents,'output must be new and disjoint from project')
release=json.loads((H/'versions.json').read_text())[v];lockdir=H/'locks'/v
old=manifest(H/'published.sources.sha256');new=manifest(H/'candidate.sources.sha256');current=sources(source)
verify(current==old or current==new,'entire input source set and hashes must match either the published or candidate fingerprint')
verify((lockdir/'lake-manifest.json').exists(),'exact lockfile for requested pair is not available')
w.mkdir(parents=True)
for n in current:
 dest=w/n;dest.parent.mkdir(exist_ok=True,parents=True);shutil.copyfile(source/n,dest)
if current!=new:
 subprocess.run(['git','apply','--no-index','--whitespace=nowarn',str(H/'portability.patch')],cwd=w,check=True)
verify(sources(w)==new,'candidate source fingerprint mismatch after staging')
for n in ['lake-manifest.json','lean-toolchain','lakefile.toml']:shutil.copyfile(lockdir/n,w/n)
def locks_ok():
 for n in ['lake-manifest.json','lean-toolchain','lakefile.toml']: verify((lockdir/n).read_bytes()==(w/n).read_bytes(),'pin changed: '+n)
lk=json.loads((w/'lake-manifest.json').read_text());pkgs=lk['packages'];math=[p for p in pkgs if p['name']=='mathlib']
verify(len(math)==1 and math[0]['inputRev']==v and math[0]['rev']==release[1],'wrong Mathlib tag or commit')
verify((w/'lean-toolchain').read_text().strip()=='leanprover/lean4:'+v,'wrong declared Lean toolchain')
if a.prepare_only:print('exact source and pin preparation passed');sys.exit(0)
env={k:val for k,val in os.environ.items() if not k.startswith(('LEAN','LAKE','ELAN','MATHLIB_CACHE','GIT_CONFIG'))}
if a.lean_bin:env['PATH']=str(a.lean_bin.resolve())+os.pathsep+env['PATH']
env.update(ELAN_TOOLCHAIN='leanprover/lean4:'+v,MATHLIB_CACHE_DIR=str(w/'.release-cache'),MATHLIB_CACHE_FROM='master',MATHLIB_NO_CACHE_ON_UPDATE='1',GIT_TERMINAL_PROMPT='0',GIT_ASKPASS='/bin/false')
home=w/'.curl-configuration';home.mkdir();(home/'.curlrc').write_text('parallel-max = 8\nconnect-timeout = 100\nmax-time = 280\nmax-filesize = 33554432\n');env['CURL_HOME']=str(home)
e=w/'release-evidence';e.mkdir()
def cmd(args,wd=w,capture=False):return subprocess.check_output(args,cwd=wd,env=env,text=True) if capture else subprocess.run(args,cwd=wd,env=env,check=True)
def log(name,args):
 with (e/name).open('w') as out:
  cp=subprocess.run(args,cwd=w,env=env,stdout=out,stderr=subprocess.STDOUT)
 verify(cp.returncode==0,f'{name} failed: see {e/name}')
 return (e/name).read_text()
actual=log('toolchain.txt',['lean','--version'])
verify('version '+v[1:]+',' in actual and 'commit '+release[0] in actual,'active Lean is not the locked binary commit')
deps=w/'.lake/packages';deps.mkdir(parents=True)
allowed={'mathlib','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','Cli'}
verify({p['name'] for p in pkgs}==allowed,'unexpected or missing dependency')
for p in pkgs:
 u=p['url'];h=p['rev'];path=deps/p['name']
 verify(re.fullmatch(r'https://github\.com/(?:leanprover|leanprover-community)/[-a-zA-Z0-9_]+(?:\.git)?',u) and re.fullmatch('[a-f0-9]{40}',h),'nonofficial URL or nonexact revision')
 path.mkdir();cmd(['git','init','-q'],path);cmd(['git','remote','add','origin',u],path)
 cmd(['git','-c','credential.helper=','fetch','--depth','1','--no-recurse-submodules','origin',h],path);cmd(['git','checkout','--quiet','--detach',h],path)
def check_deps():
 for p in pkgs:
  path=deps/p['name'];verify(cmd(['git','rev-parse','HEAD'],path,True).strip()==p['rev'] and not cmd(['git','status','--porcelain','--untracked-files=normal'],path,True).strip(),'dependency changed: '+p['name'])
 check_math=(deps/'mathlib'/'lean-toolchain').read_text().strip()
 verify(check_math=='leanprover/lean4:'+v,'mathlib declares another toolchain')
 actual={(d['name'],d['url'],d['rev']) for d in json.loads((deps/'mathlib'/'lake-manifest.json').read_text())['packages']}
 verify(actual=={(d['name'],d['url'],d['rev']) for d in pkgs if d['name']!='mathlib'},'inherited lock differs from upstream Mathlib')
check_deps()
ims=sorted({x for p in new for x in re.findall(r'(?m)^(?:public )?import (Mathlib(?:\.[A-Za-z0-9_]+)+)\s*$',(w/p).read_text())})
mods=sorted(p[:-5].replace('/','.') for p in new if p.startswith('RKCert/'))
log('cache.log',['lake','exe','cache','get','--cache-from=master',*ims]);log('build.log',['lake','--no-cache','build','RKCert',*mods])
for m in mods:verify((w/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')).is_file(),'missing build product: '+m)
expected=json.loads((H/'audited-declarations.json').read_text());count=0
for name,table in expected.items():
 out=log(name+'.log',['lake','env','lean',name+'.lean']);rows=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]+)\])",out)
 verify([n for n,ax in rows]==table and len(re.findall(r'(?m)^#print axioms ',(w/(name+'.lean')).read_text()))==len(table),'missing/unexpected axiom query results: '+name)
 for n,ax in rows:verify({z.strip() for z in ax.split(',') if z.strip()}<={'propext','Classical.choice','Quot.sound'},'unexpected reported axiom: '+n)
 count+=len(rows)
focus=['RKCert.ERKLogarithmic','RKCert.OrderTwelveGhost','RKCert.SDIRKOrderSixRing','RKCert.DirkGradeSixRegression','RKCert.ExplicitOrderTwelve','RKCert.OrderTwelveReverseObstruction','RKCert.DirkParityFloor','RKCert.ERKLowFourOff']
replays=mods if a.kernel=='all' else focus if a.kernel=='focus' else []
for m in replays:verify('replaying '+m in log('replay-'+m+'.log',['lake','env','leanchecker','--verbose',m]).splitlines(),'missing kernel replay: '+m)
locks_ok();check_deps();verify(sources(w)==new,'source changed during build')
(e/'result.json').write_text(json.dumps({'release':v,'sourceManifestSHA256':sh((H/'candidate.sources.sha256').read_bytes()),'lockSHA256':sh((w/'lake-manifest.json').read_bytes()),'modules':len(mods),'auditQueries':count,'replayed':replays},indent=2)+'\n')
print(f'{v}: {len(mods)} modules, {count} axiom queries, {len(replays)} selected module kernel replays')
