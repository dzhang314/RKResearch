#!/usr/bin/env python3
"""Instantiate four separate native certificates from each exact prime literal."""
from pathlib import Path
from argparse import ArgumentParser
from hashlib import sha256
import json
HERE=Path(__file__).resolve().parent
SEVENTEEN=HERE.parent/'erk10-sixteen-f17'
DEFECTS={11:10,13:5,19:11,23:15}
def build(p,out,template,modules):
 K=SEVENTEEN/'generate_native.py'
 # The prime-17 cache generator is reused as structure only: never its data.
 src=K.read_text().replace('%17','%PRIME').replace("data['field']==17","data['field']==PRIME")
 code={'__name__':'normalized_portfolio_cache_generator','PRIME':p}
 exec(compile(src,str(K),'exec'),code)
 N='ERK10SixteenF'+str(p)
 code.update(N=N,NS='RKResearch.Certified.'+N,PRIME=p)
 p0=(HERE/('f'+str(p)+'.json'))
 lit=json.loads(p0.read_text())
 assert int(lit['next_failure_value'])==DEFECTS[p]
 mom=(1+DEFECTS[p])%p
 code['main'](p0,out,modules)
 for suff in ('Core',''):
  T=(template/('ERK10SixteenF17'+suff+'.lean')).read_text()
  T=T.replace('ERK10SixteenF17',N)
  T=T.replace('ZMod 17','ZMod '+str(p)).replace('%17','%'+str(p))
  T=T.replace(')=3 := by',f')={mom} := by')
  T=T.replace('exact_f17','exact_f'+str(p)).replace('(3:K)≠1',f'({mom}:K)≠1')
  T=T.replace('characteristic seventeen',f'characteristic {p}')
  (out/(N+suff+'.lean')).write_text(T)
 print(p,'checked next-tree target',mom,'literal',sha256(p0.read_bytes()).hexdigest())
if __name__=='__main__':
 P=ArgumentParser(description=__doc__)
 P.add_argument('--emit',type=Path,required=True)
 P.add_argument('--manifest-dir',type=Path,required=True)
 P.add_argument('--template-dir',type=Path)
 P.add_argument('--primes',type=int,nargs='+',default=[11,13,19,23])
 a=P.parse_args()
 a.manifest_dir.mkdir(parents=True,exist_ok=True)
 for p in a.primes:
  build(p,a.emit,a.template_dir or a.emit,a.manifest_dir/('f'+str(p)+'-modules.txt'))
