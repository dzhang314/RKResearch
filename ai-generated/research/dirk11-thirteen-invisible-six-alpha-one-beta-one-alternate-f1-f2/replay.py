#!/usr/bin/env python3
"""Use matched old models, then build only the true beta-one polynomial rows."""
import argparse,hashlib,sys
from pathlib import Path
a=argparse.ArgumentParser()
a.add_argument('profile',choices=['F1','F2','H3','H5'])
a.add_argument('--research',type=Path,required=True)
a.add_argument('--p',type=int,default=103)
a.add_argument('--residue-index',type=int,default=0)
a=a.parse_args()
base='dirk11-thirteen-invisible-six-alpha-one-beta-zero-alternate-f'
cases={
 'F1':('1','8ad9396ece9684040108275e7dfc224786e6cc0140ee281228c8052e0276fa1c',[]),
 'F2':('2','f9386e78465d38dd12cf4d3c742473159ad05466c4592bc70bfac2bc51957663',[]),
 'H3':('n','eab8a0b05f98e798c7be405b137008f8887004da8fa1284acd294b71526e309e',['H3']),
 'H5':('n','eab8a0b05f98e798c7be405b137008f8887004da8fa1284acd294b71526e309e',['H5']),
}
suffix,digest,case=cases[a.profile]
s=a.research/(base+suffix)/'proof.py'
raw=s.read_bytes();assert hashlib.sha256(raw).hexdigest()==digest
start=raw.decode()
anchor='tt=T.gen()\n';assert start.count(anchor)==1
start=start[:start.index(anchor)]
assert 'hbq' not in start and 'c_q' not in start
rows=Path(__file__).with_name('rows.py').read_text()
sys.argv=[str(s),*case,'--p',str(a.p),'--residue-index',str(a.residue_index)]
exec(compile(start+'\n'+rows,str(s),'exec'),{'__name__':'__main__','__file__':str(s)})
