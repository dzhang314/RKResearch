#!/usr/bin/env python3
"""Exact-lift residue image ranks at the four direct-profile factors."""
import argparse,sys,hashlib
from pathlib import Path
ap=argparse.ArgumentParser()
ap.add_argument('--research',type=Path,required=True)
ap.add_argument('--factor',type=Path,required=True)
opt=ap.parse_args()
name=opt.factor.stem
assert name in ('ratio','c2','old','full')
source=opt.research/'dirk11-thirteen-invisible-six-alpha-one-live-fn-zero-fifth'/'rank.py'
raw=source.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='38833210adcaa029a461a08f8fa9531bb016e6b2102fd3c0caf25f146161f2af'
anchor='# Polynomials in the carrier t.'
assert raw.decode().count(anchor)==1
sys.argv=[str(source),name,str(opt.factor)]
exec(compile(raw.decode().split(anchor)[0],str(source),'exec'))
rows=Path(__file__).with_name('two-rows.py')
exec(compile(rows.read_text(),str(rows),'exec'))
d=baseMod.degree()
Q=five()
gt={'ratio':(t1,11,12,12,11),'c2':(c2,9,4,12,9),'old':(den,11,1,60,11),'full':(one,12,1,252,11)}
guard,cap,dd,dt,ar=gt[name]
assert p==103 and F0.degree()==dt and d==dd
def vect(e):
    if isinstance(e,PE):
        c=list(map(int,e.f.coeffs()));return c+[0]*(d-len(c))
    return sum((vect(x)for x in e.cs),[])
def basis(r):
    if r is base:return [base.gen()**i for i in range(d)]
    return [r.to(x)*r.gen()**i for i in range(r.n)for x in basis(r.low)]
bb=basis(S)
assert len(bb)==12*d
def rank(es):
    C=[vect(e*x)for e in es for x in bb]
    return nmod_mat(list(map(list,zip(*C))),p).rank()
got=(rank([guard]),rank([guard*A]),rank([guard*A,guard*Q]))
assert got==(cap*d,ar*d,cap*d)
print(name,'residue',baseMod,'guard/marked/joint ranks',got,flush=True)
