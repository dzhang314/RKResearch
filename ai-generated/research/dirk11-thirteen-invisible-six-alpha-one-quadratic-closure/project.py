#!/usr/bin/env python3
"""Exact rank-12 projection of the quadratic-carrier marked fourth-row gate."""
from pathlib import Path
import sys,hashlib,argparse
ap=argparse.ArgumentParser()
ap.add_argument('--research',type=Path,required=True)
ap.add_argument('--out',type=Path,required=True)
opt=ap.parse_args()
source=opt.research/'dirk11-thirteen-invisible-six-alpha-one-live-fn-zero-fifth'/'project.py'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='f5e0757bac00864eba6975292acdb29d316bd1c54fb81c3b365640554d33a689'
src=source.read_text()
anchor='# Polynomials in the carrier t.'
assert src.count(anchor)==1
sys.argv=[str(source),'--output',str(opt.out)]
exec(compile(src.split(anchor)[0],str(source),'exec'))
rows=Path(__file__).with_name('two-rows.py')
exec(compile(rows.read_text(),str(rows),'exec'))
def project(name,x):
    assert x!=0
    x,=lose(name,x)
    while isinstance(x,E):
        x=norm(x)
        if isinstance(x,E):x,=lose(name+' inner norm',x)
    return x.f/x.f.leading_coefficient()
f=project('A',A)
sf=f//f.gcd(f.derivative())
assert f.degree()==1568 and sf.degree()==352
log('marked reverse A at t=0, norm/squarefree degree',f.degree(),sf.degree())
J4_q=fmpq_poly([1,-14,56,-84,42])
J5_q=fmpq_poly([-1,20,-120,300,-330,132])
X=fmpq_poly([0,1])
Eplus=fmpq_poly([3,-32,108,-144,66])
Eminus=fmpq_poly([1,-16,72,-120,66])
Er=fmpq_poly([3,-64,604,-3096,9360,-17136,18648,-11088,2772])
assert 2*X*Eplus==J5_q+J4_q and 2*(X-1)*Eminus==J5_q-J4_q
assert 2*Er==J5_q.derivative()*J4_q-J5_q*J4_q.derivative()
def monic(q):return q/q.leading_coefficient()
forbidden={str(monic(x)) for x in (J4_q,Eplus,Er)}
gone=set()
guards={
    (12,16227):('ratio',t1,11),
    (12,54123):('c2',c2,9),
    (60,-1461941766456):('old',den,11),
    (252,-351383915829049374509981333545308408021254041562048657856):('full',one,12),
}
seen=set()
for u,e in sf.numer().factor()[1]:
    assert e==1
    uq=fmpq_poly(u)
    s=str(monic(uq))
    if s in forbidden:
        assert s not in gone
        gone.add(s)
        print('forbidden Jacobi factor degree', u.degree(), flush=True)
        continue
    key=u.degree(),int(u[0])
    name,g,cap=guards[key]
    assert name not in seen
    seen.add(name)
    if name=='c2':
        low=g.cs[0]
        assert all(c==0 for c in g.cs[1:]) and low.cs[1]==1 and all(c==0 for c in low.cs[2:])
        w=norm(low)
        assert w.f!=0 and w.f%uq==0
    if name in ('ratio','old'):
        w=g
        while isinstance(w,E):w=norm(w)
        assert w.f!=0 and w.f%uq==0
    print('exact ordinary factor',name,*key,'cap',cap,flush=True)
    (opt.out/(name+'.txt')).write_text(' '.join(map(str,u.coeffs()))+'\n')
assert gone==forbidden and seen=={d[0] for d in guards.values()}
