from pathlib import Path
from flint import fmpq_poly,fmpq,fmpz_poly
from math import lcm
from itertools import chain
import argparse
q=argparse.ArgumentParser()
q.add_argument('candidate',type=Path)
q.add_argument('--guards',type=Path,default=Path('frexact'))
q.add_argument('--output',type=Path,required=True)
q.add_argument('--ledger',type=Path)
q.add_argument('--inherit',type=Path,nargs='*',default=())
ns=q.parse_args()
def read(seq):return fmpq_poly([fmpq(x)for x in seq])
def prim(f):
    if isinstance(f,fmpq_poly):f=f.numer()
    return f//f.content() if f else f
def sat(f,g):
    d=fmpz_poly([1])
    while (j:=f.gcd(g)).degree()>0:
        f,r=divmod(f,j)
        assert r==0
        d*=j
    return prim(f),prim(d)
def rad(f):
    a=f.gcd(f.derivative())
    b,r=divmod(f,a); assert r==0
    return prim(b)
F=prim(read(ns.candidate.read_text().split()))
print('complete first projection degree',F.degree(),'height',F.height_bits(),flush=True)
F=rad(F)
print('squarefree projection degree',F.degree(),'height',F.height_bits(),flush=True)
guard_parts=[(z.stem,prim(read(z.read_text().split()))) for z in sorted(ns.guards.glob('G*'))]
for log in ([ns.ledger]if ns.ledger else [])+list(ns.inherit):
    for ln in log.read_text().splitlines():
        sp=ln.split()
        i=next(i for i,x in enumerate(sp)if x[0].isdigit()or x[0]=='-')
        guard_parts.append(('ledger:'+' '.join(sp[:i]),prim(read(sp[i:]))))
G=fmpz_poly([1])
for tag,H in guard_parts:
    if H==0:
        print('skipping identically zero guard',tag,flush=True);continue
    F,d=sat(F,H)
    if d.degree():
        G*=d
        print('leftover',F.degree(),'guard slot',tag,d.degree(),flush=True)
print('residual degree',F.degree(),'height',F.height_bits(),'exceptional projection degree',G.degree(),flush=True)
ns.output.write_text(' '.join(map(str,F.coeffs()))+'\n')
(ns.output.with_suffix('.guards')).write_text(' '.join(map(str,prim(G).coeffs()))+'\n')
for f in [G,F]:
    print('possible leading good primes:',[p for p in [29,37,43,53,67,79,101,103,107] if int(f.leading_coefficient())%p],flush=True)
