#!/usr/bin/env python3
"""Check the exact initial clock projection against the smaller frozen outputs."""
from pathlib import Path
from flint import fmpq,fmpq_poly,fmpz_poly
from sys import argv
assert len(argv)==4, 'usage: check-support.py generated-cofactor generated-guards first-projection-ledger'
here=Path(__file__).resolve().parent
def readz(p):return fmpz_poly([int(x)for x in Path(p).read_text().split()])
C=readz(argv[1]); G=readz(argv[2])
assert C==readz(here/'gamma5-cofactor.txt') and G==readz(here/'gamma5-guard-support.txt')
assert C.degree()==276 and G.degree()==220 and C.gcd(G)==1
assert sorted((x.degree(),m)for x,m in G.factor()[1])==[(d,1)for d in (4,4,16,24,24,28,60,60)]
for line in Path(argv[3]).read_text().splitlines():
    w=line.split()
    i=next(i for i,x in enumerate(w)if x[0].isdigit()or x[0]=='-')
    d=fmpq_poly([fmpq(x)for x in w[i:]]).numer()
    d//=d.content()
    d//=d.gcd(d.derivative())
    div,r=divmod(G,d)
    assert r==0, (line[:100],d.degree())
assert int(C.leading_coefficient())%103!=0
print('Exact gamma-five support and every removed coefficient content checked')
