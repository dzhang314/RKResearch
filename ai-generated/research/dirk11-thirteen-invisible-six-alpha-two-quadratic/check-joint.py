#!/usr/bin/env python3
"""Verify exact clock gcd and the content ledger in each chart."""
from pathlib import Path
from argparse import ArgumentParser
from functools import reduce
from flint import fmpq,fmpq_poly,fmpz_poly
pa=ArgumentParser()
pa.add_argument('branch',choices=('regular','F1','F2','Fn'))
pa.add_argument('normdir',type=Path)
pa.add_argument('--out',type=Path,required=True)
ns=pa.parse_args()
def read(seq):return fmpq_poly([fmpq(x)for x in seq]).numer()
def rd(p):return read(p.read_text().split())
x=fmpz_poly([0,1])
j4=42*x**4-84*x**3+56*x*x-14*x+1
ep=66*x**4-144*x**3+108*x*x-32*x+3
input=ns.normdir
files=['reverse','forward','quintic']
if ns.branch!='regular':files+=['singular-pivot']
G=reduce(lambda a,b:a.gcd(b),(rd(input/(s+'.txt'))for s in files))
claims={
 'regular': (324,[(4,24),(12,2),(12,12),(60,1)],[(516,'reverse'),(456,'forward'),(2328,'quintic')]),
 'F1': (196,[(4,16),(4,24),(36,1)],[]),
 'F2': (196,[(4,16),(4,24),(36,1)],[]),
 'Fn': (504,[(4,18),(4,42),(12,18),(48,1)],[]),
}
n,degree,norms=claims[ns.branch]
assert all(rd(input/(f+'.txt')).degree()==d for d,f in norms)
factors=G.factor()[1]
assert G.degree()==n and sorted((f.degree(),e) for f,e in factors)==degree
assert all(f in (j4,ep) for f,e in factors if f.degree()==4)
assert any(f==j4 for f,e in factors)
assert sum(f==ep for f,e in factors)==int(ns.branch!='regular')
for line in (input/'ledger.txt').read_text().splitlines():
    w=line.split()
    i=next(i for i,x in enumerate(w)if x[0].isdigit()or x[0]=='-')
    a=read(w[i:])
    assert all(f==j4 for f,k in a.factor()[1]),(line[:120],a.degree())
ns.out.write_text(' '.join(map(str,G.coeffs()))+'\n')
print('exact gcd and all stripped contents checked',ns.branch,n,degree)
