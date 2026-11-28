#!/usr/bin/env python3
"""Univariate integer multiples verifying the two actual scalar moment gates."""
from fractions import Fraction as Q
from pathlib import Path
from math import lcm
import json,sys,flint as fl

def conv(a,b):
    c=[fl.fmpz_poly() for _ in range(len(a)+len(b)-1)]
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            c[i+j]+=x*y
    return c

def lin(a,b,n=1): return [x+n*y for x,y in zip(a,b)]
def sc(a,k): return [k*x for x in a]
def dp(poly,data):
    qs=[Q(*c) if isinstance(c,list) else Q(c) for c in data]
    d=lcm(*(q.denominator for q in qs))
    return d,poly([int(q*d) for q in qs])
def exact(src):
    X=fl.fmpz_poly([0,1]); one=fl.fmpz_poly([1]); zero=fl.fmpz_poly()
    dy,y=dp(fl.fmpz_poly,src['y']);dt,t=dp(fl.fmpz_poly,src['t'])
    fD=lcm(*(Q(*c).denominator for r in src['f'] for c in r))
    F=[fl.fmpz_poly([int(fD*Q(*c)) for c in r]) for r in src['f']]
    assert F[-1]==fD*one
    U=[one]
    for f in ([zero,one],[-one,one],[-one,2*one],[X-2*one,2*one],
              [y-2*dy*one,2*dy*one],[t-2*dt*one,2*dt*one]):
        U=conv(U,f)
    L=lcm(*range(1,13)); D=16*dy*dt*L
    I=[sum((coef*(L//(j+i+1)) for i,coef in enumerate(U)),zero) for j in range(6)]
    NJ=[(I[j+1]-I[j], I[j]) for j in range(5)]
    a,b,c,d,e=NJ
    u,v,E=conv(a,c),conv(b,b),conv(b,c)
    A=lin(sc(v,9),u,-4);B=lin(sc(v,3),u,-1)
    P=[lin(conv(B,d),conv(E,c),-2),lin(conv(A,e),conv(E,d),-5)]
    Qx=fl.fmpz_poly(src['x'])
    Whole=[]
    for p in P:
        G=[]
        for j in range(3):
            H=fD*p[j]-p[3]*F[j]
            q,r=divmod(fl.fmpq_poly(H),fl.fmpq_poly(Qx))
            assert not r and all(z.denominator==1 for z in q)
            Qj=fl.fmpz_poly(list(map(int,q)))
            assert H==Qx*Qj
            G.append([int(z) for z in Qj])
        Whole.append(G)
    out=dict(Q=src['x'],Y=[int(z) for z in y],T=[int(z) for z in t],dy=dy,dt=dt,
             f=[[int(z) for z in f] for f in F],fd=fD,den=D,moments=[[[int(w) for w in v] for v in r] for r in NJ],
             rel=[[[int(z) for z in q] for q in p] for p in P],divisors=Whole)
    print('degrees of exact six integer quotient certificates',[[len(z)-1 for z in q] for q in Whole])
    print('literal coefficient scalar gate payload bytes',len(json.dumps(out,separators=(',',':'))))
    return out

if __name__=='__main__':
    source=Path(sys.argv[1]);data=exact(json.loads(source.read_text()))
    if len(sys.argv)>2:Path(sys.argv[2]).write_text(json.dumps(data,separators=(',',':'))+'\n')
