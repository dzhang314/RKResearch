#!/usr/bin/env python3
"""Exact length-five first gate after paying projected length four."""
from fractions import Fraction as F
from itertools import permutations
from math import prod
import json
from pathlib import Path

def mult(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
def poly(z):
    q=[F(1)]
    for x in z:q=mult(q,[-x,F(1)])
    return q
def integrate(q):
    return sum(x/(i+1)for i,x in enumerate(q))
def weights(nodes):
    return {z:integrate(poly(t for t in nodes if t!=z))/prod(z-t for t in nodes if t!=z)
            for z in nodes}
def check(X,w,A,C,D,E,F0,G0):
    sites=[A,C,D,E,F0,G0]
    a,t,d=1-A,1-C,1-D
    assert t==3*a/2
    pv={s:w[s]*s*prod(s-x for x in sites if x!=s) for s in sites}
    fixed=lambda y:(a+t)*y**3/3-a*t*y**2/2-y**4/4
    ks=[fixed(y)for y in [a,t,d]]
    z=[pv[s]*k for s,k in zip([A,C,D],ks)]
    co=[1/prod(x-y for y in [A,C,D]if y!=x)for x in [A,C,D]]
    den=sum(m*n for m,n in zip(co,z))
    if not den:return
    r=sum(m*n*x for m,n,x in zip(co,z,[A,C,D]))/den
    if not r or r in sites:return
    L=(z[1]*(C-r)-z[0]*(A-r))/(C-A)
    P=z[0]*(A-r)-A*L
    K={s:(P+L*s)/(pv[s]*(s-r)) for s in sites}
    assert all(K[s]==k for s,k in zip([A,C,D],ks))
    assert all(sum(w[s]*K[s]*s**i*(s-r)for s in sites)==0 for i in range(1,5))
    q4=lambda y:(a*a+a*t+t*t)*y**3/3-a*t*(a+t)*y*y/2-y**5/5
    lr=1-E
    r4=(a+t+d)*(lr**4/4+K[E])-(a*t+a*d+t*d)*lr**3/3+a*t*d*lr*lr/2-lr**5/5
    kap=[q4(y)for y in [a,t,d]]+[r4]
    def P1(x):return x*(x-r)*(x-F0)*(x-G0)
    pressure=sum(w[s]*k*P1(s)for s,k in zip([A,C,D,E],kap))
    return r,K,pressure
def main():
    meshes=[
       [F(1,5),F(5,13),F(7,9)],[F(1,5),F(13,19),F(5,3)],[F(1,5),F(25,33),F(7,41)],
       [F(1,11),F(13,37),F(7,9)],[F(5,17),F(7,9),F(11,5)],[F(1,3),F(11,13),F(7)],
    ]
    all_probes=[]
    for radii in meshes:
        X=sorted([F(0),F(1)]+[(1+sign*t)/2 for sign in (-1,1)for t in radii])
        w=weights(X)
        assert all(sum(w[s]*s**i for s in X)==F(1,i+1)for i in range(10))
        assert all(w[s]for s in X)
        S=[x for x in X if x not in (0,1)]
        accepted=0
        for A in S:
            C=1-3*(1-A)/2
            if C==A or C not in S:continue
            candidates=[x for x in S if x not in (A,C)]
            for D,E in permutations(candidates,2):
                F0,G0=sorted(s for s in candidates if s not in (D,E))
                data=check(X,w,A,C,D,E,F0,G0)
                if data is None:continue
                r,K,pressure=data
                if pressure==0:accepted+=1
                all_probes.append(dict(pole=str(r),nodes=list(map(str,X)),clock_order=list(map(str,[A,C,D,E,F0,G0])),
                    pressure=str(pressure)))
        print('mesh radii',list(map(str,radii)), 'passes of first exact K4 gate',accepted,flush=True)
    print('total exact tested meshes/orders',len(all_probes))
    Path(__file__).with_name('pressure-results.json').write_text(json.dumps(all_probes,indent=2)+'\n')
if __name__=="__main__":main()
