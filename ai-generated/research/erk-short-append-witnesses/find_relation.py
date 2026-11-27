#!/usr/bin/env python3
"""Exact old-zero relation test for one-/two-stage order raising."""
from fractions import Fraction as F
from functools import lru_cache
from math import prod, lcm, gcd
from pathlib import Path
import argparse,json

@lru_cache(None)
def forest(n,lo=(0,())):
    if n==0:return ((),)
    return tuple((u,)+v for k in range(max(1,lo[0]),n+1)
                 for u in forest(k-1)if (k,u)>=lo for v in forest(n-k,(k,u)))
@lru_cache(None)
def size(t):return 1+sum(map(size,t))
@lru_cache(None)
def fac(t):return size(t)*prod(map(fac,t))
def dot(a,b):return sum(c*d for c,d in zip(a,b)if c and d)

def check(path,target):
    j=json.loads(path.read_text())
    A=[list(map(F,r))for r in j['A']]
    D=lcm(*(v.denominator for row in A for v in row))
    M=[list(map(lambda q:int(q*D),r))for r in A]
    n=len(A)
    @lru_cache(None)
    def p(t):return tuple(prod(y[i]for y in map(act,t))for i in range(n))
    @lru_cache(None)
    def act(t):
        return tuple(size(t)*dot(r,p(t))for r in M)
    T=[]
    failures=[]
    for m in range(1,target):
        T+=list(forest(m-1))
        d=target-m
        basis={};failed=None
        for j,t in enumerate(T):
            u=list(map(F,p(t))); dst=F(D**(size(t)-1),size(t)+d); coeff={j:F(1)}
            for i in sorted(basis):
                if not u[i]:continue
                v,m0,c=basis[i];pivot=u[i]
                u=[a-pivot*b for a,b in zip(u,v)]
                dst-=pivot*m0
                for jj,r in c.items():coeff[jj]=coeff.get(jj,0)-pivot*r
            i=next((i for i,w in enumerate(u)if w),None)
            if i is not None:
                c=u[i];basis[i]=([v/c for v in u],dst/c,{j:x/c for j,x in coeff.items()if x})
            elif dst:
                O=[(T[k], c*D**(size(T[k])-1))for k,c in sorted(coeff.items())if c]
                den=lcm(*(c.denominator for _,c in O))
                O=[(v,int(c*den))for v,c in O]
                scale=gcd(*(abs(c) for _,c in O))
                O=[(v,c//scale)for v,c in O]
                Ω=sum(F(c,size(t)+d)for t,c in O)
                assert Ω==dst*den/scale
                assert all(sum(F(c*p(t)[j],D**(size(t)-1))for t,c in O)==0 for j in range(n))
                failed={'old_row_count':n,'target':target,'grade_size_cap':m,'required_new':d+1,
                        'future_moment':str(Ω),'terms':[{'tree':t,'coefficient':c}for t,c in O]}
                break
        print(path.parent.name,"target",target,"m",m,"rank reached",len(basis),"fail?",bool(failed),flush=True)
        if failed: return failed
    return {'old_row_count':n,'target':target,'no_gate_failure':True}

if __name__=="__main__":
    pa=argparse.ArgumentParser();pa.add_argument('path',type=Path);pa.add_argument('target',type=int);pa.add_argument('--emit',type=Path)
    a=pa.parse_args()
    Z=check(a.path,a.target)
    out=json.dumps(Z,indent=2)+"\n"
    if a.emit:a.emit.write_text(out)
    print('Exact first bound:',Z.get('required_new'),'new rows')
