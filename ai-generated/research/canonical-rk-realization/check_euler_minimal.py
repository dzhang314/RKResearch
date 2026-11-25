#!/usr/bin/env python3
"""Exact finite read obstruction on minimal Euler-extrapolation tableaux."""
from fractions import Fraction as F
from math import prod, factorial, isqrt


def prime(q):return q>1 and all(q%d for d in range(2,isqrt(q)+1))
def md(x,q):
    v=F(x);return v.numerator*pow(v.denominator,-1,q)%q

def det(g,q):
    a=[list(r) for r in g];z=1
    for j in range(len(a)):
        k=next((i for i in range(j,len(a)) if a[i][j]),None)
        if k is None:return 0
        if k!=j:z=-z;a[k],a[j]=a[j],a[k]
        v=a[j][j];z=z*v%q;u=pow(v,-1,q)
        for i in range(j+1,len(a)):
            f=a[i][j]*u%q
            for k in range(j,len(a)):a[i][k]=(a[i][k]-f*a[j][k])%q
    return z%q


def run():
    p,M,d=20,54,4
    L=1009;assert prime(L)
    qs=[j for j in range(M+1,250) if prime(j)][:p];assert len(qs)==p and qs[0]==59
    ss=[F(1,q) for q in qs];omega=[F((-1)**(M-j)*j**(M-1),factorial(j-1)*factorial(M-j)) for j in range(1,M+1)]
    w=[prod((1-v)/(u-v) for v in ss if v!=u) for u in ss];assert all(w) and all(omega)
    assert [sum(wj*s**i for wj,s in zip(w,ss)) for i in range(p)]==[1]*p
    assert sum(wj*s**p for wj,s in zip(w,ss))==1-prod(1-s for s in ss)!=1
    assert sum(om/m for m,om in enumerate(omega,1))==0
    hs=[s/m for s in ss for m in range(1,M+1)];assert len(set(hs))==p*M
    slots=[((14-t)//2,e) for t in range(0,14,2) for e in range(1+min(t,15-t))]
    assert len(slots)==34
    for impl in (0,1):
        sign=1 if impl else -1
        prof={((h*j),h*h*j*(j+sign)/2) for s in ss for m in range(1,M+1) for h in (s/m,) for j in range(impl,m+impl) if j}
        r=len(prof)+(not impl)
        assert r==p*M*(M+1)//2-(0 if impl else p*M-1)
        roots=[ss[0]*(j+impl)/d for j in range(d)];Q=[[] for _ in slots]
        for m in range(15,34):
            h=md(ss[0]/m,L);x=[h*(j+impl)%L for j in range(m)];mask=[prod(y-md(a,L) for a in roots)%L for y in x]
            def A(v):
                out=[];z=0
                for y in v:out.append(h*(z+impl*y)%L);z+=y
                return out
            def T(v):
                a=A(v);b=A([z*y for z,y in zip(x,v)]);f=A(a)
                return [(z*y-v-u)%L for z,y,v,u in zip(x,a,b,f)]
            for k,(a,e) in enumerate(slots):
                v=[y*pow(z,e,L)%L for y,z in zip(mask,x)]
                for _ in range(a):v=T(v)
                Q[k].extend(v)
        G=[[sum(x*y for x,y in zip(u,v))%L for v in Q] for u in Q];rG=det(G,L);assert rG
        coeff=[F(1)]
        for a in roots:
            new=[F(0)]*(len(coeff)+1)
            for j,b in enumerate(coeff):new[j]-=b*a;new[j+1]+=b
            coeff=new
        mom=[md(sum(a/F(i+j+1) for j,a in enumerate(coeff)),L) for i in range(15)]
        hh=[det([[mom[i+j] for j in range(k)] for i in range(k)],L) for k in range(1,9)];assert all(hh)
        print(f'{"DIRK" if impl else "ERK"}, p=20, finite horizon 54, canonically minimal {r} stages, proper quartic cut. All 34 old columns independent; 456-row two-hole Gram det {rG} mod {L}; eight leading paid Hankels {hh}. Positive-clock stages separated by (c,Ac); '+('all stages have nonzero b and nonzero pivot.' if impl else 'only common origin merged, weight zero but observable.'))

if __name__=='__main__':run()
