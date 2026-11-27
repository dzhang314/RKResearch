#!/usr/bin/env python3
"""Exact necessary-gate census; see README for the scoped rooted reduction."""

from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, permutations
from math import gcd, isqrt, prod
from pathlib import Path
import argparse
import json

from sympy import Poly, Symbol, primerange

T = Symbol("t")


def add(a, b):
    return [x+y for x,y in zip(a,b,strict=True)]


def neg(a):
    return [-x for x in a]


def sub(a, b):
    return add(a,neg(b))


def mul(a, b):
    c=[0]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b):
            c[i+j]+=v*w
    return c


def scale(a, b):
    return [b*t for t in a]


def dot(a, b):
    return sum(x*y for x,y in zip(a,b,strict=True))


def ev(f, x):
    v=0
    for a in reversed(f):
        v=v*x+a
    return v


def jint(f, x):
    return sum(Q(a,i)*x**i for i,a in enumerate(f,1))


def hull(xs):
    r=[1]
    for x in xs:
        r=mul(r,[-x,1])
    return r


def lag(xs):
    return [scale(hull(y for y in xs if y!=x),1/prod(x-y for y in xs if y!=x)) for x in xs]


def strip(a):
    a=abs(a)
    if not a:return 0
    for p in (2,3,5,7):
        while a%p==0:a//=p
    return a


def qfactor(f):
    """Factor over Q, independently verify product and every no-rational-root receipt."""
    orig=Poly.from_list(list(reversed(f)),T,domain="QQ")
    assert not orig.is_zero
    _, fit=orig.clear_denoms(convert=True)
    _, prim=fit.primitive()
    if prim.LC()<0:prim=-prim
    a=list(map(int,reversed(prim.all_coeffs())))
    assert gcd(*a)==1 and a[-1]>0
    cont, fs=prim.factor_list()
    assert cont==1
    product=[1]
    rs=set()
    receipts=[]
    for r,pow_ in fs:
        b=list(map(int,reversed(r.all_coeffs())))
        for _ in range(pow_):product=mul(product,b)
        assert gcd(*b)==1 and b[-1]>0
        d=len(b)-1
        if d==1:
            rr=Q(-b[0],b[1])
            assert ev(b,rr)==0
            rs.add(rr)
            cert=("linear",rr)
        elif d==2:
            disc=b[1]**2-4*b[2]*b[0]
            lower=isqrt(disc) if disc>=0 else 0
            assert disc<0 or lower**2<disc<(lower+1)**2
            cert=("negative",disc) if disc<0 else ("nonsquare",disc,lower)
        else:
            assert d==3
            p=next(int(p) for p in primerange(2,20000)
                   if b[-1]%p and all(ev(b,x)%p for x in range(p)))
            assert all(p%d for d in range(2,1+isqrt(p)))
            assert b[-1]%p and all(ev(b,x)%p for x in range(p))
            cert=("prime-no-root",p)
        receipts.append([b,pow_,cert])
    assert a==product
    assert all(ev(f,r)==0 for r in rs)
    return rs,a,receipts


grid=[Q(j,6) for j in range(-3,7)]
weights=dict(zip(grid,[jint(l,Q(1)) for l in lag(grid)],strict=True))
assert all(weights.values()) and all(strip(w.denominator)==1 for w in weights.values())
assert all(sum(weights[x]*x**j for x in grid)==Q(1,j+1) for j in range(10))
x=list(map(Q,"1 -1/2 -1/3 -1/6 1/6 1/3 1/2 2/3 5/6".split()))
w=[weights[z] for z in x]
y=[1-z for z in x]
u1=w[1]*y[1]**3/6
cof={z:1/(z*prod(z-t for t in x[1:] if z!=t)) for z in x[1:]}
U=[[0,0]]+[[cof[z]*u1/cof[x[1]]*v for v in (1,z-x[1])] for z in x[1:]]
deta=[m*prod(z-t for t in x if t!=z) for m,z in zip(w,x,strict=True)]
assert all(not any([(dot([z**j for z in x],column)) for column in zip(*U)]) for j in range(1,7))


def eta_rows(u, p, v):
    """Return determinant, two Cramer numerators, and the nine full eta numerators."""
    f2=hull([u,p])
    h0,h1=lag([u,p])
    f0=add(scale(h0,deta[x.index(u)]),scale(h1,deta[x.index(p)]*v))
    base=[[ev(f,z)/d for z,d in zip(x,deta,strict=True)] for f in (f0,f2,[0]+f2)]
    UY=[scale(t,a) for a,t in zip(y,U,strict=True)]
    def pdot(a, b):
        return [dot(a,row) for row in zip(*b)]
    b0,a0,a1=[pdot(t,U) for t in base]
    b1,a2,a3=[pdot(t,UY) for t in base]
    D=sub(mul(a0,a3),mul(a1,a2))
    C=sub(mul(a1,b1),mul(a3,b0))
    B=sub(mul(a2,b0),mul(a0,b1))
    E=[add(scale(D,t),add(scale(C,s),scale(B,v))) for t,s,v in zip(*base,strict=True)]
    return D,(C,B),E,(a0,a1,a2,a3,b0,b1)


def actual_gate(u, p, r, last2, eta_num):
    """Numerator of the actual mixed gate, allowing all within-port taps."""
    fr=[Q(0),u,p,r]
    F=hull(fr)
    early=x[:3]+[next(z for z in x[3:] if z not in set(fr).union(last2))]
    polys=lag(fr)
    # A := eta - interpolation of the actual three port eta values and zero at origin.
    A=[]
    for z,g in zip(x,eta_num,strict=True):
        for L,v in zip(polys[1:],fr[1:],strict=True):
            g=sub(g,scale(eta_num[x.index(v)],ev(L,z)))
        A.append(g)
    a,b=last2
    va,vb=ev(F,a),ev(F,b)
    V=[]
    for z,g in zip(x,A,strict=True):
        L=(z-b)/(a-b)/va
        M=(z-a)/(b-a)/vb
        V.append(sub(g,scale(add(scale(A[x.index(a)],L),scale(A[x.index(b)],M)),ev(F,z))))
    assert all(not any(V[x.index(z)]) for z in (u,p,r,a,b))
    # E G interpolates U/w at the first four nonports; J*G(X) is its reverse primitive.
    S=[0]*4
    l=lag(early)
    for z in early:
        J=[0,0]
        for t,L in zip(early,l,strict=True):
            i=x.index(t)
            J=add(J,scale(U[i],(jint(L,Q(1))-jint(L,z))/w[i]))
        i=x.index(z)
        S=add(S,scale(mul(J,V[i]),w[i]))
    return S


def census():
    records=[]
    ct,dt,ft=Counter(),Counter(),Counter()
    roots=set()
    for u,p in permutations(x[3:],2):
        F3=hull([Q(0),u,p])
        pivot=jint(F3,u)
        target=jint(F3,p)
        if not pivot:
            assert target
            dt["zero chronological pivot"]+=1
            records.append(dict(u=u,p=p,pivot_zero=True,nonzero_target=target))
            continue
        v=target/pivot
        D,CB,E,full=eta_rows(u,p,v)
        d_roots,d_primitive,d_fact=qfactor(D)
        singular=[]
        for k in sorted(d_roots):
            C,B=[ev(f,k) for f in CB]
            datum=[ev(f,k) for f in full]
            assert C or B or (not any(datum[:4]) and any(datum[4:]))
            dt["inconsistent singular direction"]+=1
            singular.append([k,C,B,datum])
        records.append(dict(u=u,p=p,singular_primitive=d_primitive,singular_factors=d_fact,singular_inconsistent=singular))
        for r in x[3:]:
            if r in (u,p):continue
            for last2 in combinations([z for z in x[3:] if z not in (u,p,r)],2):
                f=actual_gate(u,p,r,last2,E)
                rs,f_primitive,f_fact=qfactor(f)
                for _,_,cert in f_fact:ft[cert[0]]+=1
                ct["regular charts"]+=1
                if not rs:ct["no rational root"]+=1
                admitted=[]
                for k in sorted(rs-d_roots):
                    roots.add(k)
                    d=ev(D,k)
                    e=[ev(a,k)/d for a in E]
                    assert dot(e,[ev(zz,k) for zz in U])==dot(e,[b*ev(zz,k) for b,zz in zip(y,U,strict=True)])==0
                    assert all(dot(e,[b*a**n for b,a in zip(w,x,strict=True)])==0 for n in range(5))
                    assert e[x.index(u)]==1 and e[x.index(p)]==v
                    bad=next((z/Q(1)*(2*u/3) for z in e if strip((z*(2*u/3)).denominator)!=1),None)
                    assert bad is not None
                    admitted.append([k,bad,strip(bad.denominator)])
                    ct["unpaid regular roots"]+=1
                records.append(dict(u=u,p=p,r=r,last2=last2,primitive=f_primitive,factors=f_fact,
                                    unpaid=admitted,singular_roots=sorted(rs.intersection(d_roots))))
    assert ct=={"regular charts":336,"no rational root":282,"unpaid regular roots":54},ct
    assert dt=={"inconsistent singular direction":22,"zero chronological pivot":2},dt
    assert roots=={Q(2,3)}
    print("360 chronology classes (including 24 with a zero chronological pivot).")
    print("Regular chart counts:",dict(ct))
    print("Singular-direction checks:",dict(dt))
    print("The only admitted rational k is 2/3; all 54 literal midpoint taps are unpaid.")
    print("Gate factor certificates:",dict(ft))
    return records


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--emit",type=Path)
    ns=p.parse_args()
    rec=census()
    if ns.emit:
        ns.emit.write_text("\n".join(json.dumps(r,separators=(",",":"),default=str) for r in rec)+"\n")
