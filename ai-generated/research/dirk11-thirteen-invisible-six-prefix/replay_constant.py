#!/usr/bin/env python3
"""Nonzero-norm witness for the constant ghost cubic. No tableau reduction."""
from itertools import permutations
from math import isqrt


def j4(x):
    return 42*x**4-84*x**3+56*x*x-14*x+1


def j5(x):
    return (2*x-1)*(66*x**4-132*x**3+84*x*x-18*x+1)


def readings(p, v, u, w):
    """Explicit modular transcript of the actual three-clean mark."""
    def dv(a,b):
        a, b = a%p, b%p
        assert b
        return a*pow(b,-1,p)%p

    def K(x):
        return (dv(x**4,4)-dv((u+v)*x**3,3)+dv(u*v*x*x,2))%p

    def J(x):
        return (dv(x**5,5)-dv((u+v)*x**4,4)+dv(u*v*x**3,3))%p

    def aff(s,l,r):
        return dv((u-s)*l+(s-v)*r,u-v)

    rr = (v,u,w)
    hv = v*j4(v)
    cv = [dv(v**3 * s*j4(s),6*hv) for s in rr]
    kv, ku, kw = cv
    at_v, at_u = dv(K(v),kv),dv(K(u),ku)
    Lw = (u+v-aff(w,at_v,at_u))%p
    m1 = dv(u*u,2)
    m2 = dv(u**3,3)+ku
    ad = dv(u*m1-m2,v*(u-v))
    ae = dv(m2-v*m1,u*(u-v))
    Av, Au = dv(v,2),dv(ad*kv+ae*ku,ku)
    Aw = aff(w,Av,Au)
    m1,m2,m3 = dv(w*w,2),dv(w**3,3)+kw,dv(w**4,4)+Lw*kw
    tail = []
    for s in rr:
        a,b = [r for r in rr if r!=s]
        tail.append(dv(m3-(a+b)*m2+a*b*m1,s*(s-a)*(s-b)))
    res = (sum(x*y for x,y in zip(tail,cv))-Aw*kw)%p

    # For alpha=1, the additional sole-gap clock is x=sum(regular)-2.
    # Its scalar gate is tested separately; it is not used by the norm proof.
    def pol2(x):
        out = 0
        for s,k in zip(rr,cv):
            a,b = [r for r in rr if r!=s]
            out += dv((J(s)-w*K(s))*(x-a)*(x-b), k*(s-a)*(s-b))
        return out%p
    return res,pol2


def check(p, lam):
    assert p>11 and all(p%d for d in range(2,isqrt(p)+1))
    nodes=[x for x in range(p) if (j5(x)+lam*j4(x))%p==0]
    assert len(nodes)==5 and all(x not in (0,1) and j4(x)%p for x in nodes)
    vals=[readings(p,*triple)[0] for triple in permutations(nodes,3)]
    prod=1
    for x in vals:
        prod=prod*x%p
    return nodes,vals,prod


if __name__=='__main__':
    for p in (43,181,227,419,463,1019,2029,4049,5003):
        if any(p%d==0 for d in range(2,isqrt(p)+1)):
            continue
        for lam in range(p):
            nodes=[x for x in range(p) if (j5(x)+lam*j4(x))%p==0]
            if len(nodes)!=5 or any(x in (0,1) or not j4(x)%p for x in nodes):
                continue
            nodes,vals,prod=check(p,lam)
            if prod:
                print(f"p={p}, lambda={lam}, split ordinary nonendpoint labels: {nodes}")
                print(f"Nonzero actual three-clean marked residuals: {len(vals)}")
                print(f"Product modulo {p}: {prod}")
                print("Exact specialization certifies a nonzero clock norm (finite candidate set).")
                raise SystemExit(0)
    raise AssertionError("No split specialization with live product")
