#!/usr/bin/env python3
"""Exact fixed-coefficient checks for the localized reverse cubic continuation."""
from itertools import combinations,permutations
from collections import Counter

P=1013
D6=(-42,840,-5040,12600,-13860,5544)
INTERIOR=(347,468,507,546,667)
LIVE=(*INTERIOR,1)

def add(a,b): return (a+b)%P

def val(f,x):
    v=0
    for a in reversed(f): v=add(v*x,a)
    return v

def mul(f,g):
    h=[0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g): h[i+j]=add(h[i+j],a*b)
    return h

def hull(nodes):
    f=[1]
    for x in nodes: f=mul(f,[-x,1])
    return f

def integrate(f):
    return [0]+[v*pow(i+1,-1,P)%P for i,v in enumerate(f)]

def J(f,x=1): return val(integrate(f),x)

def scale(f,s): return [v*s%P for v in f]

def p_add(f,g):
    return [add(f[i] if i<len(f) else 0,g[i] if i<len(g) else 0)
            for i in range(max(len(f),len(g)))]

def card(pts,x):
    f=hull(y for y in pts if y!=x)
    return scale(f,pow(val(f,x),-1,P))

def rows(G,polys,cap):
    v=[integrate(f) for f in polys]
    return [[J(mul([0]*i+G,f)) for f in v] for i in range(cap-len(G)+2)]

def rank2(M):
    return any((x*w-y*z)%P for (x,y),(z,w) in combinations(M,2))

def hull_checks():
    for early in combinations(LIVE,3):
        late=tuple(x for x in LIVE if x not in early)
        F=hull((0,*early))
        for k in range(3):
            for overlap in combinations(early,k):
                G=hull((*late,*overlap))
                assert any(a[0] for a in rows(G,[F],6))
                yield "asymmetric"
                if k<=1:
                    assert rank2(rows(G,[F,[0]+F],5))
                    yield "symmetric"

def phase_values(a,d,v,u,L,T,phase):
    Td,Tv,Tu=(T[x] for x in (d,v,u))
    if phase=="before":
        num=-(v-2*d)*v**3
        den=d**3*(2*v-d)
        D=den*Tu
        Pv=num*Tu
        Pu=-(Td*den+Tv*num)
    else:
        num=u**3*(2*v-u)
        den=v**3*(2*u-v)
        D=den*Tv+num*Tu
        Pv=-Td*den
        Pu=-Td*num
    # D is proved nonzero in characteristic zero by the corresponding actual
    # chronology, but is never inverted in this coefficient reduction.
    return [x%P for x in (D,Pv,Pu)]

def chart_checks(a,b,c,d,v,u):
    pts=(0,a,d,v,u)
    L={x:card(pts,x) for x in (d,v,u)}
    T={x:J(f,a) for x,f in L.items()}
    assert all(T.values())
    yield "literal_taps"
    P0=hull(pts)
    assert J(P0,a)
    yield "singleton_leading"
    B=hull((0,0,a,a,b))
    assert (J(B,a)*J(P0,b)-J(B,b)*J(P0,a))%P
    yield "unspent"
    for phase in ("before","after"):
        D,Pv,Pu=phase_values(a,d,v,u,L,T,phase)
        projs={v:Pv,u:Pu}
        for spent in (d,v,u):
            if spent==d:
                values={v:Pv*(v-d),u:Pu*(u-d)}
            else:
                r=u if spent==v else v
                values={d:D*(d-spent),r:projs[r]*(r-spent)}
            R=[0]
            for x,s in values.items(): R=p_add(R,scale(L[x],s))
            G=hull((b,c,*(x for x in (d,v,u) if x!=spent)))
            assert rank2(rows(G,[P0,R],5)), (a,b,c,d,v,u,phase,spent)
            yield "first_spent_"+phase
    assert (5*d*d-(3*a+4*b)*d+2*a*b)%P
    yield "separable_derivative"

def main():
    assert all(P%k for k in range(2,32)) and D6[-1]%P
    assert tuple(z for z in range(P) if val(D6,z)==0)==INTERIOR
    census=Counter(hull_checks())
    for a,b,c,d,v,u in permutations(LIVE):
        if a==1 or b==1: continue
        census.update(chart_checks(a,b,c,d,v,u))
    assert dict(census)=={
        "asymmetric":140,"symmetric":80,"literal_taps":480,
        "singleton_leading":480,"unspent":480,"first_spent_before":1440,
        "first_spent_after":1440,"separable_derivative":480}
    for k,n in census.items(): print(f"mod 1013, {k}: {n} nonzero/rank-two cases")

if __name__=="__main__": main()
