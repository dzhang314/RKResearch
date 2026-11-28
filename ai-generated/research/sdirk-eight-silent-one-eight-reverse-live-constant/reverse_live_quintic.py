"""Full projection and five-peg mask for the conditional pure-quintic profile."""
from seven_k0_anchors import *
from extra_active import invpoly
from unequal_finite import Tower
from equal_undetected_front import Nested
from gauss_separate import span_unit
from flint import nmod_poly
from itertools import combinations
from functools import lru_cache
from sympy import isprime

L5=(-1,30,-210,560,-630,252)

@lru_cache(None)
def profile_gamma(front,profile):
    A,B,m=map(lambda b:cv(F2,b),ends(front,1))
    ha,hb=(A-1)/2,(B-1-m)/2
    D0=[F2(x)*(A**i/ha-B**i/hb) for i,x in enumerate(profile)]
    D=mon(D0)
    assert len(D)==len(profile) and len(gcdp(D,[F2(0),F2(1)]))==1
    H4=[cv(F2,w) for w in pol(h4(front),lambda x:x)]
    return D,(A,B,m,ha,hb,H4)

def gap(K,g,x,rear,profile=L5):
    u=[K(0),K(1)]; k=[K(1),K(2),K(-1)]
    c=[x,-g]
    d=[x-2*g,g] if rear else [x,-2*g]
    L=list(map(K,profile));pc,pd,px=subst(L,c),subst(L,d),ev(L,x)
    if rear is None:
        U=[K(-2),K(1)]
        F=add(mul(U,pc),sc(add(sc(u,2),mul(k,U)),-px))
        guards=u
    elif rear:
        F=sum_poly([mul([K(2),K(-1)],pc),sc(mul(u,pd),-1),sc(mul(k,[K(-2),K(2)]),px)])
        guards=nodal([K(0),K(1),K(2)])
    else:
        H=[K(-2),K(1),K(4),K(-1)]; J=[K(2),K(3),K(-12),K(4)]
        F=sum_poly([sc(mul(J,pc),2),mul(H,pd),sc(mul(k,J),-px)])
        guards=[K(0),K(0),K(1)]
    R,E=qr(F,guards)
    assert not E
    return R

def mask(V,pegs):
    L=mon(list(map(V,L5)))
    W=[sum(L[j]/(j-i) for j in range(i+1,6)) for i in range(5)]
    W=invpoly(V,W,L)
    rows=[]
    for a in pegs:
        l=ev(L,a)
        rows.append([l,l*a,l*a*a,ev(W,a),l*a**3])
    return [det([rows[j] for j in I]) for I in combinations(range(len(pegs)),5)]

def mode(front,rear,slot,p,t,verbose=False):
    assert slot in (2,3,4,5,8) and (rear is None)==(slot==8)
    D,data=profile_gamma(front,L5)
    F=Bfield(nmod_poly([0,1],p),p,t)
    M=nmod_poly([int(F(q).x[0]) for q in D],p)
    assert M.degree()==5 and M.leading_coefficient()==1
    cnt=0
    for M0,e in M.factor()[1]:
        K=Bfield(M0,p,t);g=K(nmod_poly([0,1],p));x=1-g
        A,B,m,ha,hb,H4=data
        A,B,m,ha,hb=map(K,(A,B,m,ha,hb));H4=list(map(K,H4))
        LP=[K(v)*g**j for j,v in enumerate(L5)]
        R=add(sc(LP,ha),sc(H4,-ev(LP,A)))
        S,Err=qr(R,nodal([A,B]));assert not Err and len(S)==4
        S=mon(S);K0=Tower(S);s=K0.gen();g0=K0(g);x0=K0(x)
        U0=gap(K,g,x,rear)
        nd=5 if rear is None else (2 if rear else 6)
        assert len(U0)==nd+1,(slot,front,rear,M0.degree(),len(U0)-1)
        W=Nested(list(map(K0,mon(U0))));u=W.gen();X=W(x0);G=W(g0)
        a,b,q=G*W(K0(A)),G*W(K0(B)),G*W(s)
        c=X-G*u;d=X-G*(2-u if rear else 2*u)
        pegs=[a,b,q,X,c]+([] if rear is None else [d])
        if slot<=4: pegs.pop(slot-2)
        gates=mask(W,pegs)
        if slot<=4:
            L=list(map(W,L5));z={2:a,3:b,4:q}[slot];k=1+2*u-u*u
            gates.append((X-z)*ev(L,c)-k*(c-z)*ev(L,X))
        span_unit(W,*gates)
        cnt+=1
    if verbose:print('live constant pass',front,rear,slot,p,t,cnt,flush=True)
    return cnt
