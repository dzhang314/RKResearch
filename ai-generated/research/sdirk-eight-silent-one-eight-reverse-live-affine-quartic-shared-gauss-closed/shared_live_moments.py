"""Deflated Gauss-hole moments on every surviving exact cubic gap."""
from shared_live_chrono import *
from gauss_separate import span_unit
from sympy import isprime

def deflated_moments(K,r,D,Q,slot):
    # Q is the monic Legendre quotient L4/(X-r) over the full finite algebra.
    qr=ev(Q,r);qi=qr.inv()
    nu=intp(K,Q)*qi
    I=lambda j:K(1)/(j+1)-nu*r**j
    ID=lambda P,k=0:sum((a*I(i+k) for i,a in enumerate(P)),K(0))
    def W(P):
        return [sum((P[j]*I(j-i-1) for j in range(i+1,len(P))),K(0))
                for i in range(len(P)-1)]
    if slot==8:
        # Only one remaining ordinary nonhole clock. Do not invert its mask.
        assert len(D)==7
        M0,M1=ID(D),ID(D,1)
        D=mul(D,[-M1,M0])
        M=[K(0)]
    else:
        assert len(D)==8
        M=[ID(D)]
    bez=add(mul(Q,W(D)),sc(mul(D,W(Q)),-1))
    return M+bez[1:]

def full_reduced(M,t,p,Fp):
    """Permit no full-degree loss, selected factor, or individual gap discard."""
    B=Bfield(nmod_poly([0,1],p),p,t)
    N=B.cast(Epoly(M))
    assert M.degree()==N.degree()==12 and int(N.leading_coefficient())==1
    pieces=N.factor()[1]
    C=nmod_poly([1],p)
    for J,e in pieces:
        assert e==1
        C*=J
    assert C==N
    for J,e in pieces:
        K=Bfield(J,p,t)
        F=list(map(K,Fp))
        assert len(F)==4 and F[-1]==1
        V=Tower(F)
        yield V,V.gen()

def check_tail(front,M,slot,p,t):
    T,data=exact_gap(front,M,slot)
    assert len(T)==4 and T[-1]==data[0](1) and slot in (6,8)
    t0=data[1:8]
    n=0
    for K,u in full_reduced(M,t,p,T):
        g,X,R,A,B,s,y=map(K,t0)
        r=g*R
        L=list(map(K,Lco))
        Q,rem=divp(L,[-r,K(1)])
        assert not rem and len(Q)==4
        Q=mon(Q)
        c=X-u;d=X-2*u
        pegs=[A,B,s,y,X,c]+([] if slot==8 else [d])
        D=list(map(K,nodal([g*z for z in pegs])))
        out=deflated_moments(K,r,D,Q,slot)
        span_unit(K,*out)
        n+=1
    assert n==(4 if front else 2)
    print('deflated full cubic gap units',front,slot,p,t,n,flush=True)
    return n

def main():
    p,t=1103,161
    assert isprime(p) and 2*t*t%p==1
    for front in (True,False):
        M,=exact_factors(front)
        assert M.degree()==12
        assert first_census(front,M) is None
        E,y=early5(front,M)
        assert len(E)==2 and y is not None
        for slot in (2,3,4,5):
            G,_=exact_gap(front,M,slot);assert len(G)==1
        for slot in (6,8):
            check_tail(front,M,slot,p,t)

    print('all actual reverse-live affine quartic shared-root strata excluded',flush=True)
