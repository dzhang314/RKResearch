"""Finite diagonals for regular true-quintic phases with ordinary eighth."""
from pathlib import Path
from sympy import isprime
import sys
root=Path(__file__).resolve().parent.parent
for dep in ("sdirk-eight-half-quadratic", "sdirk-eight-half-star-quadratic",
            "sdirk-eight-silent-one-eight-reverse-live-constant",
            "sdirk-eight-silent-one-seven-distinct-anchors",
            "sdirk-eight-silent-one-seven-distinct-coprime",
            "sdirk-eight-silent-one-seven-six-anchored",
            "sdirk-eight-silent-one-seven-six-reverse",
            "sdirk-eight-silent-one-seven-six-shared",
            "sdirk-eight-silent-three-closure", "sdirk-eight-silent-two-equal",
            "sdirk-eight-silent-two-high", "sdirk-eight-silent-two-unequal"):
    sys.path.append(str(root/dep))
from regular_star_projection import raw,evs
from regular_star_nonliteral import get_nonliteral
from regular_arith_projection import arithmetic,specialize_g,specialize_s,Bfield,gcdp,add,sc,nmod_poly
from regular_arith_nonliteral import nonliteral_arithmetic,resultant_sample

def star_checks(front,p,t,g):
    for slot in (2,3,4):
        P,Q,_,_,_=raw(front,slot)
        S,T=[evs(A,p,t,g) for A in (P,Q)]
        assert S.degree()==P.degrees()[1] and T.degree()==Q.degrees()[1]
        assert S.gcd(T).degree()==0
        print('finite regular star literal',front,slot,p,t,g,flush=True)
    H,_,_=get_nonliteral(front)
    out=[evs(P,p,t,g) for P in H]
    assert [q.degree() for q in out]==[P.degrees()[1] for P in H]
    for lam in range(1,20):
        S=sum(lam**i*q for i,q in enumerate(out[1:]))
        if out[0].gcd(S).degree()==0:break
    else:raise ArithmeticError('no specified nonliteral s-resultant factor')
    print('finite regular star nonliteral',front,p,t,g,lam,flush=True)

def composed(DD,n,F,H,p,t,g,lam):
    assert DD.degree()==n
    ff=specialize_g(F,p,t,g)
    rest=[specialize_g(P,p,t,g) for P in H]
    counts=[]
    for M,e in DD.factor()[1]:
        K=Bfield(M,p,t);s0=K(nmod_poly([0,1],p))
        U=specialize_s(ff,K,s0)
        assert len(U)==7 and bool(U[-1])
        J=[]
        for j,P in enumerate(rest):
            J=add(J,sc(specialize_s(P,K,s0),K(lam**j%p)))
        assert len(gcdp(U,J))==1
        counts.append(M.degree())
    return sorted(counts)

def arith_checks(front,p,t,g):
    for slot in (2,3,4):
        D,F,G,N,_=arithmetic(front,slot)
        ns=composed(evs(D,p,t,g),D.degrees()[1],F,[G,N],p,t,g,1)
        print('finite regular arithmetic literal',front,slot,p,t,g,1,ns,flush=True)
    F,H=nonliteral_arithmetic(front)
    DD=resultant_sample(F,H[0],p,t,g)
    ns=composed(DD,72,F,H,p,t,g,1)
    print('finite regular arithmetic nonliteral',front,p,t,g,1,ns,flush=True)

def main():
    p,t,g=1129,203,2
    assert isprime(p) and (2*t*t-1)%p==0
    for front in (True,False):
        star_checks(front,p,t,g)
        arith_checks(front,p,t,g)
    print('all regular ordinary-eighth orientations have finite characteristic-zero diagonal projections',flush=True)

if __name__=='__main__':
    main()
