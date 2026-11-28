"""Bounded direct-oriented factor cover. Every retained clock is checked."""
from arith5_outer import loadQ,strip,gguards
from arith5_guards import (P,T,norm,leading_support,one_guard,
    maybe_factor,physical)
from arith3_outer import checked_quotient
from arith2_aux import Factors,to_int,tiny
from arith_star_fibers import modgamma
from arith5_fibers import check_all
from regular_star_projection import remove,g
from quadratic_poly import E
from flint import fmpq_poly
from collections import Counter
from functools import lru_cache

@lru_cache(None)
def proposals():
    A,B,*_,guards=physical()
    known={}
    def register(label,pol):
        for H,e in Factors(pol):
            known.setdefault(tuple(H),[]).append((label,e))
    register('leading',to_int(leading_support()))
    lead,n=remove(guards['nodal_lead'],[g,guards['quintic']])
    assert n==[4,1] and lead.degrees()==(0,5,14,1)
    for label,G in [('nodal_lead',lead),('terminal_h',guards['terminal_h']),
                     ('anchor',guards['anchor']),('quintic',guards['quintic']),
                     ('terminal_q',guards['terminal_q'])]:
        register(label,tiny(A,G,label))
    print('stage5 exact norm proposals',[(len(H)-1,L) for H,L in known.items()],flush=True)
    return [(E(fmpq_poly(list(H))).monic(),L) for H,L in known.items()]

def power(X,n):
    Z=E(1)
    while n:
        if n%2:Z*=X
        n//=2
        if n:X*=X
    return Z

def full_power(Q,S):
    """Residue multiplicity only proposes; exact whole polynomial division verifies."""
    A,B=(modgamma(X,P,T) for X in (Q,S))
    if not B.degree():raise ArithmeticError('missing degree')
    guess=0
    while not A%B:A//=B;guess+=1
    assert guess
    K=checked_quotient(Q,power(S,guess))
    if K is not None:
        assert K.lc()==E(1)
        return K,guess
    # Some extra factors may merge at this selected place.
    e=0
    while True:
        T0=checked_quotient(Q,S)
        if T0 is None:break
        Q=T0;e+=1
    assert e and Q.lc()==E(1)
    return Q,e

def cover():
    A=loadQ()
    Q,ss=strip(A)
    assert (A.degree(),Q.degree(),ss)==(3517,3509,[0,0,0,0,8])
    print('stage5 oriented actual gamma strip',A.degree(),Q.degree(),ss,flush=True)
    Q=Q.monic()
    L=[]
    for M,labels in proposals():
        S=maybe_factor(Q,M)
        if S is None:continue
        assert checked_quotient(M,S) is not None
        Q,n=full_power(Q,S)
        print('stage5 directly verified oriented factor',M.degree(),S.degree(),n,labels,
              'remaining',Q.degree(),flush=True)
        L.append((M.degree(),S,labels,n))
    assert Q.degree()+sum(S.degree()*n for _,S,_,n in L)==A.degree()-sum(G.degree()*e for G,e in zip(gguards(),ss))
    return Q,L

def main():
    U,L=cover()
    out=Counter()
    for D,S,names,e in L:
        a,b,gs=one_guard(S,'pivot',names)
        print('stage5 complete guarded orientations',D,S.degree(),e,names,dict(a),
              'exact support',gs,'remaining',b,flush=True)
        assert not b
        out.update(a)
    V=modgamma(U,P,T)
    print('stage5 whole oriented quotient input',U.degree(),len(V.factor()[1]),flush=True)
    a,b=check_all(V,P,T,'pivot',verbose=False)
    print('stage5 complete genuine silent-fifth enforced census',dict(out),dict(a),'remaining',b,flush=True)
    assert not b

if __name__=='__main__':main()
