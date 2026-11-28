"""Exact oriented factor cover, without materializing any large outer norm."""
from arith3_outer import loadQ,strip,checked_quotient
from arith3_projection import rankdrop
from arith3_physical import s_projections,literal3
from arith3_fibers import check_all
from arith2_aux import tiny,to_int,Factors
from arith3_outer import gguards
from arith_star_fibers import gpoly,modgamma
from check_star_family import F as ExField
from paired_proposals import recover,fast_guard,prime_series,reduced_support
from star4_actual_fifth import Bfield,trim
from quadratic_poly import E
from regular_star_projection import Co
from flint import fmpq_poly
from functools import lru_cache
from collections import Counter

P=65537
T=2040
@lru_cache(None)
def proposals():
    A,B=s_projections()
    guards=literal3()[5]
    # Candidate factors only, all selected divisibility checked below.
    da,db=(gpoly(Co(Z,1)[-1]) for Z in (A,B))
    n=lambda Q:Q.a*Q.a-Q.b*Q.b/2
    out={}
    def register(label,M):
        for Q,e in Factors(M):
            out.setdefault(tuple(Q),[]).append((label,e))
    register('leading',to_int(n(da).gcd(n(db))))
    for name,i in [('anchor',3),('quintic',9),('terminal_h',10),('x_eq_q',8)]:
        register(name,tiny(A,guards[i],name))
    assert out
    print('guard proposal norm pieces',[(len(Q)-1,L) for Q,L in out.items()],flush=True)
    return [(E(fmpq_poly(list(M))).monic(),L) for M,L in out.items()]

def maybe_factor(Q,M):
    n0=M.degree()
    zz=modgamma(M,P,T);zq=modgamma(Q,P,T)
    n=zz.gcd(zq).degree()
    if not n:return None
    if n==n0 and checked_quotient(Q,M) is not None:return M
    # An accidental increase at p cannot justify any division.
    for p,t in prime_series():
        n=min(n,modgamma(M,p,t).gcd(modgamma(Q,p,t)).degree())
        if p>2**60+2000:break
    if not n:return None
    def trial(p,t):
        D=modgamma(M,p,t).gcd(modgamma(Q,p,t))
        return [int(D[i]) for i in range(n)] if D.degree()==n else []
    def verify(A,B):
        S=E(fmpq_poly([*A,1]),fmpq_poly(B))
        if checked_quotient(M,S) is None or checked_quotient(Q,S) is None:return None
        return S
    return recover(n,trial,verify,('actual oriented stage3 factor',n0,n))

def cover():
    F=proposals()
    ret=[]
    for mode,A in [('pivot',loadQ()),('rankdrop',gpoly(rankdrop()))]:
        Q,d=strip(A)
        Q=Q.monic()
        print('stage3 exact initial guard strip',mode,A.degree(),Q.degree(),d,flush=True)
        L=[]
        for M,names in F:
            S=maybe_factor(Q,M)
            if S is None:continue
            count=0
            while True:
                B=checked_quotient(Q,S)
                if B is None:break
                Q=B
                assert Q.lc()==E(1)
                count+=1
            assert count and S.degree()
            print('stage3 direct orientation support',mode,M.degree(),S.degree(),count,names,
                  'remaining degree',Q.degree(),flush=True)
            L.append((S,names,count))
        assert Q.degree()+sum(S.degree()*e for S,n,e in L)==A.degree()-sum(q.degree()*k for q,k in zip(gguards(),d))
        ret.append((mode,Q,L))
    return ret

def proposal_degree(Q,G,K):
    for p,t in prime_series():
        try:
            U=Bfield(modgamma(K.M,p,t),p,t)
            return len(reduced_support(Q,G,U))-1
        except (ArithmeticError,ValueError,ZeroDivisionError):continue
    raise ArithmeticError('no exact guard proposal degree')

def one_guard(S,mode,labels):
    D,E0=s_projections()
    guards=literal3()[5];K=ExField(S)
    if any(not K(G) for G in gguards()):
        return {'exact_gamma_collision':1},[],[]
    pol=lambda f:trim([K(gpoly(x)) for x in Co(f,1)])
    U,V=pol(D),pol(E0)
    Q=min((x for x in (U,V) if x),key=len)
    L=modgamma(S,P,T)
    K0,B=check_all(L,P,T,mode,Q,False)
    history=[]
    if not B:return K0,B,history
    available={name for name,n in labels}
    jobs=[('anchor',3),('terminal_h',10),('quintic',9),('x_eq_q',8)]
    for name,i in sorted(jobs,key=lambda row:row[0] not in available):
        G=pol(guards[i])
        if not G:return {'exact_whole_'+name:1},[],history
        n=proposal_degree(Q,G,K)
        if not n:continue
        Q=fast_guard(K,Q,G,n,('stage3',mode,name))
        history.append((name,n))
        K0,B=check_all(L,P,T,mode,Q,False)
        if not B:break
    return K0,B,history

def main():
    all0=cover()
    for mode,Q,L in all0:
        total=Counter()
        for S,lab,e in L:
            out,bad,steps=one_guard(S,mode,lab)
            print('stage3 all guard fibres',mode,S.degree(),e,lab,dict(out),
                  'exact support removed',steps,'remaining',bad,flush=True)
            assert not bad
            total.update(out)
        F=modgamma(Q,P,T)
        n=len(F.factor()[1])
        print('stage3 entire generic quotient',mode,Q.degree(),n,flush=True)
        out,bad=check_all(F,P,T,mode,verbose=False)
        print('stage3 complete generic quotient result',mode,dict(out),'remaining',bad,flush=True)
        assert not bad
        print('stage3 complete exact and local census',mode,dict(total),dict(out),flush=True)

if __name__=='__main__':main()
