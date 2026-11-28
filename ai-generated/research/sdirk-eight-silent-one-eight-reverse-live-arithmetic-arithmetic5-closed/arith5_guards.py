"""Leading-degree and true fourth-guard supports, verified in exact oriented algebras."""
from arith5_physical import physical
from arith5_fibers import check_all
from arith4_profile import basis
from arith4_projection import rankdrop
from arith4_guard_support import maybe_factor
from arith3_outer import checked_quotient
from arith2_aux import Factors,to_int,tiny
from arith_star_fibers import gpoly,modgamma
from check_star_family import F as ExField
from paired_proposals import fast_guard,prime_series,reduced_support
from star4_actual_fifth import Bfield,trim
from quadratic_poly import E
from regular_star_projection import Co,g
from flint import fmpq_poly
from collections import Counter
from functools import lru_cache

P,T=65537,2040

def norm(Q):return Q.a*Q.a-Q.b*Q.b/2

def rational_pieces(R):
    return [E(fmpq_poly(Q)).monic() for Q,e in Factors(to_int(R))]

@lru_cache(None)
def leading_support():
    A,B=physical()[:2]
    da,db=(gpoly(Co(Q,1)[-1]) for Q in (A,B))
    return norm(da).gcd(norm(db))

def gamma_guards():
    a,b,q,La,Lb,A0,B0,x,c,d,*_=basis()[-1]
    return list(map(gpoly,(g,La,Lb,x-a,x-b)))

def candidate_degree(Q,G,K):
    for p,t in prime_series():
        try:
            U=Bfield(modgamma(K.M,p,t),p,t)
            return len(reduced_support(Q,G,U))-1
        except (ArithmeticError,ValueError,ZeroDivisionError):continue
    raise ArithmeticError('no exact support proposal degree')

def one_guard(S,mode,labels):
    D,E0,*_,guards=physical()
    K=ExField(S)
    if any(not K(G) for G in gamma_guards()):
        return {'exact_gamma_collision':1},[],[]
    pol=lambda f:trim([K(gpoly(x)) for x in Co(f,1)])
    U,V=pol(D),pol(E0)
    Q=min((Z for Z in (U,V) if Z),key=len)
    L=modgamma(S,P,T)
    out,bad=check_all(L,P,T,mode,Q,False)
    steps=[]
    if not bad:return out,bad,steps
    jobs=['nodal_lead','terminal_h','anchor','quintic','terminal_q','nodal_at_terminal']
    names={name for name,e in labels}
    for name in sorted(jobs,key=lambda name:name not in names):
        G=pol(guards[name])
        if not G:return {'exact_whole_'+name:1},[],steps
        n=candidate_degree(Q,G,K)
        if not n:continue
        Q=fast_guard(K,Q,G,n,('stage5',mode,name))
        steps.append((name,n))
        out,bad=check_all(L,P,T,mode,Q,False)
        if not bad:break
    return out,bad,steps

def rankdrop_main():
    R=gpoly(rankdrop()).monic();N0=R.degree()
    assert N0==53
    candidates=rational_pieces(norm(R).gcd(leading_support()))
    print('stage5 independent rankdrop exact leading candidates',[S.degree() for S in candidates],flush=True)
    cnt=Counter();Pdeg=0
    for M in candidates:
        S=maybe_factor(R,M)
        if S is None:continue
        C=checked_quotient(R,S)
        assert C is not None and C.lc()==E(1)
        R=C;Pdeg+=S.degree()
        a,b,support=one_guard(S,'rankdrop',[('leading',1)])
        print('stage5 rankdrop exact degree specialization',M.degree(),S.degree(),dict(a),support,b,flush=True)
        assert not b
        cnt.update(a)
    assert R.degree()+Pdeg==N0
    F=modgamma(R,P,T)
    W,B=check_all(F,P,T,'rankdrop',verbose=False)
    print('stage5 rankdrop full degree and all local outcomes',N0,R.degree(),dict(cnt),dict(W),B,flush=True)
    assert not B

if __name__=='__main__':rankdrop_main()
