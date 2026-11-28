"""Exact same physical-fifth/nodal guard source, with modular cover proposals only."""
from arith67_model import model
from arith67_outer import oriented
from regular_star_projection import Co
from arith_star_fibers import gpoly
from nodal_guard_aux import small_guard
from star4_guarded_fibers import modQ
from flint import fmpz_poly,fmpq_poly,nmod_poly
from math import lcm
from pathlib import Path
from functools import lru_cache

def to_int(Q):
    d=lcm(*(int(x.q) for x in Q))
    P=fmpz_poly([int(x*d) for x in Q]);return P//P.content()

def facts(P):
    F=[];N=fmpz_poly([1])
    for V,e in P.factor_squarefree()[1]:
        for U,b in V.factor()[1]:
            assert b==1
            U=U if U[U.degree()]>0 else -U
            F.append((U,e));N*=U**e
    assert N==P or N==-P
    return F

def proposals():
    A,B,J,*_=model()
    Q=[gpoly(Co(P,1)[-1]) for P in (A,B,J)]
    R=[U.a*U.a-U.b*U.b/2 for U in Q]
    W=R[0].gcd(R[1]).gcd(R[2])
    X=[('leading',f,e) for f,e in facts(to_int(W))]
    X.extend(('nodal_lead',f,e) for f,e in facts(small_guard()))
    print('same physical J and true R4 exact sources',[(k,x.degree(),e) for k,x,e in X],flush=True)
    J={}
    for k,P,e in X:J.setdefault(tuple(P),[]).append((k,e))
    return [(fmpz_poly(list(P)),L) for P,L in J.items()]

@lru_cache(None)
def oriented_mod(p,t):
    P=oriented(p,2*t%p);assert P
    h=next(i for i,a in enumerate(P) if a)
    return nmod_poly(P[h:],p)

def norm_proposal(p=65537,t=2040):
    U,V=(oriented_mod(p,w) for w in (t,p-t))
    assert U.degree()==V.degree()==6843
    T=U*V;T*=pow(int(T.leading_coefficient()),-1,p)
    D=T;out=[]
    for M,L in proposals():
        E=fmpq_poly(M);E=E*(1/E[E.degree()])
        try:C=modQ(E,p)
        except (ArithmeticError,ValueError):continue
        e=0;A=T
        while A and not A%C:A//=C;e+=1
        if not e:
            k=C.gcd(T).degree()
            if k:print('part-only exact source proposal',M.degree(),L,k,flush=True)
            continue
        n=C.gcd(U).degree()
        print('exact source full modular cover proposal',M.degree(),e,n,L,flush=True)
        out.append((M,e,n,L))
        for _ in range(e):
            if D%C:break
            D//=C
    F=D.gcd(U)
    print('modular proposal quotient and oriented factors',D.degree(),F.degree(),
          [(M.degree(),e) for M,e in F.factor()[1]],flush=True)
    assert D.degree()==7038 and F.degree()==3519
    assert sorted((M.degree(),e,n) for M,e,n,L in out)==[
        (4,108,4),(8,144,4),(18,24,9),(24,18,12),(42,72,21),(48,2,24),(60,18,30)]
    return out

def main():
    O=norm_proposal()
    Path('arith67-cover-plan.txt').write_text('\n'.join(str(e)+' '+str(n)+' '+str(L)+' '+
          ' '.join(map(str,M)) for M,e,n,L in O))
if __name__=='__main__':main()
