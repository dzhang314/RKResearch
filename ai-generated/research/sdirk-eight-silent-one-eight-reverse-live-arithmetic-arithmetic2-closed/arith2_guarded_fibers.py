"""Exact orientation-cover and exact monic fourth-guard lessons in literal two."""
from arith2_projection import projections
from arith2_model import model
from arith2_outer import residue_inputs
from arith2_cover_probe import orient_mod
from arith2_fibers import use_s
from arith_star_fibers import gpoly,modgamma
from check_star_family import F as ExField,Split
from paired_proposals import recover,fast_guard,prime_series,reduced_support
from quadratic_poly import E
from regular_star_projection import Co,red
from star4_actual_fifth import Bfield,trim,sc,gcdp,sv,nmod_poly
from star4_guarded_fibers import modQ
from silent8_fibers import sfactors
from check_star_arithmetic67 import gfiber
from flint import fmpq_poly,fmpz_poly
from pathlib import Path
from collections import Counter
from time import perf_counter

p=65537
t=2040

def ration(M):
    U=fmpq_poly(M);return E(U*(1/U[U.degree()]))

def exact_orientation(M,n):
    d=M.degree()
    if n==d:return M
    assert 0<n<d
    def trial(p,t):
        A=modgamma(M,p,t);B=orient_mod(p,t)
        G=A.gcd(B)
        return [int(G[i]) for i in range(n)] if G.degree()==n else []
    def check(A,B):
        S=E(fmpq_poly([*A,1]),fmpq_poly(B))
        if M%S:return None
        T=M.exact(S)
        G=modgamma(T,p,t)
        assert G.degree()==T.degree() and G.leading_coefficient()==1
        if G.gcd(orient_mod(p,t)).degree():return None
        return S
    S=recover(n,trial,check,('checked literal2 orientation',d,n))
    assert S.degree()==n and S.lc()==E(1)
    return S

def chosen_guard_degree(Q,G,K):
    for pp,tt in prime_series():
        try:
            C=Bfield(modgamma(K.M,pp,tt),pp,tt)
            L=reduced_support(Q,G,C)
            return len(L)-1
        except (ArithmeticError,ValueError,ZeroDivisionError):continue
    raise RuntimeError('no exact support proposal')

def all_small(S,U=None):
    A,B=residue_inputs(p,2*t)
    M=modgamma(S,p,t);assert M.degree()==S.degree() and M.leading_coefficient()==1
    count=Counter();openx=[];out=[]
    F=M.factor()[1]
    T=nmod_poly([1],p)
    for R,e in F:
        T*=R**e
        K=Bfield(R,p,t);g=K(nmod_poly([0,1],p))
        D,E0=(gfiber(P,K) for P in (A,B))
        Q=trim([K(v.v) for v in U]) if U is not None else []
        W=next((z for z,d in ((Q,len(U) if U else -1),(D,28),(E0,46))
                if z and len(z)==d),None)
        if W is None:
            openx.append((R.degree(),'s_leading',len(D)-1,len(E0)-1));continue
        for V in (Q,D,E0):W=gcdp(W,V)
        assert W
        if len(W)==1:count['no_s']+=1;continue
        for X,e in sfactors(W,K):
            try:r,k=use_s(K,g,X,p,t)
            except (ArithmeticError,AssertionError,ValueError,ZeroDivisionError) as e1:
                r,k='unsupported_work',str(e1)
            if r in ('unsupported_work','raw_gap_leading','actual_nodal_lead','open_true_ordinary_fifth'):
                q={}
                for n,P in zip(('g','La','Lb','anchor','s_eq_a','s_eq_b','x_z','x_b','x_q','quintic','terminal_h'),model()[5]):
                    U0=gcdp(X,sv(P,K,g,p,t))
                    if len(U0)>1:q[n]=len(U0)-1
                openx.append((R.degree(),len(X)-1,r,k,q))
            else:count[r]+=1
    assert T==M
    return count,openx

def one_guard(S,labels):
    D,E0=projections()
    G=model()[5];K=ExField(S)
    unit1=red(G[0]*G[1]*G[2]*G[6]*G[7])
    if not K(gpoly(unit1)):return {'exact_gamma_collision':1},[],[]
    pol=lambda f:trim([K(gpoly(x)) for x in Co(f,1)])
    required=list(map(pol,(D,E0)))
    Q=min((x for x in required if x),key=len)
    summary=[]
    U,B=all_small(S,Q)
    if not B:return U,B,summary
    jobs=[('anchor',3),('terminal_h',10),('quintic',9),('x_eq_q',8)]
    available={name for name,_ in labels}
    for key,i in sorted(jobs,key=lambda row:row[0] not in available):
        G1=pol(G[i])
        if not G1:return {'exact_whole_'+key:1},[],summary
        n=chosen_guard_degree(Q,G1,K)
        if not n:continue
        Q=fast_guard(K,Q,G1,n,key)
        summary.append((key,n))
        U,B=all_small(S,Q)
        if not B:break
    return U,B,summary

def loads():
    p=Path('arith2-cover-plan.txt')
    for l in p.read_text().splitlines():
        from ast import literal_eval
        e,k,text=l.split(' ',2)
        j=text.index(']')
        lab=literal_eval(text[:j+1]);A=list(map(int,text[j+1:].split()))
        yield fmpz_poly(A),int(e),int(k),lab

def main():
    totals=Counter()
    for P,e,n,j in loads():
        if n==0:
            M=modgamma(ration(P),p,t)
            assert M.degree()==P.degree() and M.leading_coefficient()==1
            assert M.gcd(orient_mod(p,t)).degree()==0
            print('true whole case no oriented root',P.degree(),e,j,flush=True)
            totals["no_orientation"]+=1
            continue
        S=exact_orientation(ration(P),n)
        C,B,X=one_guard(S,j)
        assert not B,(P.degree(),e,n,j,B,X)
        totals.update(C)
        print('oriented literal2 guard branch',P.degree(),e,n,j,dict(C),
              'exact support',X,flush=True)
    print('complete exact small pieces and guard checks',dict(totals),flush=True)

if __name__=='__main__':main()
