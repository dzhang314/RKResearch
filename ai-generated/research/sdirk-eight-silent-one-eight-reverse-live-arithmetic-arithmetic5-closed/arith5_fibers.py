"""Complete physical silent-fifth residue factors with both modes retained."""
from arith5_physical import physical
from arith4_profile import basis
from arith_star_diagonal import int_input
from check_star_arithmetic67 import gfiber
from star4_actual_fifth import Bfield,gcdp,trim,sv
from silent8_fibers import sfactors,getpoly
from ordinary_reconstruction import extend
from flint import nmod_poly,fmpz_mpoly_ctx
from collections import Counter
from functools import lru_cache

I=fmpz_mpoly_ctx.get(['g','s'])
@lru_cache(None)
def fourth_inputs(p,t):
    U=[]
    for A,B,_ in map(int_input,physical()[:2]):
        U.append(I.from_dict({j:(A.get(j,0)+2*t*B.get(j,0))%p for j in A.keys()|B.keys()}))
    return U

def use_s(K,g0,G,p,t,mode):
    _,_,N,S,F,J,_=physical()
    U,s,inc=extend(K,G);g=inc(g0)
    pols=[N,S,F,J]
    if mode=='rankdrop':pols.extend(basis()[4])
    elif mode=='pivot':
        from arith5_projection import pivot_silent_gate
        pols.append(pivot_silent_gate())
    else:raise ValueError(mode)
    Z=[getpoly(Q,U,g,s,p,t) for Q in pols]
    W=next((p0 for p0,q0 in zip(Z,pols) if len(p0)==q0.degrees()[0]+1),None)
    if W is None:return 'u_leading',tuple(len(q)-1 for q in Z)
    for q in Z:W=gcdp(W,q)
    assert W
    if len(W)==1:return 'no_paid_silent_fifth_tail',None
    return 'open_actual_fifth_tail',len(W)-1

def check_all(A,p,t,mode,Q0=None,verbose=True):
    D,E=fourth_inputs(p,t)
    counts=Counter();bad=[];coverage=nmod_poly([1],p)
    gs=physical()[-1]
    for R,e in A.factor()[1]:
        coverage*=R**e
        K=Bfield(R,p,t);g=K(nmod_poly([0,1],p));d=R.degree()
        X,Y=map(lambda Q:gfiber(Q,K),(D,E))
        q=trim([K(z.v) for z in Q0]) if Q0 is not None else []
        Q=next((P for P,n in ((q,len(Q0) if Q0 else -1),(X,49),(Y,55)) if P and len(P)==n),None)
        if Q is None:
            bad.append((d,e,'s_leading',len(X)-1,len(Y)-1));continue
        for T in (X,Y,q):Q=gcdp(Q,T)
        assert Q
        if len(Q)==1:
            counts['no_s']+=1;continue
        for G,m in sfactors(Q,K):
            try:r,v=use_s(K,g,G,p,t,mode)
            except (AssertionError,ArithmeticError,ValueError,ZeroDivisionError) as err:
                r,v='arithmetic_fail',str(err)
            if r=='no_paid_silent_fifth_tail':counts[r]+=1
            else:
                detail={i:d for i,H in gs.items() if (d:=len(gcdp(G,sv(H,K,g,p,t)))-1)}
                bad.append((R.degree(),e,len(G)-1,r,v,detail))
        if verbose:print('stage5 all actual silent checked',mode,R.degree(),e,dict(counts),'open',bad[-1:],flush=True)
    assert coverage==A
    return counts,bad
