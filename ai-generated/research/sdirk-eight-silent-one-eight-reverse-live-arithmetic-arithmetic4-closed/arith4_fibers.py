"""Supported p-local complete physical-3 fibres, separate geometric pivot modes."""
from arith4_physical import literal4,s_projections
from arith4_profile import basis
from arith2_fibers import mono
from arith_star_diagonal import int_input
from arith_star_model import literal_fifth_poly
from check_star_arithmetic67 import gfiber
from star4_actual_fifth import Bfield,gcdp,sc,trim,lv,pe,sv
from ordinary_reconstruction import divide_root,extend
from silent8_fibers import sfactors,getpoly
from flint import nmod_poly,fmpz_mpoly_ctx
from collections import Counter
from functools import lru_cache

I=fmpz_mpoly_ctx.get(['g','s'])
@lru_cache(None)
def sinput(p,t):
    U=[]
    for A,B,_ in map(int_input,s_projections()):
        U.append(I.from_dict({j:(A.get(j,0)+2*t*B.get(j,0))%p for j in A.keys()|B.keys()}))
    return U

@lru_cache(None)
def g_equations(mode):
    if mode=="rankdrop":return tuple(basis()[4])
    if mode=="pivot":return ()
    raise ValueError(mode)

def use_s(K,g0,T,p,t,mode):
    F,G,P0,Cross,N,guards,H,R,clocks=literal4()
    G5=literal_fifth_poly()
    U,s,inc=extend(K,T);g=inc(g0)
    Ps=[getpoly(z,U,g,s,p,t) for z in (F,G,N,P0,Cross)]
    m=next((A for A,d in zip(Ps,(z.degrees()[0] for z in (F,G,N,P0,Cross))) if len(A)==d+1),None)
    for Q in g_equations(mode):
        A=getpoly(Q,U,g,s,p,t)
        if m is None and len(A)==Q.degrees()[0]+1:m=A
        Ps.append(A)
    if m is None:return 'gap_leading',tuple(len(q)-1 for q in Ps)
    W=m
    for q in Ps:W=gcdp(W,q)
    assert W
    if len(W)==1:return 'no_gap',None
    V,u,inc0=extend(U,mono(W));ga=inc0(g);x=1-ga;c=x-ga*u;d=x-2*ga*u
    H0,R0=([inc0(lv(h,U,g,s,p,t)) for h in A] for A in (H,R))
    Hc,Rc=pe(H0,c),pe(R0,c)
    n=trim([Hc*(R0[i] if i<5 else V(0))-Rc*h for i,h in enumerate(H0)])
    if len(n)!=6:return 'nodal_leading',None
    n=divide_root(divide_root(mono(n),c,V),d,V);assert len(n)==4
    gf=getpoly(G5,U,g,s,p,t);ig=ga.inv()
    WY=[inc0(z)*ig**i for i,z in enumerate(gf)]
    B=gcdp(n,WY)
    if len(B)==1:return 'no_true_fifth',None
    return 'open_true_fifth',len(B)-1

def check_all(R,p,t,mode,Q0=None,verbose=True):
    U,V=sinput(p,t)
    out=Counter();bad=[];d0=nmod_poly([1],p)
    gd=literal4()[5]
    for M,e in R.factor()[1]:
        d0*=M**e
        K=Bfield(M,p,t);g=K(nmod_poly([0,1],p));md=M.degree()
        A,B=(gfiber(Q,K) for Q in (U,V))
        Q=trim([K(z.v) for z in Q0]) if Q0 is not None else []
        W=next((x for x,n in ((Q,len(Q0) if Q0 else -1),(A,34),(B,44)) if x and len(x)==n),None)
        if W is None:
            bad.append((md,e,'s_leading',len(A)-1,len(B)-1));continue
        S=W
        for x in (A,B,Q):S=gcdp(S,x)
        assert S
        if len(S)==1:
            out['no_s']+=1;continue
        for T,r in sfactors(S,K):
            try:k,info=use_s(K,g,T,p,t,mode)
            except (ArithmeticError,AssertionError,ValueError,ZeroDivisionError) as err:k,info='arithmetic_fail',str(err)
            if k in ('no_gap','no_true_fifth'):out[k]+=1
            else:
                names=('g','La','Lb','anchor','s_eq_a','s_eq_b','x_a','x_b','x_q','quintic','terminal_h')
                tests={i:j for i,h in zip(names,gd) if (j:=len(gcdp(T,sv(h,K,g,p,t)))-1)}
                bad.append((md,e,len(T)-1,k,info,tests))
        if verbose:
            print('stage4 full residue',mode,md,e,dict(out),'bad-last',bad[-1:],flush=True)
    assert d0==R
    return out,bad
