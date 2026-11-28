"""Literal-silent-two true complete fourth/gap/fifth proof components."""
from arith2_outer import residue_inputs,oriented
from arith2_model import model
from arith_star_model import literal_fifth_poly
from silent8_fibers import sfactors,getpoly
from check_star_arithmetic67 import gfiber
from ordinary_reconstruction import divide_root,extend
from star4_actual_fifth import Bfield, gcdp,sc,trim,lv,pe,sv
from flint import nmod_poly
from collections import Counter
from time import perf_counter

def mono(X):
    assert X
    return sc(X,X[-1].inv())

def use_s(K,g0,T,p,t):
    F,G,P0,Cross,N,guards,H,R,dat,_=model()
    G5=literal_fifth_poly()
    U,s,inc=extend(K,T);g=inc(g0)
    Ps=[getpoly(z,U,g,s,p,t) for z in (F,G,N,P0,Cross)]
    if len(Ps[1])==5:W=Ps[1]
    elif len(Ps[0])==7:W=Ps[0]
    else:return 'raw_gap_leading',tuple(len(q)-1 for q in Ps)
    # Full basis of actual gaps; additional necessary divided cross
    # preserves both tail deletions if actual roots reduce together.
    for q in Ps:W=gcdp(W,q)
    if len(W)==1:return 'no_gap',None
    W=mono(W)
    V,u,inc0=extend(U,W);ga=inc0(g);xx=1-ga;cc=xx-ga*u;dd=xx-2*ga*u
    H0,R0=([inc0(lv(x,U,g,s,p,t)) for x in A] for A in (H,R))
    Hc,Rc=pe(H0,cc),pe(R0,cc)
    n=trim([Hc*(R0[i] if i<5 else V(0))-Rc*h for i,h in enumerate(H0)])
    if len(n)!=6:return 'actual_nodal_lead',None
    n=mono(n)
    n=divide_root(divide_root(n,cc,V),dd,V);assert len(n)==4
    gg=getpoly(G5,U,g,s,p,t);gi=ga.inv()
    GY=[inc0(z)*gi**i for i,z in enumerate(gg)]
    r=gcdp(n,GY)
    if len(r)==1:return 'no_true_fifth',None
    return 'open_true_ordinary_fifth',len(r)-1


def verify_partial(F,p,t,s_poly=None):
    A,B=residue_inputs(p,2*t)
    _,_,_,_,_,gg,*_=model()
    gn=('gamma','early_a','early_b','anchor','s_eq_a','s_eq_b',
        'x_eq_silent','x_eq_b','x_eq_q','quintic','terminal_h')
    n=0;ok=Counter();fails=[];hint=Counter()
    for M,e in F.factor()[1]:
        K=Bfield(M,p,t);gg=K(nmod_poly([0,1],p));m=M.degree()
        D,E=(gfiber(P,K) for P in (A,B))
        if len(D)!=28 and len(E)!=46:
            fails.append((m,e,'s_leading',len(D)-1,len(E)-1));continue
        S=gcdp(D,E)
        if len(S)==1:ok['no_s']+=1;continue
        for T,r in sfactors(S,K):
            try:res,other=use_s(K,gg,T,p,t)
            except (ArithmeticError,ZeroDivisionError,ValueError,AssertionError) as exc:
                res,other='arithmetic_fail',str(exc)
            if res in ('raw_gap_leading','actual_nodal_lead','arithmetic_fail','open_true_ordinary_fifth'):
                hints={}
                for k,P in zip(gn,model()[5]):
                    U=gcdp(T,sv(P,K,gg,p,t))
                    if len(U)>1:hint[k]+=len(U)-1;hints[k]=len(U)-1
                fails.append((m,e,len(T)-1,res,other,hints))
            else:ok[res]+=1
        n+=1
        print('whole gap probe gamma branch',m,e,'through',dict(ok),'open last',fails[-1:] if fails else [],flush=True)
    return ok,fails,hint

def pilot(p=65537,t=2040):
    t0=perf_counter()
    P=oriented(p,2*t)
    h=next(i for i,z in enumerate(P) if z);d=max(i for i,z in enumerate(P) if z)
    M=nmod_poly(P[h:],p)
    M=M*pow(int(M.leading_coefficient()),-1,p)
    print('oriented pilot diag shape',p,t,d,h,sorted((F.degree(),e) for F,e in M.factor()[1]),flush=True)
    K,V,H=verify_partial(M,p,t)
    print('arith literal actual silent-two p-only census',dict(K),V,dict(H),round(perf_counter()-t0,2),flush=True)

if __name__=='__main__':pilot()
