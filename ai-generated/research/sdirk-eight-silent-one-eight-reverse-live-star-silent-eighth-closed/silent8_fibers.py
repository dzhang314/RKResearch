"""Full fourth, penultimate, fifth, and last ordinary quadratic fibres."""
from functools import lru_cache
from collections import Counter
from math import comb
from flint import fq_default_ctx,fq_default_poly_ctx,fmpz_mod_poly_ctx
from star4_actual_fifth import Bfield,nmod_poly,gcdp,sc,trim,lv,pe,mul
from star4_guarded_fibers import modQ,modcoef,Field,gpoly
from silent8_diag import get_inputs
from silent8_star_fifth import Co,red,model,literal_fifth_poly
from ordinary_reconstruction import divide_root,extend,reject_chronology

def gfiber(F,K,x):
    r={}
    for (j,i),v in F.to_dict().items():
        r[i]=r.get(i,K(0))+K(int(v)%K.p)*x**j
    return trim([r.get(i,K(0)) for i in range(max(r,default=-1)+1)])

def sfactors(S,K):
    if len(S)<=2:
        return [(S,1)]
    S=sc(S,S[-1].inv())
    G=fq_default_ctx(modulus=fmpz_mod_poly_ctx(K.p)([int(c) for c in K.M]),fq_type="FQ_NMOD")
    R=fq_default_poly_ctx(G)
    A=R([G([int(c) for c in v.x]) for v in S])
    _,FF=A.factor()
    out=[]
    for f,e in FF:
        W=[K(nmod_poly([int(c) for c in u.to_list()],K.p)) for u in f]
        out.append((W,e))
    T=[K(1)]
    for f,e in out:
        for _ in range(e):T=mul(T,f)
    assert T==S
    return out

def getpoly(F,U,x,y,p,t):
    S=Co(F,0)
    return trim([lv(z,U,x,y,p,t) for z in S])

def reverse_arg(f,x,g,K):
    out=[K(0)]*len(f)
    for j,c in enumerate(f):
        for i in range(j+1):
            out[i]+=c*comb(j,i)*(x/g)**(j-i)*(-1)**i
    return trim(out)

@lru_cache(None)
def true_guards():
    D1,F,N,H,delta,dat=model()
    a,b,q,La,Lb,A0,B0,x=dat
    gguard=red(La*Lb*(x-a)*(x-b))
    ng=Co(N,0)[-1]
    return gpoly(gguard),tuple(gpoly(r) for r in Co(ng,1)),ng

def one_s(K,gs,S,p,t):
    _,F,N,H,delta,dat=model()
    _,G,_=literal_fifth_poly()
    A,B=(dat[5],dat[6])
    U,s,E=extend(K,S);g=E(gs);x=1-g
    gs0,s0=g,s
    f,n,h = map(lambda a:getpoly(a,U,g,s,p,t),(F,N,G))
    assert len(n)<=5
    if len(n)!=5:
        return 'nodal_leading',None
    n=sc(n,n[-1].inv())
    r=reverse_arg(h,x,g,U)
    q=gcdp(n,f)
    assert q
    if len(q)==1:
        return 'no_penultimate',None
    V,u,E0=extend(U,q)
    n=divide_root(list(map(E0,n)),u,V)
    j=gcdp(n,list(map(E0,r)))
    assert j
    if len(j)==1:
        return 'no_distinct_fifth',None
    W,y,E1=extend(V,j)
    n=divide_root(list(map(E1,n)),y,W)
    assert len(n)==3
    X,r0,E2=extend(W,n)
    key=lambda v:E2(E1(E0(v)))
    g=key(g);s=key(s);u=E2(E1(u));y=E2(y)
    g.inv()
    k=1+2*u-u*u
    xx=1/g-1
    zz=xx+k*(u-2)/2
    r1=-E2(n[1])-r0
    Aa,Bb,dd=[key(lv(p0,U,gs0,s0,p,t)) for p0 in (A,B,delta)]
    # Work with actual H physical, not a virtual ordinary amplitude at z.
    hs=[key(lv(a,U,gs0,s0,p,t))/dd for a in H]
    Y=[X(1),Aa,Bb,s,xx-y,xx-r0,xx-r1,zz,xx-u,xx]
    HH=[X(0)]+[pe(hs,g*c) for c in Y[1:]]
    reject_chronology(X,Y,HH,g,k)
    return 'actual_chronology',None

def all_mod(M,e,L,p,t,guard_fiber=None,verbose=False):
    R,JJ=get_inputs();J=JJ[L]
    FF=modQ(M,p); assert FF.degree()==M.degree() and FF.leading_coefficient()==1
    tracks=[];failure=[]
    for P,m in FF.factor()[1]:
        K=Bfield(P,p,t);gg=K(nmod_poly([0,1],p));A=gfiber(R,K,gg);B=gfiber(J,K,gg)
        if guard_fiber is None:
            if len(A)!=33 and len(B)!=L+1:
                failure.append((P.degree(),'fourth_leading',len(A)-1,len(B)-1));continue
            S=A if len(A)==33 else B
        else:
            S=[modcoef(v,K,gg,p) for v in guard_fiber]
            assert S and S[-1]==1
        S=gcdp(gcdp(S,A),B)
        assert S
        if len(S)==1:
            tracks.append('no_s')
            continue
        for T,k in sfactors(S,K):
            try:r,w=one_s(K,gg,T,p,t)
            except (ArithmeticError,ValueError,ZeroDivisionError) as exc:
                r,w='residue_model_fail',str(exc)
            if r in ('nodal_leading','residue_model_fail'):failure.append((P.degree(),len(T)-1,r,w))
            else:tracks.append(r)
            if verbose:print('    s unit',P.degree(),len(T)-1,r,w,flush=True)
    print('whole gamma diagonal',L,M.degree(),e,p,dict(Counter(tracks)),'open',failure,flush=True)
    return not failure,tracks,failure
