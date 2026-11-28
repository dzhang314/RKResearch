#!/usr/bin/env python3
"""Replay all characteristic-zero eliminations; see README.md for the actual-tree bridge."""
from argparse import ArgumentParser
from pathlib import Path
from runpy import run_path
from fractions import Fraction as Q
from math import comb
import sympy as S

HERE=Path(__file__).resolve().parent
cli=ArgumentParser()
cli.add_argument("--arithmetic",type=Path,default=HERE.parent/"dirk11-thirteen-invisible-six-constant-exclusion/replay.py")
args=cli.parse_args()
D=run_path(str(args.arithmetic))
Ring,quot,det=D['Ring'],D['quot'],D['det']
j4,j5=D['J4'],D['J5']
P=run_path(str(HERE/'project.py'))
s,p=P['s'],P['p']
Fpair,Gpair=P['Fpair'],P['projected'].as_expr()
AF,BF=[[u.a.as_expr() for u in P[key]] for key in ('AF','ghost')]
factors={S.degree(f,s):f for f,m in P['sfactors']}
assert S.degree(Gpair,p)==3 and len(AF)==4 and len(BF)==3
PRIME=101
Hcoeff=(1,-14,56,-84,42)

def ringpoly(R):
    def trim(x):
        x=list(x)
        while len(x)>1 and x[-1]==0:x.pop()
        return x
    def add(a,b):
        return trim([(a[i] if i<len(a) else R.to(0))+(b[i] if i<len(b) else R.to(0))
            for i in range(max(len(a),len(b)))])
    def scale(a,s):return trim([r*s for r in a])
    def mul(a,b):
        out=[R.to(0)]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):out[i+j]+=x*y
        return trim(out)
    def div(a,b):
        assert b[-1]==1
        a=list(a);n=len(b)-1;m=len(a)-n;Q=[R.to(0)]*max(1,m)
        for i in range(m-1,-1,-1):
            Q[i]=a[n+i]
            for j in range(n):a[i+j]-=Q[i]*b[j]
        return trim(Q),trim(a[:n] or [R.to(0)])
    def ev(pol,X):
        a=X.r.to(0)
        for p in reversed(pol):a=a*X+X.r.to(p)
        return a
    def prim(a):return [R.to(0),*(x/(j+1)for j,x in enumerate(a))]
    return add,scale,mul,div,ev,prim

def ghost_sylv(R,old,rho):
    add,scale,mul,div,ev,prim=ringpoly(R)
    W=Ring("old reflected triple",R,old[:-1]); Y=W.gen()
    m=j4(Y)/(1-W.to(rho)-Y)
    pm=[R.to(0),*m.v];pmy=[R.to(0),*(Y*m).v]
    IP=ev(pm,Y)
    r=(ev(prim(pm),Y)/IP).v
    rr=(ev(prim(pmy),Y)/IP).v
    u=(ev(prim([R.to(0),*old]),Y)/IP).v
    a,b,c=u[2],u[1],u[0]
    d,e,f=rr[2]-r[1],rr[1]-r[0],rr[0]
    sylv=(a*f-c*d)**2-(a*e-b*d)*(b*f-c*e)
    return sylv,r[2],(u,rr,r)

def rat(c):
    n,d=S.Rational(c).as_numer_denom()
    return Q(int(n),int(d))
def coefficients(P,base,dim):
    return [base.to(rat(P.nth(i)))for i in range(dim)]
def symp_reduced_coeffs(q,ss,degree):
    Sfield=S.Poly(q,p)
    return [eval_f(Sfield.nth(i),ss)for i in range(degree+1)]
def eval_f(q,ss):
    acc=ss.r.to(0)
    for c in S.Poly(q,s).all_coeffs():acc=acc*ss+rat(c)
    return acc
def eval_sym(q,ss,pp):
    ac=pp.r.to(0)
    for c in S.Poly(q,p).all_coeffs():ac=ac*pp+eval_f(c,ss)
    return ac
def lin(F,G):
    assert len(F)>2 and len(G)>2
    R=F[0].r;z=R.to(0)
    m,n=len(F)-1,len(G)-1
    M=[i*[z]+F[::-1]+(n-2-i)*[z]for i in range(n-1)]+[i*[z]+G[::-1]+(m-2-i)*[z]for i in range(m-1)]
    cs=[]
    for j in range(2):
        B=[row[:-2]+[row[-1-j]]for row in M]
        cs.append(det(B))
    return cs
def reflection(pol):
    n=len(pol)-1
    return [sum(((-1)**(n+j))*comb(k,j)*pol[k] for k in range(j,n+1))for j in range(n+1)]

def test_alpha(W,ss,pp,rho):
    B=Ring("ordered a",W,[pp,-ss]); a=B.gen();b=B.to(ss)-a;r=B.to(rho)
    add,scale,mul,div,ev,prim=ringpoly(B)
    H=[B.to(0),*(B.to(i)for i in (1,-14,56,-84,42))]
    F=prim(mul([B.to(0),B.to(1)],mul([-b,B.to(1)],[-r,B.to(1)])))
    rh=ev(F,b)/ev(H,b)
    da=(ev(F,a)-rh*ev(H,a))/(a*(a-b)*(a-r))
    lam=-j5(b)/j4(b);J4=[1,-14,56,-84,42,0];J5=[-1,20,-120,300,-330,132]
    T5=[(B.to(x)+lam*y)/132 for x,y in zip(J5,J4)]
    S6=[B.to(0),*T5]
    old=reflection(quot(quot(T5,b),a))
    G,aff,vals=ghost_sylv(B,old,r)
    w,e,c=vals          # W quadratic, r1, r0
    # The two gap ghosts live. α=1 exact pole location tested without
    # dividing by its scalar stage.
    vr=ev(F,r)-rh*ev(H,r)
    num=(1-r)*vr-42*rh*ev(S6,r)
    hyp=lambda p:sum(x*num**i*vr**(2-i)for i,x in enumerate(p))
    gap=[e[0],e[1]-c[0],e[2]-c[1]]
    t1,t2=hyp(w),hyp(gap)
    # α=2: paid grade-six primitive and commutator projections.
    A=1-a
    def scaled_remainder(f,p):
        z=list(f)
        while len(z)>2:
            lead=z[-1];d=len(z)-len(p)
            z=[p[-1]*u for u in z]
            for i,q in enumerate(p):z[i+d]-=lead*q
            assert z[-1]==0
            z=z[:-1]
        return z+[B.to(0)]*(2-len(z))
    P0=[B.to(0),*old]
    IYP=prim([B.to(0),*P0])
    W0=Ring("old triple",B,old[:-1]); Y=W0.gen()
    k=lambda x:x*j4(x)/(1-x-x.r.to(r))
    cand=(ev(IYP,Y)/k(Y)).v
    q4=(ev(IYP,A)-A*da*ev(P0,A))/k(A)
    Q=add(cand,scale(old,(q4-ev(cand,A))/ev(old,A)))
    s0,s1=scaled_remainder(Q,w)
    s2,s3=scaled_remainder(old,w)
    d0=s0+s1*(1-r)
    d1=da**2*(s2+s3*(1-r))
    print("Residual zero flags, alpha1 then alpha2",[[x==0 for x in zs]for zs in ((t1,t2),(d0,d1))],flush=True)
    for j,(f,g) in enumerate([(t1,t2),(d0,d1)]):
        (f+2*g).inv()
        print("alpha",j+1,"excluded by unit",flush=True)

def Ppoles(T,ss,pp):
    add,scale,mul,div,ev,prim=ringpoly(T)
    q2=[pp,-ss,T.to(1)]
    H4=[T.to(x)for x in Hcoeff]
    J5=[T.to(x)for x in (-1,20,-120,300,-330,132)]
    HH=[T.to(0),*H4]
    def pad(p,n):return p+[T.to(0)]*(n-len(p))
    def rm(a):return div(a,q2)[1]
    def invpair(v):
        a,b=pad(rm(v),2)
        f=(a*a+a*b*ss+b*b*pp).inv()
        return [(a+b*ss)*f,-b*f]
    lr=scale(rm(mul(J5,invpair(H4))),-1)
    assert len(lr)==1
    lam=lr[0]
    T5=scale(add(J5,scale(H4,lam)),Q(1,132))
    old,zero=div(T5,q2); assert zero==[T.to(0)]
    Hinv=invpair(HH)
    F0=prim([T.to(0),T.to(0),pp,-ss,T.to(1)])
    F1=scale(prim([T.to(0),pp,-ss,T.to(1)]),-1)
    L0=pad(rm(mul(F0,Hinv)),2);L1=pad(rm(mul(F1,Hinv)),2)
    E=add(F0,[T.to(0),*F1])
    E=add(E,scale(mul(HH,[L0[0],L0[1]+L1[0],L1[1]]),-1))
    E=add(E,scale(mul([L0[1],L1[1]],[T.to(0),*T5]),42))
    A,Z=div(E,[T.to(0),*q2]); assert Z==[T.to(0)]
    return A,reflection(old)

def guard(prime,which):
    ff={'den':P['EJ'],'orig':P['EH'],'lead':P['LEAD12']}[which]
    S0=S.Poly(ff,s,domain=S.QQ).monic()
    K=S.QQ.algebraic_field((S0,s))
    def NP(f):
        z=S.Poly(f,p)
        def kt(x):
            v=S.Poly(x,s,domain=S.QQ).rem(S0)
            return K([S.QQ.from_sympy(c)for c in v.all_coeffs()])
        return S.Poly.from_list([kt(c)for c in z.all_coeffs()],p,domain=K)
    PF=NP(Fpair).monic();H0=NP(P['guardH'].a.as_expr())
    cut=[]
    while True:
        G=S.gcd(PF,H0).monic()
        if G.degree()==0:break
        cut.append(G.degree())
        PF=PF.exquo(G).monic()
    assert cut==([1] if which in ('den','orig') else [])
    print("guard",which,"remove only dead H pair factors",cut,flush=True)
    if which=="lead":
        L=NP(AF[-1])
        g=S.gcd(PF,L).monic(); PF=PF.exquo(g).monic()
        assert g.degree()==1 and PF.degree()==3
        pieces=[(g,2,"leading drop"),(PF,3,"regular lead")]
    else:
        assert PF.degree()==3
        pieces=[(PF,3,"valid H pairs")]
    for piece,deg,label in pieces:
        if piece.degree()==0:continue
        P0=Ring('prime',prime=prime)
        B=Ring('guard sum',P0,coefficients(S0,P0,S0.degree())); sb=B.gen()
        Cs=[eval_f(piece.nth(i),sb)for i in range(piece.degree())]
        if len(Cs)==1: T=B;pp=-Cs[0];ss=sb
        else: T=Ring('remaining pair products',B,Cs);pp=T.gen();ss=T.to(sb)
        print(label,'pair degree',piece.degree(),flush=True)
        F,rr=Ppoles(T,ss,pp)
        print('rho cubic degree observed',len(F)-1,flush=True)
        # Degree chosen from the exact pair chart, never from residue alone.
        assert len(F)==deg+1
        q0=F[-1].inv()
        U=Ring('carrier pole',T,[f*q0 for f in F[:-1]])
        rh=U.gen()
        sU,pU=U.to(ss),U.to(pp)
        G,A,_=ghost_sylv(U,[U.to(x)for x in rr],rh)
        G.inv()
        print("First ghost exclusion for all gap shapes:",label,flush=True)

def exact6():
    fr=S.Poly(factors[6],s,domain=S.QQ).monic()
    assert fr.is_irreducible
    K=S.QQ.algebraic_field((fr,s))
    def kb(e):
        z=S.Poly(e,s,domain=S.QQ).rem(fr)
        return K([S.QQ.from_sympy(a)for a in z.all_coeffs()])
    def ps(e,dim):
        f=S.Poly(e,p)
        return [kb(f.nth(i))for i in range(dim+1)]
    def Mdet(m):
        if len(m)==1:return m[0][0]
        q=K.zero
        for i,x in enumerate(m[0]):
            if x!=K.zero:q+=(-1)**i*x*Mdet([[w for j,w in enumerate(row)if j!=i]for row in m[1:]])
        return q
    def linear(f,g):
        m,n=len(f)-1,len(g)-1
        z=K.zero
        M=[i*[z]+f[::-1]+(n-2-i)*[z]for i in range(n-1)]+[i*[z]+g[::-1]+(m-2-i)*[z]for i in range(m-1)]
        return [Mdet([c[:-2]+[c[-1-j]]for c in M]) for j in range(2)]
    a0,a1=linear(ps(Fpair,4),ps(Gpair,3))
    assert a1!=K.zero
    print("exact p pivot of degree 6",flush=True)
    def hom(f,dim,x,y):
        z=K.zero
        for j,a in enumerate(ps(f,dim)): z+=a*x**j*y**(dim-j)
        return z
    E=P['E'];Jshift=[k-l for k,l in zip(P['j5'],P['j4']+[E(0)])]
    left=P['rem'](Jshift,P['uv'])
    assert all(S.Poly(co.a.as_expr(),p).degree()<=3 for co in left)
    image=[hom(co.a.as_expr(),3,-a0,a1)for co in left]
    print("exact pair J5-J4 zero flags",[v==K.zero for v in image],flush=True)
    assert all(x==K.zero for x in image)
    print("Degree six: lambda=-1 forces forbidden interior clock 1",flush=True)

def sumone(prime):
    # Exact formula for s=1 is also audited by specialization over Q.
    R=Ring('prime',prime=prime)
    i66=R.to(66).inv()
    B=Ring('symmetric clean product',R,[i66,-18*i66]); pb=B.gen()
    uq=[pb-Q(41,231),5*pb/7+Q(142,231),-4*pb/7-Q(106,77)]
    T=Ring('carrier pole at s=1',B,uq); rr=T.gen();ss=T.to(1);pp=T.to(pb)
    add,scale,mul,div,ev,prim=ringpoly(T)
    clean=[T.to(Q(j,132))for j in (-1,20,-120,300,-330,132)]
    old,zero=div(clean,[pp,-ss,T.to(1)])
    assert zero==[T.to(0)]
    old=reflection(old)
    G,_,_=ghost_sylv(T,old,rr)
    G.inv()
    print("s=1 unit",flush=True)

def reconstruct(degree):
    FF=Ring("finite residue",prime=PRIME); sf=S.Poly(factors[degree],s,domain=S.QQ).monic()
    K=Ring("sum clock",FF,coefficients(sf,FF,degree));ss=K.gen()
    pr=lin(symp_reduced_coeffs(Fpair,ss,4),symp_reduced_coeffs(Gpair,ss,3))
    pp=-pr[0]/pr[1]
    A=[eval_sym(f,ss,pp) for f in AF];B=[eval_sym(f,ss,pp) for f in BF]
    ru=lin(A,B)
    rho=-ru[0]/ru[1]
    print("degree",degree,": p and rho leading pivots are units",flush=True)
    if degree==42:
        test_alpha(K,ss,pp,rho)

exact6()
reconstruct(30)
reconstruct(42)
sumone(PRIME)
for chart in ('den','orig','lead'):
    guard(PRIME,chart)
print("All linear-profile branches excluded (exact project + characteristic-zero clock-algebra unit lifts).",flush=True)
