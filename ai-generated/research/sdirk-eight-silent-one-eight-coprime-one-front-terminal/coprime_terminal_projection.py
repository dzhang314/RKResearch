"""Literal profile of one-active-front coprime branch, with actual Gaussian terminal."""
from shared_one_front_projection import *
from shared_one_front_models import trim

def L(X):return can(sum(x*X**j for j,x in enumerate(LM)))

def coF(P,iv):
    cs=[]
    for f in co(P,iv):
        h=gco(plug(f,2,1-r))
        assert len(h)<=1
        cs.append(h[0] if h else F(0))
    return trim(cs)

@lru_cache(None)
def setup(front,slot):
    A,B,m=map(lambda w:cv(F2,w),ends(front,1))
    ha,hb=(A-1)/2,(B-1-m)/2
    active,quiet,H=(A,B,ha) if slot==0 else (B,A,hb)
    al,bl,af=map(expr,(A,B,active))
    H4=[cv(F2,v) for v in pol(h4(front),lambda z:z)]
    S0,_,S1,QT,QA=context(F2,A,B,m,ha,hb,None,H4)
    hs=term(H4,s)
    diag=1-r
    La,Ls=L(diag*af),L(diag*s)
    q0=can(s*hs*La-af*expr(H)*Ls)
    q1=can(expr(H)*Ls-hs*La)
    Q=can(q0+q1*y)
    N0=can(expr(H)*(s-af)*L(diag*y))  # common H4 canceled from E_T, E_A
    m0=s-1-2*hs;m1=s*s/2-s-2*hs
    aa=(bl*m0-m1)*expr((B-A).inv());bb=m0-aa
    rowT=can(s**3-s**4/4+2*hs+aa*al**3+bb*bl**3)
    rowA=can(hs+aa*expr(ha)+bb*expr(hb))
    def cfield(poly):
        z=[]
        for f in co(poly,1):
            pairs={}
            for (iy,is0,ig,ir,it),w in f.to_dict().items():
                assert iy==is0==ig==ir==0
                pairs[it]=w
            from check_star_family import E as QqE
            z.append(F2(QqE(FlP([pairs.get(0,0)]),FlP([pairs.get(1,0)]))))
        return z
    assert len(gcdp(H4,cfield(rowA)))==1
    qt,qa=ev(QT,active),ev(QA,active)
    Xt,rem=exdiv(can(rowT-expr(qt)*hs),s-af);assert not rem
    Xa,rem=exdiv(can(rowA-expr(qa)*hs),s-af);assert not rem
    M0=y-1;M1=y*y/2-y;M2=y**3/3-y*y
    J0=M2-(al+bl)*M1+al*bl*M0
    T0=can(y**3-y**4/4+(al+bl)*M2-al*bl*M1+s*J0)
    A0=can(expr(S0[0])*M0+expr(S0[1])*M1+term(S1,s)*J0)
    j=-F2(4)/3+2*(A+B)-2*A*B
    DT=term([2-F2(4)/3*(A+B)+2*A*B,j],s)
    DA=expr(1-2*S0[0]-2*S0[1])+term(S1,s)*expr(j)
    T1=can(hs*(DT-expr(qt))-Xt*(y-af))
    A1=can(hs*(DA-expr(qa))-Xa*(y-af))
    Et=can(T0*Q+T1*N0);Ea=can(A0*Q+A1*N0)
    Et,b=exdiv(Et,(y-af)*(y-s));assert not b
    Ea,b=exdiv(Ea,(y-af)*(y-s));assert not b
    assert Et.degrees()[0]==Ea.degrees()[0]==3
    q=lambda X:can(diag*q0+q1*X)
    dres=can(sum(c*(-diag*q0)**i*q1**(4-i) for i,c in enumerate(LM)))
    cond=[can(hs*(s-al)*(s-bl)),q1,dres,Ls]
    u=y;k=1+2*u-u*u;Hh=-2+u+4*u*u-u**3;Jj=2+3*u-12*u*u+4*u**3
    x=r;c=r-diag*u;d1=r-diag*(2-u);d2=r-2*diag*u
    F1=can((2-u)*L(c)*q(d1)-u*L(d1)*q(c))
    F2a=can(Hh*L(d2)*q(c)+2*Jj*L(c)*q(d2))
    F1,b=exdiv(F1,u*(u-1)*(u-2));assert not b
    F2a,b=exdiv(F2a,u*u);assert not b
    assert F1.degrees()[0]==2 and F2a.degrees()[0]==5
    W=can(Et.resultant(Ea,0))
    W0=coF(W,1);C0=coF(La,1)
    assert W0 and len(C0)==1 and C0[0].inv()
    G=mon(guarded(W0,[coF(c,1) for c in cond]))
    assert len(W0)==22 and len(G)==8
    assert len(gcdp(G,coF(co(F1,0)[-1],1)))==len(gcdp(G,coF(co(F2a,0)[-1],1)))==1
    print('coprime Gaussian terminal exact s projection',front,slot,len(W0)-1,len(G)-1,
          'star gap leading',len(gcdp(G,coF(co(F1,0)[-1],1)))-1,
          'arith gap leading',len(gcdp(G,coF(co(F2a,0)[-1],1)))-1,flush=True)
    return G,Et,Ea,F1,F2a,(q0,q1,La,Ls,cond,A,B,m,active,H,H4)
