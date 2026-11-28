"""First literal fifth characterization for a constant denominator with single live front."""
from off_literal_projection import *

def profile(f,slot,rear=None,ori=1):
    A,B,m=map(lambda q:cv(F2,q),ends(f,1))
    ha,hb=(A-1)/2,(B-1-m)/2
    anc,off,hh=(A,B,ha) if slot==0 else (B,A,hb)
    L4=lambda X:sum(p*X**j for j,p in enumerate(Lco))
    qf=can(L4(g*expr(anc)))
    return A,B,m,ha,hb,anc,off,hh,qf,can(expr(hh)*L4(g*y))

@lru_cache(None)
def literal_eqs(f,slot):
 A,B,m,ha,hb,anc,off,hh,Qp,Pn=profile(f,slot)
 F=F2;al,bl,af=map(expr,(A,B,anc))
 H4=list(map(lambda u:cv(F,u),pol(h4(f),lambda z:z)))
 L0,AA,e,QT,QA=context(F,A,B,m,ha,hb,None,H4)
 tv,av=ev(QT,anc),ev(QA,anc)
 Hs=term(H4,s)
 s0=s-1-2*Hs;s1=s*s/2-s-2*Hs
 ta=(bl*s0-s1)*expr((B-A).inv());tb=s0-ta
 row_T=can(s**3-s**4/4+2*Hs+ta*al**3+tb*bl**3)
 row_A=can(Hs+ta*expr(ha)+tb*expr(hb))
 assert len(gcdp(H4,[v for j,v in enumerate(exact_sc(row_A,1))]))==1
 XT,rr=exdiv(can(row_T-expr(tv)*Hs),s-af);assert not rr
 XA,rr=exdiv(can(row_A-expr(av)*Hs),s-af);assert not rr
 m0=y-1;m1=y*y/2-y;m2=y**3/3-y*y
 J0=m2-(al+bl)*m1+al*bl*m0
 T0=y**3-y**4/4+(al+bl)*m2-al*bl*m1+s*J0
 A0=expr(L0[0])*m0+expr(L0[1])*m1+term(e,s)*J0
 JH=-F(4)/3+2*(A+B)-2*A*B
 DT=term([2-F(4)/3*(A+B)+2*A*B,JH],s)
 DA=expr(1-2*L0[0]-2*L0[1])+term(e,s)*expr(JH)
 T1=can(Hs*(DT-expr(tv))-XT*(y-af))
 A1=can(Hs*(DA-expr(av))-XA*(y-af))
 Et=can(Hs*T0*Qp+T1*Pn);Ea=can(Hs*A0*Qp+A1*Pn)
 Et,rr=exdiv(Et,y-af);assert not rr
 Ea,rr=exdiv(Ea,y-af);assert not rr
 Phi,R=exdiv(can(ats(Qp)*Hs-ats(Pn)),s-af);assert not R
 A,C0=exdiv(Et,y-s);B,C1=exdiv(Ea,y-s)
 assert not can(C0-ats(T0)*Phi) and not can(C1-ats(A0)*Phi)
 return Phi,A,B,Et,Ea,T0,A0,T1,A1,H4


def cert(f,slot):
    Phi,T0,A0,*_=literal_eqs(f,slot)
    print('one front constant literal systems',f,slot,Phi.degrees(),T0.degrees(),A0.degrees(),flush=True)
    D=can(T0.resultant(A0,0))
    anc,off=profile(f,slot)[5:7]
    for a in (anc,off):
        while True:
            q,r=exdiv(D,s-expr(a))
            if r:break
            D=q
    print('first literal y elimination',f,slot,D.degrees(),flush=True)
    R=can(Phi.resultant(D,1))
    assert R
    G=exact_g(R)
    B=exact_g(profile(f,slot)[8])
    X=mon(guarded(G,[[F2(0),F2(1)],B]))
    assert (len(G)-1,len(X)-1)==(180,100)
    print('joint exact physical diagonal degree',f,slot,len(G)-1,len(X)-1,flush=True)
    return X,Phi,D,T0,A0
