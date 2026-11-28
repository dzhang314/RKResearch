"""Two exact homogeneous six-peg cuts for a truly ordinary arithmetic rear."""
from functools import lru_cache
from h5_star_branches import L,SC,specialize,main_front
from h5_regular_projection import model,gpoly
from h54_arithmetic_projection import exact_tail,remove_in_cubic,Yrem
from h567_star_projection import sig_mom
from aq_rear import u as Y,s as U,g,red,ev,divide
from regular_star_projection import Co,remove,nodal,mul
from hole4_projection import crt
from aq5_projection import flip

def combine(*L):
    return [red(sum(Q[i] for Q in L if i<len(Q))) for i in range(max(map(len,L)))]

def sc(a,P):
    return [red(a*q) for q in P]

def remove_common(P,guards):
    P=list(P)
    out=[]
    for q in guards:
        g0=min(remove(v,(q,))[1][0] for v in P if v)
        if g0:P=[divide(v,q**g0) if v else v for v in P]
        out.append(g0)
    return P,out

@lru_cache(None)
def signed_model():
    H,D,A,B,J,Z0,gs,dat=model(True)
    a,b,r,x=dat[-4:]
    F,_,_,(c,d,k)=exact_tail()
    E5=nodal([a,b,x,c,d])
    hr=ev(H,r)
    assert hr==g*gs[4]
    nu4,nu5=(sig_mom(H,i,hr,B,r) for i in (4,5))
    assert all(not sig_mom(H,i,hr,B,r) for i in range(4))
    h3,h4=H[-2:]
    im=[sig_mom(E5,i,hr,B,r) for i in range(5)]
    m0,m1,m2,m3=[[im[i+1],red(-g*im[i])] for i in range(4)]
    e5=[E5[-2],-g]
    C=combine(sc(h4,mul(m0,m2)),sc(-h4,mul(m1,m1)),sc(-nu4,m0))
    D=combine(sc(h4*nu4,mul(e5,m0)),sc(h4*nu5-h3*nu4,m0),sc(-h4*nu4,m1),sc(-h4*h4,mul(m0,m3)),
              sc(h4*h4,mul(m1,m2)))
    C0,ce=remove_common(C,gs)
    D0,de=remove_common(D,gs)
    assert ce==de==[2,0,0,0,1,0,0,0]
    assert len(C0)==len(D0)==3
    assert [q.degrees()[1] for q in C0+D0]==[4]*6
    print('arith early s signed coefficients',ce,de,[[p.degrees() for p in Q] for Q in (C0,D0)],flush=True)
    return C0,D0,F,gs

def res22(P,Q):
    p0,p1,p2=P
    q0,q1,q2=Q
    return red((p2*q0-p0*q2)**2-(p2*q1-p1*q2)*(p1*q0-p0*q1))

@lru_cache(None)
def project(cubic,second=False):
    H,D,A,B,J,Z0,gs,dat=model(True)
    C0,D0,F,_=signed_model()
    T=D0 if second else C0
    if cubic:
        P=SC
        F=Yrem(F)
        raw=Yrem(res22(list(map(Yrem,Co(J,1))),list(map(Yrem,T))))
    else:
        P=main_front()
        raw=red(ev(T,(2*Y+1)/3))
    V,e0=remove(raw,gs)
    Q=flip(crt(flip(F),flip(V),'arithmetic six-peg true gap'))
    if cubic:Q=Yrem(Q)
    Q0,qe=remove(Q,gs)
    if cubic:
        Q0,pa=remove_in_cubic(Q0,A)
        Q0,ph=remove_in_cubic(Q0,gs[4])
        assert raw.degrees()==((2,8,86,0) if second else (2,8,74,0))
        assert e0==[4,0,0,0,0,0,0,0] and qe==[16,0,0,0,0,0,0,0]
        assert Q.degrees()==((2,0,490,0) if second else (2,0,430,0))
        assert Q0.degrees()==((2,0,375,0) if second else (2,0,327,0))
        assert (pa,ph)==((9,5) if second else (7,5))
    else:
        pa=ph=0
        assert e0==[0,0,0,0,0,0,0,0] and qe==[8,0,2,0,0,0,0,0]
        assert Q.degrees()==((87,0,205,1) if second else (72,0,175,0))
        assert Q0.degrees()==((81,0,185,1) if second else (66,0,155,0))
    print('arith six-peg gap projection',cubic,second,'raw gate',raw.degrees(),V.degrees(),e0,'Q exact',Q.degrees(),'Q guards',Q0.degrees(),qe,pa,ph,flush=True)
    R=crt(P,Q0,'arithmetic six-peg true diagonal')
    R0,e=remove(R,tuple(v for v in gs if v.degrees()[0]==0))
    T,d=remove(R0,(L,))
    print('arith six-peg outer projection',cubic,second,'exact',R.degrees(),'guarded',R0.degrees(),e,'non L',T.degrees(),d,flush=True)
    if cubic:
        assert R.degrees()[2]==R0.degrees()[2]==(1125 if second else 981)
        assert e==[0,0,0,0] and d==[0]
        return ((gpoly(R0).monic(),P,Q0,'usual'),)
    assert (R.degrees()[2],R0.degrees()[2],T.degrees()[2])==((1420,912,897) if second else (1195,807,792))
    assert e==([304,51,0,0] if second else [244,36,0,0]) and d==[5]
    PL,QL=specialize(P),specialize(Q0)
    assert PL.degrees()==(4,0,2,1) and QL.degrees()==((76,0,2,1) if second else (61,0,2,0))
    print('arith six-peg specialized polynomials',PL.degrees(),QL.degrees(),flush=True)
    return ((gpoly(T).monic(),P,Q0,'usual'),(gpoly(L).monic(),PL,QL,'degenerate'))
