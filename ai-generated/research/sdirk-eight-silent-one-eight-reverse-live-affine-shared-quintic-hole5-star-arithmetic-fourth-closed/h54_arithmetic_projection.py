"""Exact constraints for regular star-front, arithmetic-rear, actually silent fourth."""
from functools import lru_cache
from h5_star_branches import L,SC,main_front
from h5_regular_projection import model,gpoly
from aq_rear import u as Y,s as S,g,red,ev,divide
from regular_star_projection import Co,remove,det
from hole4_projection import crt
from aq5_projection import flip

@lru_cache(None)
def exact_tail():
    H,D,A,B,J,Z,gs,dat=model(True)
    a,b,r,x=dat[-4:]
    u=S;c=x-g*u;d=x-2*g*u;k=1+2*u-u*u
    hc,hd,hx=[ev(H,v) for v in (c,d,x)]
    G0=divide(red(x*hc-k*c*hx),u)
    G1=divide(red(g*(k*hx-hc)),u)
    Hr=-2+u+4*u*u-u**3;Jr=2+3*u-12*u*u+4*u**3
    F=divide(red(Hr*hd+2*Jr*hc-k*Jr*hx),u*u)
    return F,G0,G1,(c,d,k)

def Yrem(P):
    return red(divmod(P,SC)[1])

def remove_in_cubic(P,guard):
    """Only cancel a factor proved by an exact polynomial identity modulo SC."""
    columns=[Co(Yrem(guard*Y**j)) for j in range(3)]
    M=[[cc[i] for cc in columns] for i in range(3)]
    D=det(M);assert D and D.degrees()[0]==0
    assert P
    outs=0
    while True:
        coeff=Co(P)+[0,0,0]
        cand=[]
        try:
            for j in range(3):
                A=[[r if k!=j else coeff[i] for k,r in enumerate(row)] for i,row in enumerate(M)]
                cand.append(divide(det(A),D))
        except AssertionError:break
        Q=red(ev(cand,Y))
        assert Q and Yrem(guard*Q-P)==0
        P=Q
        outs+=1
    return P,outs

@lru_cache(None)
def project(cubic):
    H,D,A,B,J,Z,gs,dat=model(True)
    F,G0,G1,data=exact_tail()
    J0,J1,J2=Co(J,1)
    if cubic:
        F=Yrem(F)
        G=Yrem(red(J2*G0*G0-J1*G0*G1+J0*G1*G1))
    else:
        G=red(G0+(2*Y+1)/3*G1)
    Q=flip(crt(flip(F),flip(G),'actual silent fourth arithmetic rear'))
    if cubic:
        Q=Yrem(Q)
        P=SC
    else:
        P=main_front()
    Q0,qe=remove(Q,gs)
    if cubic:
        assert Q.degrees()==(2,0,220,1) and qe==[26,0,0,0,0,0,0,0]
        Q0,al=remove_in_cubic(Q0,A)
        assert Q0.degrees()==(2,0,182,1) and al==2
    else:
        assert Q.degrees()==(29,0,85,0) and Q0.degrees()==(26,0,72,1)
        assert qe==[7,0,1,0,0,0,0,0]
    if cubic:
        print('ordinary hole5 exact cubic alpha quotient',Q0.degrees(),al,flush=True)
    print('arith rear projection in Y',cubic,'inputs',F.degrees(),G.degrees(),'exact',Q.degrees(),'guards',Q0.degrees(),qe,flush=True)
    R=crt(P,Q0,'actual silent fourth arith rear diagonal')
    R0,e=remove(R,tuple(v for v in gs if v.degrees()[0]==0))
    T,de=remove(R0,(L,))
    print('arith rear diagonal',cubic,'exact',R.degrees(),'guards',R0.degrees(),e,'non L',T.degrees(),de,flush=True)
    assert de==[0]
    if cubic:
        assert R0.degrees()==R.degrees()==(0,0,546,1) and e==[0,0,0,0]
    else:
        assert R.degrees()==(0,0,510,1) and R0.degrees()==(0,0,320,0)
        assert e==[106,21,0,0]
    return ((gpoly(R0).monic(),P,Q0,'usual'),)
