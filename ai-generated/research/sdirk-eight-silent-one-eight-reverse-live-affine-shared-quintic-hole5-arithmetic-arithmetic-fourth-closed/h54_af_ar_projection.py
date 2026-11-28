"""Actual arithmetic front/rear, ordinarily silent but reverse-live physical fourth."""
from functools import lru_cache
from h5_artharth_projection import rear
from h5_arthfront_projection import model,early,gpoly,Co,remove,crt,flip
from aq_rear import s as U,g,red,ev,divide
from h54_split_outer import exact_outer,strip_univariate_guards

def norm(M):
    return M.a*M.a-M.b*M.b/2

@lru_cache(None)
def tails():
    H,D,A,B,J,Z,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    F,_,(c,d,k)=rear(2) # Only the actual z-independent ordinary arithmetic rear.
    hc,hx=[ev(H,q) for q in (c,x)]
    G0=divide(red(x*hc-k*c*hx),U)
    G1=divide(red(g*(k*hx-hc)),U)
    return F,G0,G1,(c,d,k)

@lru_cache(None)
def projection_in_Y():
    H,D,A,B,J,Z,gs,dat=model(False)
    F,G0,G1,dat=tails()
    J0,J1,J2=Co(J,1)
    C=red(J2*G0**2-J1*G0*G1+J0*G1**2)
    C0,e=remove(C,gs)
    assert (F.degrees(),G0.degrees(),G1.degrees())==((3,5,10,1),(3,3,11,1),(3,3,11,1))
    assert C.degrees()==(9,6,32,1) and C0.degrees()==(9,6,30,1)
    assert e==[2,0,0,0,0,0,0,0]
    print('actual arithmetic silent4 gap conditions',
          F.degrees(),G0.degrees(),G1.degrees(),C.degrees(),C0.degrees(),e,flush=True)
    Q=flip(crt(flip(F),flip(C0),'actual fourth arithmetic rear gap'))
    Q0,ee=remove(Q,gs)
    assert Q.degrees()==(63,0,210,1) and Q0.degrees()==(57,0,182,1)
    assert ee==[16,0,2,0,0,0,0,0]
    print('actual arithmetic silent4 gap projected',Q.degrees(),Q0.degrees(),ee,flush=True)
    return Q0

@lru_cache(None)
def project():
    H,D,A,B,J,Z,gs,dat=model(False)
    P=early();Q=projection_in_Y()
    R=exact_outer(P,Q)
    R0,e=strip_univariate_guards(R,tuple(q for q in gs if q.degrees()[0]==0))
    M=R0.monic()
    Lead=norm(gpoly(Co(P)[-1])).gcd(norm(gpoly(Co(Q)[-1])))
    common=Lead.gcd(norm(M % type(M)(Lead)))
    assert R.degrees()==(0,0,3949,1) and R0.degree()==2641
    assert e==[624,171,0,0] and common.degree()==0
    print('actual arithmetic silent4 diagonal',R.degrees(),R0.degree(),e,
          'same Y-leading norm',common.degree(),flush=True)
    return M,P,Q
