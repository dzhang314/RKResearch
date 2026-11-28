"""Actual physical fourth silent; both earlier clocks remain ordinary pegs."""
from regular_star_projection import *
from arith4_profile import basis
from arith3_projection import fivepegs
from star4_actual_fifth import common_division
from small_crt import small_resultant
from functools import lru_cache

@lru_cache(None)
def literal4():
    H,P,V,Delta,(a,b,q,La,Lb,A0,B0)=profile(False)
    _,_,_,_,(F0,F1),cl=basis()
    assert cl[:3]==(a,b,q)
    x,c,d,k,h,j=cl[7:]
    F,fp=remove(red(V*F0+P*F1),[g,La,Lb])
    GA=red((x-q)*ev(H,c)-k*(c-q)*ev(H,x))
    G0,r=divmod(GA,v);assert not r
    G,gp=remove(red(G0),[g,La,Lb])
    assert fp==gp==[1,1,1] and F.degrees()[0]==6 and G.degrees()[0]==4
    H5,_=remove(H[-1],[g,La,Lb,V])
    V0,_=remove(V,[g,La,Lb]);Hx,_=remove(ev(H,x),[g,La,Lb,V0])
    guards=[g,La,Lb,V0,s-A0,s-B0,x-a,x-b,x-q,H5,Hx]
    E=nodal([a,b,x]);U=W(H)
    HE=mul(H,E)
    assert W(HE)==mul(E,U)
    columns=[]
    for e in range(5):
        Q=[Z]*e+E;QW=W(Q)
        columns.append([red(cof(H,QW,i)-cof(Q,U,i)) for i in range(1,5)])
    R=[(-1)**i*det([C for j,C in enumerate(columns) if i!=j]) for i in range(5)]
    R,rr=common_division(R,guards)
    Rc,Rd=ev(R,c),ev(R,d)
    T0,r=divmod(red(h*(c-q)*Rd+j*(d-q)*Rc),v);assert not r
    Cross,r=divmod(red(Rc*ev(H,d)-Rd*ev(H,c)),v);assert not r
    S,ss=remove(red(T0),guards)
    T,tt=remove(red(Cross),guards)
    N,nn=remove(fivepegs(H,(a,b,x,c,d)),guards)
    assert rr==[5,4,4,1,0,0,0,0,0,1,0]
    assert ss==[0]*11 and tt==[2,1,1,0,0,0,0,0,0,0,0]
    assert nn==[5,4,4,1,0,0,0,0,0,0,0] and N.degrees()[0]==8
    print('physical stage4 cofactor model',rr,S.degrees(),ss,T.degrees(),tt,N.degrees(),nn,flush=True)
    return F,G,S,T,N,guards,H,R,(a,b,q,x,c,d)

@lru_cache(None)
def s_projections():
    F,G,S,T,N,guards,*_=literal4()
    R=[]
    for A,B in ((F,G),(G,N)):
        P=small_resultant(A,B)
        Q,n=remove(P,guards)
        print('actual stage4 fourth input',P.degrees(),Q.degrees(),n,flush=True)
        R.append(Q)
    assert [x.degrees() for x in R]==[(0,33,96,1),(0,43,136,1)]
    return R

if __name__=='__main__':s_projections()
