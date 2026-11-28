"""Regular actual silent eighth: independent ordinary fifth elimination."""
from regular_silent_eighth import silent8_system
from regular_star_projection import C,Z,O,g,s,t,v,red,con,Co,remove,profile,ev,det,cast
from seven_k0_anchors import cv,F2,pol,h4
from star4_actual_fifth import common_division
from functools import lru_cache
from time import perf_counter

@lru_cache(None)
def model():
    D,F,N,*_=silent8_system(True)
    H,P,V,Delta0,(a,b,q,La,Lb,A0,B0)=profile(True)
    H,H0=common_division([*H,red(Delta0*V)],[g,La,Lb]);delta=H.pop()
    assert H0==[1,1,1]
    assert all(red(h-con(h))==0 for h in [D,F,N,delta,*H])
    return D,F,N,H,delta,(a,b,q,La,Lb,A0,B0,1-g)

@lru_cache(None)
def literal_fifth_poly():
    D,F,N,H,d,(a,b,q,La,Lb,A0,B0,x)=model()
    a,b=A0,B0
    ha,hb=(a-1)/2,(b-1)/2
    h=red(sum(cast(cv(F2,w))*s**j for j,w in enumerate(pol(h4(True),lambda x:x))))
    assert not red((b-a)**2-8)
    z0=s-1-2*h;z1=s*s/2-s-2*h
    wt_a=red((b*z0-z1)*(b-a)/8);wt_b=z0-wt_a
    As=red(h+wt_a*ha+wt_b*hb)
    Ts=red(s**3-s**4/4+2*h+wt_a*a**3+wt_b*b**3)
    Ta=red(a**3-a**4/4+a-1);Tb=red(b**3-b**4/4+b-1)
    J=[[ha,a*ha,ha,Ta],[hb,b*hb,hb,Tb],[h,s*h,As,Ts]]
    cof=[(-1)**(i+3)*det([[z for j,z in enumerate(row) if i!=j] for row in J]) for i in range(4)]
    Delta=red((b-a)*(s-a)*(s-b))
    HY=ev(H,g*v)
    M0=red(d*(v-1)-2*HY)
    M1=red(d*(v*v/2-v)-2*HY)
    M2=red(d*(v**3/3-v*v)-4*HY/3)
    tap_a=red((s-b)*(b*s*M0-(b+s)*M1+M2))
    tap_b=red((a-s)*(a*s*M0-(a+s)*M1+M2))
    tap_s=red((b-a)*(a*b*M0-(a+b)*M1+M2))
    AH=red(Delta*HY+tap_a*ha+tap_b*hb+tap_s*h)
    TT=red(Delta*(d*(v**3-v**4/4)+2*HY)+tap_a*a**3+tap_b*b**3+tap_s*s**3)
    X0=red(cof[0]*Delta*HY+cof[1]*Delta*v*HY+cof[2]*AH+cof[3]*TT)
    assert X0.degrees()==(6,8,11,0)
    X,cnt=remove(X0,[v-a,v-b,v-s,g,La,Lb,(s-a)*(s-b),d])
    print('actual fifth raw/guarded',X0.degrees(),X.degrees(),cnt,flush=True)
    assert cnt==[1,1,1,2,0,0,2,0] and X.degrees()==(3,3,9,0)
    assert X==con(X) or X==-con(X)
    return X0,X,cnt

@lru_cache(None)
def N_at_fifth():
    D,F,N,H,delta,(a,b,q,La,Lb,A0,B0,x)=model()
    C0=Co(N,0)
    assert len(C0)==5
    M=red(sum(c*g**(4-i)*(x-g*v)**i for i,c in enumerate(C0)))
    P,cnt=remove(M,[g,La,Lb])
    print('actual fifth quartic raw/guarded',M.degrees(),P.degrees(),cnt,flush=True)
    assert cnt==[5,0,0] and P.degrees()==(4,8,23,0)
    return P,cnt

@lru_cache(None)
def determinant_projection():
    D,F,N,H,delta,(a,b,q,La,Lb,A0,B0,x)=model()
    _,F5,_=literal_fifth_poly()
    N5,_=N_at_fifth()
    begin=perf_counter()
    Q=red(N5.resultant(F5,0))
    assert Q and Q==con(Q)
    h5=H[-1];hx=ev(H,x);lead=Co(N,0)[-1]
    guards=[g,La,Lb,delta,(s-A0)*(s-B0),x-a,x-b,x-q,h5,hx,lead]
    J,cnt=remove(Q,guards)
    assert Q.degrees()==(0,35,105,0) and J.degrees()==(0,31,87,0)
    assert cnt==[6,0,0,0,0,0,0,0,2,0,0]
    print('independent ordinary fifth resultant',Q.degrees(),J.degrees(),cnt,round(perf_counter()-begin,3),flush=True)
    return D,J,F,N,H,delta,(a,b,q,La,Lb,A0,B0,x)
