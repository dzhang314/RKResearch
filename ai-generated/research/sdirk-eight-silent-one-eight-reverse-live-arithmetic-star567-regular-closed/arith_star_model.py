"""Exact fixed-quartic reduction for arithmetic literal front, ordinary star rear."""
from regular_star_projection import *
from star4_actual_fifth import common_division
from functools import lru_cache
from time import perf_counter
from math import comb

@lru_cache(None)
def quartic_model():
    H,P,V,D,(a,b,q,La,Lb,A0,B0)=profile(False)
    H,U=common_division([*H,red(D*V)],[g,La,Lb]);delta=H.pop()
    assert U==[1,1,1]
    V0,uv=remove(V,[g,La,Lb]);assert uv==[2,0,0]
    x=1-g;m=1-2*g
    AA,BB,MO=map(lambda w:cast(cv(F2,w)),ends(False,1))
    assert AA==A0 and BB==B0
    E=nodal([a,b,q,x])
    MX=[]
    H_W=W(H)
    for j in range(5):
        Z0=mul(E,[comb(j,i)*(-m)**(j-i) for i in range(j+1)])
        ZW=W(Z0)
        MX.append([red(cof(H,ZW,i)-cof(Z0,H_W,i)) for i in range(1,5)])
    R=[(-1)**j*det([col for i,col in enumerate(MX) if i!=j]) for j in range(5)]
    assert all(R)
    guards=[g,La,Lb,V0,s-A0,s-B0,x-a,x-b,x-q,H[-1],ev(H,x)]
    R0,co=common_division(R,guards)
    assert co==[2,0,0,2,0,0,0,0,0,0,0]
    assert [r.degrees()[1:3] for r in R0]==[(8,24),(8,23),(8,22),(8,21),(7,20)]
    print('exact fixed quartic', [u.degrees() for u in R], [u.degrees() for u in R0], co,flush=True)
    c=m-g*v;d=m+g*v
    Hc,Hd,Hx=[ev(H,r) for r in (c,d,x)]
    R2,rr=divmod(red((1-v)*Hc-(1+v)*Hd+2*v*(2-v*v)*Hx),v*(v*v-1));assert not rr
    U0=centered(red(R2));assert len(U0)==2
    AB,abco=common_division(U0,guards)
    assert all(AB) and abco==[0]*11
    print('exact reduced centered tail coefficients', [z.degrees() for z in AB],abco,flush=True)
    return R0,AB,H,delta,(a,b,q,La,Lb,A0,B0,MO,x,m),guards

@lru_cache(None)
def two_remainders():
    R,(A,B),H,d,dat,guards=quartic_model()
    S=red(B*R[1]-g*g*A*R[3])
    U=red(B*B*R[0]-g*g*A*B*R[2]+g**4*A*A*R[4])
    extra=[*guards,d,A,B,red(A+B),red(A+2*B),R[4]]
    S0,c0=remove(S,extra);U0,c1=remove(U,extra)
    assert c0==[2]+[0]*9+[1]+[0]*6 and c1==[4]+[0]*16
    assert (S0.degrees()[1:3],U0.degrees()[1:3])==((8,21),(14,42))
    print('homogeneous arith star remainder raw/range',S.degrees(),U.degrees(),S0.degrees(),U0.degrees(),c0,c1,flush=True)
    return S0,U0

def inverse_const(U):
    assert U.degrees()[0:3]==(0,0,0)
    N=red(U*con(U))
    q=N.to_dict()
    a=q[(0,0,0,0)]
    assert a and len(q)==1
    return con(U)/a

@lru_cache(None)
def literal_fifth_poly():
    R,AB,H,d,dat,guards=quartic_model()
    a,b,m=dat[5:8];ha,hb=red((a-1)/2),red((b-1-m)/2)
    h=red(sum(cast(cv(F2,w))*s**j for j,w in enumerate(pol(h4(False),lambda x:x))))
    z0=s-1-2*h;z1=s*s/2-s-2*h
    wa=red((b*z0-z1)*inverse_const(b-a));wb=z0-wa
    AH=red(h+wa*ha+wb*hb)
    TS=red(s**3-s**4/4+2*h+wa*a**3+wb*b**3)
    TA=red(a**3-a**4/4+a-1)
    TB=red(b**3-b**4/4+b-1-m+m*a**3)
    rows=[[ha,a*ha,ha,TA],[hb,b*hb,hb+m*ha,TB],[h,s*h,AH,TS]]
    C0=[(-1)**(i+3)*det([[z for j,z in enumerate(row) if i!=j] for row in rows]) for i in range(4)]
    Dlt=red((b-a)*(s-a)*(s-b))
    HY=ev(H,g*v)
    M0=red(d*(v-1)-2*HY);M1=red(d*(v*v/2-v)-2*HY);M2=red(d*(v**3/3-v*v)-4*HY/3)
    Qa=red((s-b)*(b*s*M0-(b+s)*M1+M2))
    Qb=red((a-s)*(a*s*M0-(a+s)*M1+M2))
    Qs=red((b-a)*(a*b*M0-(a+b)*M1+M2))
    RA=red(Dlt*HY+Qa*ha+Qb*hb+Qs*h)
    RT=red(Dlt*(d*(v**3-v**4/4)+2*HY)+Qa*a**3+Qb*b**3+Qs*s**3)
    L=red(C0[0]*Dlt*HY+C0[1]*Dlt*v*HY+C0[2]*RA+C0[3]*RT)
    G,c=remove(L,[v-a,v-b,v-s,*guards,d])
    assert G.degrees()==(3,5,9,1) and c==[1,1,1,2,0,0,0,2,2,0,0,0,0,0,0]
    print('exact arith ordinary/silent fifth cubic',L.degrees(),G.degrees(),c,flush=True)
    return G
