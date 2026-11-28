"""The actual virtual fifth at an earlier literal clock pins strict-four."""
from no_extra import *
from literal_shared_pole_front import frontdata,exact_uc_y
from functools import lru_cache

@lru_cache(None)
def read(f,i):
 A,B,m,ha,hb,a,b,h,H4,L0,e,tau,ah,HS,XT,XA,dT,dA,*_=frontdata(f,i)
 M0=b-1;M1=b*b/2-b;M2=b*b*b/3-b*b
 J=M2-(A+B)*M1+A*B*M0
 T0=[b**3-b**4/4+(A+B)*M2-A*B*M1,J]
 A0=add([L0[0]*M0+L0[1]*M1],sc(e,J))
 T1=add(mul(H4,add(dT,[-tau])),sc(exact_uc_y(XT),a-b))
 A1=add(mul(H4,add(dA,[-ah])),sc(exact_uc_y(XA),a-b))
 E=add(mul(T0,A1),sc(mul(A0,T1),-1))
 assert E
 G=mon(guarded(E,[[-A,F2(1)],[-B,F2(1)],H4]))
 assert len(G)-1==(1 if f else 3)
 assert len(gcdp(G,T1))==1 # actual first slope already suffices
 assert len(gcdp(gcdp(G,T0),A0))==1
 print('exact shared fifth fourth projection:',f,i,len(G)-1,flush=True)
 return G,(T0,A0,T1,A1)
