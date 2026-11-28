"""No active literal front: the sole transported literal fixes the profile scale."""
from shared_star_projection import *
from shared_silent8_projection import eexact

@lru_cache(None)
def gauge(f,i):
 A,B,m,ha,hb,a,b,hh,H4,*_=frontdata(f,i)
 a=C(a)
 x=1-g;mid=x-g;c=mid-g*v;d=mid+g*v;z=g*a
 k=2-v*v
 L=lambda x:sum(p*x**j for j,p in enumerate(Lco))
 pc,pd,px=L(c),L(d),L(x)
 T=can(k*px*(c-z)*(d-z))
 S=can((x-z)*(pc*(d-z)+pd*(c-z)))
 q1=can(2*T-S);q0=can(2*g*T-q1*x)
 R0=can(q1-exdiv(can((x-z)*(pd*(c-z)-pc*(d-z))),v))
 R=centered(exdiv(R0,v*v-1))
 A,B=Vcoeff(R);assert len(A)==len(B)==7
 guards=list(map(Gcoeff,[g,x-z,px,L(z)]))
 assert len(guarded(gcdp(A,B),guards))==1
 P0,P1=-term(A,g),term(B,g)
 def get(X):return check_post(centered(can(X)),P0,P1)
 Q0,Q1=centered(q0),centered(q1)
 cap=max(Q0.degrees()[1],Q1.degrees()[1])
 def hom(X):return can(sum(a*P0**j*P1**(cap-j)*g**k*t**l for (i,j,k,l),a in X.to_dict().items()))
 Z0,Z1=map(lambda X:ef(Gcoeff(hom(X))),(Q0,Q1))
 common=egcd(Z0,Z1)
 Z0,Z1=eexact(Z0,common),eexact(Z1,common)
 cop=sum(w*(-q0)**j*q1**(4-j) for j,w in enumerate(Lco))
 Q=lambda X:can(q0+q1*X)
 extras=[q1,cop,Q(x),Q(c)*Q(d),Q(z),pc*pd,(c-z)*(d-z),v*v,v*v-1,2-v*v]
 guard=[*guards,B,*list(map(lambda X:Gcoeff(get(X)),extras)),unef(common)]
 assert (Z0.degree(),Z1.degree(),common.degree())==(9,8,10)
 print('no-front star gauge degrees',f,i,Z0.degree(),Z1.degree(),common.degree(),flush=True)
 return A,B,unef(Z0),unef(Z1),guard
