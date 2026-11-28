"""Separate reverse site at stage six/seven, star eighth, ordinary fourth/fifth."""
from arithmetic_nodal import *
from arithmetic_crt import degree_safe_reduction
from star_fifth import *
from shared_silent8_projection import red_e

def q_guards(Q0,gs,a):
 X=1-g
 q0,q1=coeff_var(Q0,0);q0=fold(g*q0)
 base=[*gs,L(g*a),L(X),X-g*a,L(g*s),X-g*s]
 qx=fold(q0+X*q1)
 sq,_=guard_strip(q1,base);xx,_=guard_strip(qx,base)
 qres=fold(sum(Lco[j]*(-q0)**j*q1**(4-j) for j in range(5)))
 qres,_=guard_strip(qres,[*base,sq,xx])
 return [*base,sq,xx,qres]

def even(Z):
 assert all(k%2==0 for i,j,k,l,m in Z.to_dict())
 return CX.from_dict({(i,j,k//2,l,m):p for (i,j,k,l,m),p in Z.to_dict().items()})

@lru_cache(None)
def star67(f,i):
 J,T,A,D,Q0,P0,gs,a,b=front(f,i)
 x=1-g;cx=x-g*u
 q0,q1=coeff_var(Q0,0)
 q0=fold(g*q0)
 qx=fold(q0+x*q1);Lx=L(x);k=1+2*u-u*u
 loc=exdiv(fold(L(cx)-k*Lx),u)
 P=coeff_var(subst_var(loc,2,u+1),2)
 assert len(P)==4
 # Now the symbolic u coordinate denotes V=(actual normalized gap-1)^2.
 E0=fold((qx*(P[0]+P[2]*u)+g*Lx*(2-u)*q1)*g*q1
          +(qx-g*q1)*qx*(P[1]+P[3]*u))
 c=x-g-g*u;d=x-g+g*u
 N0=even(from_small(ns.nodalR(list(map(to_small,[g*a,g*s,x,c,d])),
                           to_small(q0),to_small(q1))))
 simple=q_guards(Q0,gs,a)
 E,ne=guard_strip(E0,[u,u-1,u-2,*simple])
 N,nn=guard_strip(N0,[u,u-1,u-2,*simple])
 P0,nq=guard_strip(fold(E.resultant(N,2)),simple)
 assert P0
 print('j6/j7 star reverse-eliminated E, N, projection',f,i,E.degrees(),N.degrees(),
       P0.degrees(),ne,nn,nq,flush=True)
 return J,P0,T,A,D,Q0,E,N
