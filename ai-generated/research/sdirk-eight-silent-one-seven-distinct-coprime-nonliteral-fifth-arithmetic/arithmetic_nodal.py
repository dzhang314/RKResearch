"""Alternative arithmetic fifth projector using the five already active pegs."""
from star_fifth import *
from time import perf_counter
import shared_star_projection as ns

def to_small(Z):
 return ns.CX.from_dict({(j,k,l,m):w for (i,j,k,l,m),w in Z.to_dict().items() if not i})
def from_small(Z):
 return CX.from_dict({(0,j,k,l,m):w for (j,k,l,m),w in Z.to_dict().items()})

@lru_cache(None)
def nodal_projection(f,i):
 J,Tf,Af,D,Q0,P0,gs,a,b=front(f,i)
 X=1-g;C1=X-g*u;D1=X-2*g*u;Lx=L(X)
 q0,q1=coeff_var(Q0,0)
 q0=fold(g*q0);q=lambda x:fold(q0+x*q1)
 qx,qc,qd=map(q,(X,C1,D1))
 H=-2+u+4*u*u-u**3;T=4*u**3-12*u*u+3*u+2
 k=1+2*u-u*u
 F=fold(H*L(D1)*qx*qc+2*T*L(C1)*qx*qd-k*T*Lx*qc*qd)
 Y=from_small(ns.nodalR(list(map(to_small,[g*a,g*s,X,C1,D1])),to_small(q0),to_small(q1)))
 E,ne=guard_strip(F,[u,*gs,L(g*a),Lx,1-g-g*a])
 N,nn=guard_strip(Y,[u,*gs,L(g*a),Lx,1-g-g*a])
 print('j5 arithmetic five-peg degrees',f,i,E.degrees(),N.degrees(),ne,nn,flush=True)
 assert (E.degrees()[2],N.degrees()[2])==(5,6)
 return J,Tf,Af,D,Q0,E,N
