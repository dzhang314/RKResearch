"""Detected seven active triple at one defect clock, nonzero reverse factor."""
from unequal_finite import *
from equal_detected import ends
from sympy import isprime

def cr(front,i,pos,p,t):
 NP=lambda a:nmod_poly(a,p)
 u=NP([0,1]);den=-2+u+4*u*u-u**3
 F=(1+4*u-4*u*u)*den+4*u*u*(3*u-2)
 F,R=divmod(F,-(1+2*u-u*u));assert not R and F.degree()==3
 F*=pow(int(F.leading_coefficient()),-1,p)
 U=Bfield(F,p,t);u=U(u)
 p0=ends(front,1)[i]
 A=U(Epoly(JJ(p0)))
 g=1/(1+A+(u if pos==9 else 0));x=1-g
 c=x-g*u;d=x-2*g*u
 P=nodal([x,c,d])
 J=lambda j:sum(U(v)/(i+j+1) for i,v in enumerate(P))
 det3([J(j) for j in range(5)]).inv()
 return True
