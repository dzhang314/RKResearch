"""Exact active-tail projection for the non-half invisible three-stage chart."""
from sympy import QQ,sqrt
from sympy.polys.rings import ring
from itertools import product
K=QQ.algebraic_field(sqrt(2)/2);t=K.unit
R,u,g=ring('u g',K)
J,v=ring('g',K)
L=lambda X:70*X**4-140*X**3+90*X**2-20*X+1
kappa=1+2*u-u*u
Den=-2+u+4*u*u-u**3
Qnum=(1+4*u-4*u*u)*Den+4*u*u*(3*u-2)
def univariate(X):
 X=R(X)
 assert X.degree(u)<=0
 return J.from_dict({(j,):v for (i,j),v in X.items() if i==0})
def strip(p,b):
 assert p
 while (D:=p.gcd(b)).degree()>0:
  p=p.exquo(D)
 return p
def exact_phase(front,rear):
 U=1+2*t;W=2-U if front else 2*U;r=K.zero if front else 3*U/2-1
 a,b=g*(1+U),g*(1+W);A,B=U/2,(W-r)/2
 x=1-g;c=x-g*u
 d=x-g*(2-u if rear else 2*u)
 Q=lambda X:B*(b-X)*L(a)+A*(X-a)*L(b)
 xg=univariate(Q(x));lx=univariate(L(x))
 assert xg.gcd(lx).degree()==0
 q0=univariate(Q(R.zero));q1=univariate(Q(R.one))-q0
 qres=70*q0**4+140*q0**3*q1+90*q0*q0*q1*q1+20*q0*q1**3+q1**4
 F=(x-g)*Q(x)*L(c)-kappa*(c-g)*Q(c)*L(x)
 H=(x-g)*Q(x)*L(d)-kappa*(d-g)*Q(d)*L(x) if rear else     Den*(x-g)*Q(x)*L(d)-Qnum*(d-g)*Q(d)*L(x)
 # Divide only factors with a known nonzero value in the actual chart.
 F=strip(F,u*g*(2*g-1));H=strip(H,g*(2*g-1)*u*(u-2) if rear else g*(2*g-1)*u*Den)
 print('literal polynomial degrees',front,rear,(F.degree(u),F.degree(g)),(H.degree(u),H.degree(g)),flush=True)
 res=J(F.resultant(H))
 print('projection raw',res.degree(),flush=True)
 G=strip(res,v*(2*v-1)*xg*lx)
 G=G.exquo(G.gcd(G.diff(v))).monic()
 print('projection guarded',front,rear,G.degree(),'constant',G.gcd(q1).degree(),'shared',G.gcd(qres).degree(),flush=True)
 n=F.degree(u)
 lC=J.from_dict({(j,):k for (i,j),k in F.items() if i==n})
 print('leading cubic exceptional degree',G.gcd(lC).degree(),flush=True)
 return G,F,H,q0,q1,qres
if __name__=='__main__':
 for f,r in product((True,False),repeat=2):exact_phase(f,r)
