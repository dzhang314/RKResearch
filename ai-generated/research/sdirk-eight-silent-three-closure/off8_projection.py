"""Explicit reverse-silent-third univariate projection."""
from sympy import QQ,sqrt
from sympy.polys.rings import ring
K=QQ.algebraic_field(sqrt(2)/2)
R,u=ring("u",K)
t=K.unit
kappa=1+2*u-u*u
D=4-kappa*(u-2)
N=2
x=D-N;z=D-N*(1+u)
Lb=lambda X:70*X**4-140*X**3*D+90*X**2*D**2-20*X*D**3+D**4
def protect(f,g):
 assert f
 while (h:=f.gcd(g)).degree()>0:f=f.exquo(h)
 return f.monic()
def primitive(front):
 f=1+2*t;w=2-f if front else 2*f;r=K.zero if front else 3*f/2-1
 a=R(N*(1+f));b=R(N*(1+w))
 A,B=f/2,(w-r)/2
 Qa=lambda X:B*(b-X)*Lb(a)+A*(X-a)*Lb(b)
 p=(x-N)*Qa(x)*Lb(z)-kappa*(z-N)*Qa(z)*Lb(x)
 u0=protect(p,u*D*kappa*(u-2))
 u0=u0.exquo(u0.gcd(u0.diff(u))).monic()
 m0=Qa(0);m1=Qa(1)-m0
 Rq=70*m0**4+140*m0**3*m1*D+90*m0**2*m1**2*D**2+20*m0*m1**3*D**3+m1**4*D**4
 # Leading-denominator and shared-root pieces are separated, not discarded in the full tableau chart.
 D0=u0.gcd(m1)
 D1=u0.gcd(Rq)
 good=protect(u0,m1*Rq)
 print('silent r2 branch',front,'raw',p.degree(),'guarded',u0.degree(), 'constant',D0.degree(),'shared-or-constant',D1.degree(), 'coprime',good.degree(),flush=True)
 for i in (u0,good,D0,D1):
  fc=i.factor_list()[1]
  print('factor degrees',[(q.degree(),m) for q,m in fc],flush=True)
 return good,D0,D1
if __name__=='__main__':
 for v in (True,False):primitive(v)
