"""Exact quintic gate and cubic gcd for two shared D labels, arithmetic/star."""
import sympy as S
from sympy.polys.rings import ring
x=S.Symbol('u')
p=639*x**5-4686*x**4+5552*x**3+7776*x**2-1392*x-1568
H=1+3*x/2;m=(H+2)/2
D=-2+x+4*x*x-x**3
kk=1+2*x-x*x
N=(1+4*x-4*x*x)*D+4*x*x*(3*x-2)
L=lambda y:(y-H/2)**4-6*S.Rational(1,7)*m*m*(y-H/2)**2+3*S.Rational(1,35)*m**4
assert S.expand(L(x)*N-L(2*x)*kk*D+x*(3*x-2)*(x*x-2*x-1)*p/1120)==0
Q=S.Poly(p,x,domain=S.QQ)
assert Q.is_irreducible
K=S.QQ.algebraic_field((Q,x));u=K.unit
H=1+3*u/2;m=(H+2)/2
S0,y=ring('y',K);v=y-H/2
L3=v**3-3*m*m*v/5
L4=v**4-6*m*m*v*v/7+3*m**4/35
D=-2+u+4*u*u-u**3;kk=1+2*u-u*u
N=(1+4*u-4*u*u)*D+4*u*u*(3*u-2)
f1=kk/2;f2=N/(2*D);r=1-u*u/8
assert all([u,H,H-u,H-2*u,f1,f2,r])
at=lambda f,z:f.evaluate(y,z)
a=at(L3,u)/at(L4,u)
b=at(L3,2*u)/at(L4,2*u)
M=(L3-(a+(b-a)*(y-u)/u)*L4).exquo((y-u)*(y-2*u))
assert M.degree()==3
T,z=ring('z',K);M=T.from_dict(M.to_dict())
m0,m2,m3=[M[(j,)] for j in (0,2,3)]
lam=1-H*z*(m2+m3*(z+H))/m0
beta=-at(L4,u)/(f1*r)
l0=at(L4,K.zero)
weights=[(H-u)*(H-2*u)/(2*u*u),-H*(H-2*u)/(u*u),H*(H-u)/(2*u*u)]
t=[2*lam*l0-beta/2,-beta*(f1+lam*r),-beta*(f2+lam*r)]
E=sum(c*w for c,w in zip(t,weights))-(2*l0-beta*lam/2)
assert E.degree()==2 and M.gcd(E)==T.one
print('quintic gap field: cubic third-label row and quadratic last-read gcd one',flush=True)
