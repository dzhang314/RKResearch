"""Exact both-S two-shared-D SDD star-star, including all possible row fours."""
import sympy as S
from sympy.polys.rings import ring
q,t=S.symbols('q t')
assert S.expand(35*q*q-120*q+48+37*(2-q)**2)==S.expand(4*(q-1)*(18*q-49))
d2=S.QQ(49,18)
L3=t**3-S.Rational(12,5)*t
L4=t**4-S.Rational(24,7)*t*t+S.Rational(48,35)
l4d=d2*d2-S.QQ(24,7)*d2+S.QQ(48,35)
slope=(d2-S.QQ(12,5))/l4d
assert slope and l4d
assert S.expand(L3-slope*t*L4-t*(18*t*t-49)*(203*t*t+204)/6253)==0
E=S.Poly(203*t*t+204,t,domain=S.QQ)
assert E.is_irreducible
K=S.QQ.algebraic_field((E,t))
P,w=ring('w',K)
e=K.unit
assert e and e!=K.one and e!=-K.one
r=(2-d2)/2
R=w*(w+e)/(2*(1-e))
v=lambda f,x:f.evaluate(w,x)
assert v(R,-K.one)==K.convert(S.QQ(1,2))
lam=(1+e)/(1-e)
assert lam and lam!=K.one and v(R,K.one)*2==lam
L=w**4-24*w*w/7+P(S.QQ(48,35))
B=-4*v(L,K.one)/lam
a=-B*(1+lam)/2
b=-B*r*(1+lam)
A=a+(b-a)*(w*w-1)/(d2-1)
J=(L-R*(A+B*R)).exquo(w*w-1)
assert J.degree()==2
kap=2-d2
X=w+2
T=-(X*X-4*X+2)/2
JT=-X**3/6+X*X-X
Lambda=1+(X-1)/kap
Delta=P(S.QQ(4,3))+2*(kap+1)*(X-1)/(3*kap)
C4=1-Lambda+2-Delta/2
N4=T-JT
assert C4==59*w/39+P(S.QQ(37,13))
assert N4==w**3/6-w*w/2-w+P(S.QQ(1,3))
assert J.gcd(C4*R-N4)==P.one
print('both unused singleton choices rejected by the genuine first-fourth read',flush=True)
G,g=ring('g',K)
E0=lambda f:G(v(f,e))
aff=E0(C4)*g-E0(N4)
U=E0(L)-g*(E0(A)+G(B)*g)
assert U.gcd(aff)==G.one
print('both third-D residual possibilities rejected in the whole exact field',flush=True)
