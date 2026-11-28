"""Both actual D endpoints share the center and R is even; both openers arithmetic D,S,S."""
import sympy as S
from sympy.polys.fields import field
from sympy.polys.rings import ring
from time import monotonic
F,u=field('u',S.QQ)
U=S.Symbol('u')
def D(v):return -2+v+4*v*v-v**3
def k(v):return 1+2*v-v*v
def N(v):return (1+4*v-4*v*v)*D(v)+4*v*v*(3*v-2)
def f(v):
    q=N(v)
    h=k(v)*D(v)
    return v*(q-4*h)/(2*(q-h))
def p(z):
    return S.Poly.from_dict(z.to_dict(),U,domain=S.QQ)
v=f(u)
cycle=(f(v)-u).numer
z=2*u*v
Lv=z*z-S.Rational(6,7)*z+S.Rational(3,35)
L0=S.Rational(3,35)
rg=k(u)/(2*(u*u-z))
lam=2*rg*(v*v-z)/k(v)
# H at the when-repeated endpoint t=0, assuming the R pair is ±sqrt(z).
p0=z*(2*u*u+2*v*v-5*u*v)
hv=Lv*z*z/p0
r0=-rg*z
hvt=(4*F(L0)/lam)*(r0-F(S.Rational(1,2)))*(r0-lam/2)
num=(hv-hvt).numer
G=cycle.gcd(num)
assert G.degree()==0
print('degrees',cycle.degree(),num.degree(),'gcd',G.degree(),S.factor(p(G).as_expr()))
