"""Both distinct D endpoints, both triple-D midpoint arithmetic."""
import sympy as S
from sympy.polys.rings import ring

h=S.Symbol('h')
def H(v):return -2+v+4*v*v-v**3
def k(v):return 1+2*v-v*v
def num(v):return (1+4*v-4*v*v)*H(v)+4*v*v*(3*v-2)
def L4(t,m):return t**4-S.Rational(6,7)*m*m*t*t+S.Rational(3,35)*m**4
U=S.Poly(S.expand(num(h)*L4(0,h+1)-k(h)**2*H(h)*L4(h,h+1)),h)
print('guarded endpoint factor degrees',[(f.degree(),p) for f,p in U.factor_list()[1]],flush=True)
factors=[f.monic() for f,p in U.factor_list()[1] if all(f.gcd(S.Poly(guard,h)).degree()==0 for guard in [h,h+1,k(h),num(h),H(h),3*h-2])]
assert len(factors)==1 and factors[0].degree()==7 and factors[0].is_irreducible
K=S.QQ.algebraic_field((factors[0],h)); hh=K.unit
m=hh+1;ell=2*m
kap=k(hh);q=num(hh)/H(hh)
R,t=ring('t',K)
a=K.convert(S.Rational(6,7))*m*m
b=K.convert(S.Rational(3,35))*m**4
c=K.convert(S.Rational(3,5))*m*m
L=lambda x:x**4-a*x*x+b
L3=lambda x:x**3-c*x
assert q*L(0)==kap**2*L(hh)
beta=-4*L(hh)/q
mu=(hh*hh-c)/L(hh)
S0=(c/mu+b)/(hh*hh)
W=t*t-S0
L0=L(t)
Q0=L3(t)-mu*t*L0
assert Q0==-mu*t*(t*t-hh*hh)*W
Lroot=S0*S0-a*S0+b
assert S0 and Lroot and S0!=hh*hh
P=R(kap/2)+(q-1)/(4*hh)*t+(q+1-2*kap)/(4*hh*hh)*t*t
Pe=R(kap/2)+(q+1-2*kap)/(4*hh*hh)*t*t
Po=P-Pe
assert P.evaluate(t,-hh)==K.one/2 and P.evaluate(t,hh)==q/2
def inv(v):
    a0,b0,g=v.gcdex(L0**2)
    assert g==R.one
    return a0
C=(inv(Q0)*(4*m**6/175))%(L0**2)
def width(F):
    return ((F*C)%(L0**2)).get((7,),K.zero)
const=-4*(2*S0-a)/Lroot-ell*width((L0*inv(W))%(L0**2))
def tra(F):
    w=F%W
    tg=2*w.get((0,),K.zero)/Lroot+sum(F.evaluate(t,s)/L(s) for s in [-hh,K.zero,hh])
    return 2*tg-ell*width(F)
assert not tra(Po)
tr=tra(Pe)
assert const and tr and beta
rho=const/(beta*tr)
# Polynomial literal fourth forward read; carry the centered variable.
fn=P.compose(t,t-m)
jf=R.from_dict({(i+1,):v/(i+1) for (i,),v in fn.items()})
bf=fn.get((1,),K.zero)
cf=fn.get((2,),K.zero)
s0=bf+cf*K.convert(S.Rational(4,3))
s1=-K.one/kap+cf*2*(kap+1)/(3*kap)
d4=s0+s1*(t+m-1)
n4=P-jf.compose(t,t+m)
RR,T,Z=ring('T,Z',K)
fa=lambda p:RR.from_dict({(i,0):v for (i,),v in p.items()})
H4=fa(L0)+beta*rho*fa(W)*(fa(Pe)+Z*fa(Po))-(1-Z*Z)*(beta*rho*rho/4)*fa(W)**2
F4=(1-Z)*(rho/2)*fa(W*d4)-fa(n4)
Rr=H4.resultant(F4)
print('projection alive, degree',Rr.degree(),flush=True)
print('ring',Rr.ring,flush=True)
assert Rr and Rr.degree()==6
Y=Rr.ring.gens[0]
g=Rr.gcd(Rr.compose(Y,-Y)).monic()
print('two-ended factor degrees',[(a.degree(),p) for a,p in g.factor_list()[1]],flush=True)
assert g.degree()==0
print('two-ended exact resultant gcd 1')
