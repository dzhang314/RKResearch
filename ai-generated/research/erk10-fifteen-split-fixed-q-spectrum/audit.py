"""Exact nonlinear pair, fixed-q host, and exceptional-spectrum identities."""
import sympy as S
from spectrum import F, late, nodes, mul, moment
from literal import selftest

t,W,U,L,lam,Q=S.symbols("t W U L lam Q")
pair=t/L+(U-t)**2/(W-L*t)
form=(U*U+t*(W/L-2*U))/(W-L*t)
assert S.cancel(pair-form)==0
assert S.cancel(S.diff(form,t)*(W-L*t)**2-(W-L*U)**2/L)==0
r,v,z,j=S.symbols("r v z j")
aa=v**3*(3*v-4*r)/12; bb=v**2*(3*r-2*v)/6
assert S.expand(aa+(6*bb/r**3)*r**4/12-v*v*(v-r)**2/4)==0
f=z*(z-2*r/3)
assert S.cancel(S.integrate(f,(z,0,v))/f.subs(z,r)-v*v*(v-r)/r**2)==0
print("exact pair Möbius determinant and fixed-q host coefficient guards")

c,g,R=map(F,["2/3","1/2","3/4"])
e,f,h,M,JM=late(c,F(1,3),g,R)
assert (f,h)==(F(-3,5),F(11,30))
S0=mul([F(1),F(-1)],nodes([g,h,R]))
assert moment(mul(S0,JM))==0
assert moment(mul(mul(S0,nodes([f])),M))==0
right=mul(mul(nodes([F(0),c]),[F(1),F(-28,9)]),nodes([f]))
assert moment(mul(S0,right))==0
print("exact one-parameter A(1)=0 exclusion at c=2/3 and {g,R}={1/2,3/4}")

x,f,t,A,B=S.symbols("x f t A B")
M=x*x*(x-2)**2
JM=S.integrate(M,(x,0,x))
FF=x*(x-2)*(1+644*x)
I=lambda p:S.integrate((1-x)*p,(x,0,1))
matrix=S.Matrix([[I(r*x**k) for k in range(4)] for r in (JM,(x-f)*M,(x-f)*FF)])
coeff=[86298*f**2-477063*f-5939,-6*(111963*f**2-582798*f-5837),
       6*(242269*f**2-1207208*f-10357),-30*(30891*f**2-148922*f-1137)]
cof=[S.expand((-1)**j*matrix[:,[i for i in range(4) if i!=j]].det()) for j in range(4)]
factor=S.cancel(cof[0]/coeff[0])
assert factor!=0 and not factor.has(f)
assert all(S.expand(p-factor*q)==0 for p,q in zip(cof,coeff))
assert S.gcd_list(coeff)==1
P=sum(c*x**j for j,c in enumerate(coeff))
quad=x*x-2*x+2
near=x*x-2*x+3
hz=sum(sum(int(co)*A**i[0]*B**(2-i[0]) for i,co in S.Poly(c,f).terms())*x**j
       for j,c in enumerate(coeff))
check=lambda p:all(int(q)%7==0 and q.q==1 for q in S.Poly(S.expand(p),x,A,B,t).coeffs())
assert check(hz-(A-B)*(B*x+A+5*B)*quad)
assert check(S.expand(P.subs(f,1+7*t)/7)-t*(x-1)*quad)
assert check(S.expand(P.subs(f,1+49*t)/49)-(x-1)*(t*quad-near))
assert all((i*i-2*i+2)%7 for i in range(7))
for v in [0,3]: assert all((v*(i*i-2*i+2)-(i*i-2*i+3))%7 for i in range(7))
print("c=2 exact moment cubic, projective mod7 factoring, and two descents")
selftest()

# Symbolic independent check of the universal two-row dependence after
# integrating against the two paid blind polynomials.
y,c,f,D,q0,q2,q3=S.symbols("y c f D q0 q2 q3")
q1=(-(D+1)*q0-q2*c*c-q3*c**3)/c
P3=q0+q1*y+q2*y*y+q3*y**3
Omega=(D-1)/c
n=(y-f)*(f*(1+Omega*y)-(1-2*f/c)*(y-c))+P3.subs(y,f)/q0*y*(y-c)
K=S.cancel(n-f*(f-c)*P3/q0)
assert S.rem(K,y*(y-c)*(y-f),y)==0
print("head linear rows are dependent via the exact 0,c,f Jacobi polynomial identity")
