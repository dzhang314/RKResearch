"""Independent exact moment, rational square and cardinal audits."""
import sympy as S
from itertools import product
y,c=S.symbols("y c")
I=lambda p:S.integrate(p,(y,0,1))
M=y*y*(y-c)**2
W=(1-y)*S.integrate(M,(y,0,y))
m=[S.factor(I(W*y**j)) for j in range(4)]
want=[(7*c*c-7*c+2)/420,(28*c*c-30*c+9)/2520,
      (40*c*c-45*c+14)/5040,(150*c*c-175*c+56)/25200]
assert all(S.cancel(a-b)==0 for a,b in zip(m,want))
D0=56*c**4-105*c**3+75*c*c-24*c+3
pivot=S.Matrix([[m[1],m[0]],[m[2],m[1]]])
assert S.cancel(pivot.det()+D0/6350400)==0
u,v=pivot.inv()*S.Matrix([-m[2],-m[3]])
N=[42000,-154000,246980,-225900,128904,-47088,10797,-1428,84]
P=sum(n*c**(8-i) for i,n in enumerate(N))
assert S.cancel(u*u-4*v-P/(100*D0**2))==0
print("exact orthogonal-quadratic moments, determinant and degree-eight discriminant")
rq=[sum(n*a**(8-i) for i,n in enumerate(N))%7 for a in range(1,7)]
assert rq==[6,5,6,3,6,3]
assert not (set(rq)&{x*x%7 for x in range(7)})
for a,b in product(range(49),repeat=2):
    if (a%7==0)==(b%7==0):
        continue
    norm=sum(n*a**(8-i)*b**i for i,n in enumerate(N))
    assert norm%7==0 and norm%49!=0
print("all rational discriminant residues excluded: mod7 units and valuation-one edges")

f,g,h=S.symbols("f g h")
nodes=(f,g,h)
T=(y-f)*(y-g)*(y-h)
base=S.symbols("p0:4")
V=sum(q*y**i for i,q in enumerate(base))
rhs=S.cancel((V-V.subs(y,0)*T/T.subs(y,0))/y)
lhs=sum(V.subs(y,z)*S.prod(y-t for t in nodes if t!=z)
        /(z*S.prod(z-t for t in nodes if t!=z)) for z in nodes)
assert S.cancel(lhs-rhs)==0
print("three-site cardinal interpolation of V(z)/z; exact polynomial quotient")

a,b,R,k,E0,E1=S.symbols("a b R k E0 E1")
N=2*(4*b*k*k*y-4*b*k*k+2*b*k*y+2*b*k-2*k*y+y)/(2*k-1)
Na=S.cancel(a*N.subs({y:y/a,b:b/a}).subs(k,c/(2*c-4*b)))
assert S.cancel(Na-2*((-2*a*b+a*c+b*c-c*c)*y+a*b*c)/(a*(2*b-c)))==0
assert S.cancel(Na.subs(y,a)/(a*a*(a-c))+2/a**2)==0
assert S.cancel(Na.subs(y,b)/(b*b*(b-c))+2*(c-2*a)/(a*b*(c-2*b)))==0
C2=(y-R)*(c-2*y)
D2=(1-y)*(E1-y*E0)
c0,c1,c2=reversed(S.Poly(C2,y).all_coeffs())
d0,d1,d2=reversed(S.Poly(D2,y).all_coeffs())
g=(c2*d1-c1*d2)*a*b+(c2*d0-c0*d2)*(a+b)+(c1*d0-c0*d1)
assert S.expand(C2.subs(y,a)*D2.subs(y,b)-C2.subs(y,b)*D2.subs(y,a)-(a-b)*g)==0
print("A(1)=0: literal first two ratio formulas and symmetric sum/product reduction")
