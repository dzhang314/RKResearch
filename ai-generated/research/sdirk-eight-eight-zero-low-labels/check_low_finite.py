"""Exactly eight physical zeros, five labels, finite rear gap phases."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
from sys import argv
kind=argv[1]
assert kind in ('ghost','arith','zero-star','zero-arith')
vdegree={'ghost':3,'arith':6,'zero-star':2,'zero-arith':2}[kind]
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
Hv={2:v_**2-2*v_-1,3:v_**3-4*v_**2-v_+2,
    6:8*v_**6-44*v_**5+22*v_**4+97*v_**3-55*v_**2-13*v_+6}[vdegree]
H=S.Poly(Hv,v_).monic()
assert Q.is_irreducible and H.is_irreducible
K=S.QQ.algebraic_field((Q,u_));u=K.unit
R,b=ring('b',K)
Bb=b*b-(2*u+4)*b+1+2*u
F=S.Poly(S.resultant(Q,(b_**2-(2*u_+4)*b_+1+2*u_).subs(b_,w_-u_),u_),w_).monic()
assert F.degree()==6 and F.is_irreducible


def recover(K,R,t,mod,f,aa,bb,n,m):
    def vec(p):
        return S.Matrix([S.Rational(str((p.get((j,),K.zero).to_list()[::-1]+[0]*n)[i]))
                         for j in range(m) for i in range(n)])
    C=S.Matrix.hstack(*(vec(t**i%mod) for i in range(n*m)))
    C=C.inv()
    a=C*vec(aa);b=C*vec(bb)
    def eval(z):
        return sum((R(K.convert(x))*t**i%mod for i,x in enumerate(z)),R.zero)%mod
    assert eval(a)==aa and eval(b)==bb and not eval(f.all_coeffs()[::-1])
    return a,b
u_w,b_w=recover(K,R,R(u)+b,Bb,F,R(u),b,3,2)
E=S.QQ.algebraic_field((F,w_));w=E.unit
def ev(field,P,y):
    return sum((field.convert(x)*y**i for i,x in enumerate(P)),field.zero)
G=S.Poly(S.resultant(H,F.as_expr().subs(w_,z_-2*v_),v_),z_).monic()
assert G.degree()==6*vdegree and G.is_irreducible
S0,v=ring('v',E)
VH=sum((E.convert(x)*v**j for j,x in enumerate(H.all_coeffs()[::-1])),S0.zero)
w_z,v_z=recover(E,S0,S0(w)+2*v,VH,G,S0(w),v,6,vdegree)
K=S.QQ.algebraic_field((G,z_));z=K.unit
w=ev(K,w_z,z);v=ev(K,v_z,z);u=ev(K,u_w,w);b=ev(K,b_w,w)
assert u+b+2*v==z and not ev(K,H.all_coeffs()[::-1],v)
a=1+2*u
assert a and b and a!=b
assert not (4*u**3-12*u*u+3*u+2) and not (b*b-(2*u+4)*b+1+2*u)
now('primitive degree',G.degree())


from itertools import permutations
C=lambda q,r=1:K.convert(S.Rational(q,r))
R,D,X=ring('D X',K)
w=2-v if kind=='zero-star' else 2*v
offset=(K.zero,v,w)
assert len(set(offset))==3
assert all(a-b!=x-y for x,y in permutations(offset,2))
s,t,r=(D-1-x for x in offset)
I=lambda p:sum((q*C(1,j+1)*D**(i+j) for (i,j),q in p.items()),R.zero)
mask=(X-a)*(X-b)*(X-s)*(X-t)*(X-r)
g=I(mask).gcd(I(X*mask)).gcd(I(X**2*mask)).monic()
print('disjoint determinant gcd degree',g.degree(D),flush=True)
assert g==D**g.degree(D)
for f0 in (a,b):
 for shift in offset:
   d0=1+f0+shift
   assert d0
   nodes=list(dict.fromkeys([a,b]+[d0-1-h for h in offset]))
   assert len(nodes)==4
   M=R.one
   for x in nodes:M*=X-x
   m0,m1,m2=[I(M*X**j).evaluate(D,d0) for j in range(3)]
   assert m0*m2!=m1*m1
print('no single-overlap singularities; all finite-gap five-label cases excluded',flush=True)

from sympy import symbols
x,y=symbols('x y')
L=lambda t:70*t**4-140*t**3+90*t*t-20*t+1
delta=S.cancel((L(y)-L(x))/(y-x))
for z3 in (2*y-x,4*x-y):
    z=S.resultant(delta,L(z3),y)
    assert S.Poly(z,x).gcd(S.Poly(L(x),x)).degree()==0
print('both distinct four-Gaussian rear triples excluded in characteristic zero',flush=True)
