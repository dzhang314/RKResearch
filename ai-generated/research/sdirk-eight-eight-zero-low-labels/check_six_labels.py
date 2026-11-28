"""Exactly eight physical zeros, five labels, finite rear gap phases."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
from sys import argv
kind=argv[1]
assert kind in ('zero-star','zero-arith')
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

Z2=(X-a)*(X-b); Z3=X*Z2
J=lambda P:sum((c*C(1,j+1)*D**i*X**(j+1) for (i,j),c in P.items()),R.zero)
P0=2*X-1-X*X*C(1,2);Poff=(X-1)*(X-1-u)
A0=lambda P,x:sum((c*x**j for (i,j),c in P.items()),K.zero)
split=A0(P0,a)*Poff-A0(Poff,a)*P0
expected=X*X-(2*u+4)*X+1+2*u
mult=-u*u/3+2*u/3+C(1,6)
assert mult and J(split)-split==mult*(X-a)*expected
assert A0(split,b) and not A0(expected,b)
assert P0.gcd(Poff)==R.one
J2,J3=J(Z2),J(Z3)
def ex(p,x):return sum((c*x**j for (i,j),c in p.items()),K.zero)
J2a,J2b=ex(J2,a),ex(J2,b);J3a,J3b=ex(J3,a),ex(J3,b)
dj=J2a*J3b-J2b*J3a
assert dj==a*a*b*b*(a-b)**3*C(1,24) and dj
L=lambda x:70*x**4-140*D*x**3+90*D**2*x*x-20*D**3*x+D**4
ap=(-L(a)*J3b+L(b)*J3a)/R(dj)
bp=(-J2a*L(b)+J2b*L(a))/R(dj)
CC,rem=divmod(ap*(Z2-J2)+bp*(Z3-J3)-L(X),Z2)
assert not rem and CC.degree(X)==2
def evX(p,y):return sum((c*D**i*y**j for (i,j),c in p.items()),R.zero)
def strip(f,Gs):
 for q in Gs:
  while f.degree(D)>0:
   k=f.gcd(q)
   if k.degree(D)==0:break
   f=f//k
 return f.monic()
mask=(X-a)*(X-b)*(X-s)*(X-t)*(X-r)
m0,m1,m2=[I(mask*X**j) for j in range(3)]
guard=[D]+[x-y for x in (a,b) for y in (s,t,r)]
H=strip(m0*m2-m1*m1,guard)
assert H
now('disjoint guarded degree',H.degree(D))
for F in (s,t,r):
 g=H.gcd(evX(CC,F))
 now('rear C3 gcd',g.degree(D))
 assert g.degree(D)==0
Fnum=sum((c*D**i*m1**j*m0**(2-j) for (i,j),c in CC.items()),R.zero)
g=H.gcd(Fnum)
now('extra C3 gcd',g.degree(D), 'moment singular gcd',m0.gcd(m1).gcd(m2).degree(D))
if g.degree(D):
 assert strip(g,[m0]).degree(D)==0
 assert H.gcd(m0).gcd(m1).gcd(m2).degree(D)==0

KC,T=ring('T',K)
for f0 in (a,b):
 for shift in offset:
   d0=1+f0+shift
   assert d0
   nodes=list(dict.fromkeys([a,b]+[d0-1-h for h in offset]))
   assert len(nodes)==4
   P=R.one
   for x in nodes:P*=X-x
   ms=[I(P*X**j).evaluate(D,d0).get((0,),K.zero) for j in range(4)]
   m0,m1,m2,m3=ms
   det=m0*m2-m1*m1
   assert det
   o=(m1*m3-m2*m2)/det
   p=(m1*m2-m0*m3)/det
   P2=T*T+p*T+o
   F3=CC.evaluate(D,d0)
   B3=KC.from_dict(dict(F3.items()))
   assert all(B3.evaluate(T,c) for c in nodes if c not in (a,b))
   assert P2.gcd(B3).degree()==0
now('all six-overlap frames close',kind)
