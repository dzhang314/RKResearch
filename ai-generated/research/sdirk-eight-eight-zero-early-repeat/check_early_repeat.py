"""Exact early-only repeat elimination in the silent and star rear phases."""
import sympy as S
from sympy.polys.rings import ring
from time import monotonic
from sys import argv
kind=argv[1]
assert kind in ('ghost','star')
vdegree=3
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
Hv=v_**3-4*v_**2-v_+2
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
if kind=='star':
    K=E;z=w;G=F
    u=ev(K,u_w,w);b=ev(K,b_w,w)
    assert u+b==z
else:
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

C=lambda q,r=1:K.convert(S.Rational(q,r))
R,D,X=ring('D X',K)
I=lambda p:sum((q*C(1,j+1)*D**(i+j) for (i,j),q in p.items()),R.zero)

Z2=(X-a)*(X-b); Z3=X*Z2
J=lambda P:sum((c*C(1,j+1)*D**i*X**(j+1) for (i,j),c in P.items()),R.zero)
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
D1,DD=ring('q',K)
def ccollect(G,j):
 return D1.from_dict({(i,):z for (i,d),z in G.items() if d==j})
l0,l1,l2=[ccollect(CC,i) for i in range(3)]
def pair_times(x,y):
 a,b=x;c,d=y
 return a*c-b*d*l2*l0,a*d+b*c-b*d*l1
def nrm(poly):
 j=poly.degree(X)
 ps=[(D1.one,D1.zero)]
 for i in range(j):
  ps.append(pair_times(ps[-1],(D1.zero,D1.one)))
 a,b=D1.zero,D1.zero
 for i in range(j+1):
   z=ccollect(poly,i)*l2**(j-i)
   a+=z*ps[i][0];b+=z*ps[i][1]
 return a*a-a*b*l1+b*b*l2*l0
def stripC2(poly):
 while poly.degree()>0:
  d=poly.gcd(l2)
  if d.degree()==0:break
  poly=poly//d
 return poly

P,T=ring('T',R.to_domain())
co=lambda z:P(R(z))
F=(T-co(a))*(T-co(b))*(T-co(X))
s=D-1
if kind=='star':
  U0=F*(T-co(s))
  masks=[U0,U0*(T-co(D-2))**2,F*((T-co(D-2))**2-2)]
  baseguards=[s-a,s-b]
else:
  t=s-v;r=s-2*v
  k=1+2*v-v*v
  U0=F*(T-co(s))*(T-co(t))*(T-co(r))
  Fs=U0//(T-co(s));Ft=U0//(T-co(t));Fr=U0//(T-co(r))
  masks=[U0,co(k)*Ft-Fs,Fr]
  baseguards=[x-y for x in (s,t,r) for y in (a,b)]
def I1(P):
 return sum((x*D**j*C(1,j+1) for (j,),x in P.items()),R.zero)
rows=[[I1(F*T**j) for j in range(2)] for F in masks]
from itertools import combinations
mins=[a*d-b*c for (a,b),(c,d) in combinations(rows,2)]
def asD(p):
 return D1.from_dict({(i,):z for (i,j),z in p.items()})
ns=[stripC2(nrm(m)) for m in mins]
g=ns[0].gcd(ns[1]).gcd(ns[2])
assert tuple(p.degree() for p in ns)==((32,32,28) if kind=='ghost' else (30,28,32))
assert g.monic()==DD**4
print('norm degrees and gcd',*[p.degree() for p in ns],g.degree(),flush=True)
for guard in [DD]+list(map(asD,baseguards)):
 n=0
 while True:
   f=g.gcd(guard)
   if f.degree()==0:break
   g=g//f;n+=1
 print('scalar guard multiplicity',n,flush=True)
assert g.degree()==0
print('guarded common degree',g.degree(),flush=True)
assert l2.gcd(l1).degree()==0
eval_at_linear_c=lambda m:sum((ccollect(m,j)*(-l0)**j*l1**(m.degree(X)-j) for j in range(m.degree(X)+1)),D1.zero)
hl=l2
for m in mins:hl=hl.gcd(eval_at_linear_c(m))
assert hl.degree()==0
print('leading drop common gcd',hl.degree())
