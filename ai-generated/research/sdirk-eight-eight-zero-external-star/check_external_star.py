"""Exact guarded diagonal projection for the entire external live reflected star."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
from sys import argv
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
assert Q.is_irreducible
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
K=E;z=w;G=F
u=ev(K,u_w,w);b=ev(K,b_w,w)
assert u+b==z
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
sigma=(T-co(a))*(T-co(b))*(T-co(X))
m=D-2
Y=T-co(m)
def I1(P):
    return sum((x*D**j*C(1,j+1) for (j,),x in P.items()),R.zero)
def J1(P):
    return P.ring.from_dict({(j+1,):x*C(1,j+1) for (j,),x in P.items()})
E=sigma-J1(sigma)
M=[I1(Y**j*sigma) for j in range(5)]
V=[I1(Y**j*E) for j in range(4)]
r=[M[j+2]-2*M[j] for j in (0,1,2)]
L0=V[2]-2*V[0]
Ld=I1((Y**2-2)*(Y*sigma-J1(Y*sigma)))
Le=V[3]-2*V[1]
F=[(2*M[j+1]-M[j+2])*V[0]+(M[j+2]-2*M[j])*V[1]+(M[j]-M[j+1])*V[2]
   for j in (0,1)]
A0=L0**2*r[2]-L0*(Ld+Le)*r[1]+Ld*Le*r[0]
A1=L0*F[1]-Ld*F[0]
now('biv degrees',[(v.degree(D),v.degree(X)) for v in (L0,Ld,Le,A0,A1)])
def nrm_pair(poly):
    j=poly.degree(X)
    pp,qq=D1.zero,D1.zero
    z,w=D1.one,D1.zero
    for i in range(j+1):
        f=ccollect(poly,i)*l2**(j-i)
        pp+=f*z;qq+=f*w
        z,w=pair_times((z,w),(D1.zero,D1.one))
    return pp,qq
def norm0(f):
    a,b=nrm_pair(f)
    return a*a-a*b*l1+b*b*l2*l0
def strip0(f):
    a, i=f,0
    while a and not a.get((0,),K.zero):
        a=a//DD
        i+=1
    return a,i
def norm(f):
    n=norm0(f)
    n1=stripC2(n)
    n2,j=strip0(n1)
    now('norm degrees',n.degree(),n1.degree(),n2.degree(),j)
    return n2
pp=[norm(k) for k in (L0,Ld,Le)]
g0=pp[0].gcd(pp[1]).gcd(pp[2])
now('singular pivot gcd',g0.degree())
assert tuple(p.degree() for p in pp)==(16,18,18) and g0.degree()==0
N0,N1=map(norm,(A0,A1))
g=N0.gcd(N1)
now('ordinary fourth-v-fifth gcd',g.degree())
assert (N0.degree(),N1.degree())==(46,42) and g.degree()==0

dd= l2
assert dd.gcd(l1).degree()==0
def at_linear(f):
    k=f.degree(X)
    return sum((ccollect(f,i)*(-l0)**i*l1**(k-i) for i in range(k+1)),D1.zero)%dd
gr=dd.gcd(at_linear(A0)).gcd(at_linear(A1))
now('leading drop read gcd',gr.degree())
assert gr.degree()==0
gl=dd.gcd(at_linear(L0)).gcd(at_linear(Ld)).gcd(at_linear(Le))
now('leading drop pivot gcd',gl.degree())
assert gl.degree()==0
print('verified complete external live-star exclusion',flush=True)
