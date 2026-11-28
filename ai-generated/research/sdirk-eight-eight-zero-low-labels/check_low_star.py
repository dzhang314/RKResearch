"""Exactly eight physical zeros, five labels, finite rear gap phases."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
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
K=E;Z=w
u=ev(E,u_w,w);b=ev(E,b_w,w)
a=1+2*u
assert u+b==Z and a and b and a!=b

from itertools import combinations
C=lambda p,q=1:K.convert(S.Rational(p,q))
R,D,X=ring('D X',K)
m=D-2;s=D-1
I=lambda p:sum((c*C(1,j+1)*D**(i+j) for (i,j),c in p.items()),R.zero)
AB=(X-a)*(X-b)
def det(M):
 (a,b,c),(d,e,f),(g,h,j)=M
 return a*(e*j-f*h)-b*(d*j-f*g)+c*(d*h-e*g)
def minors(rows):
 n=[]
 for (a,b),(c,d) in combinations(rows,2):n.append(a*d-b*c)
 q=n[0]
 for p in n[1:]:q=q.gcd(p)
 assert q
 return q.monic()
def strip(q,guards):
 for h in guards:
  while q.degree(D)>0:
    k=q.gcd(h)
    if k.degree(D)==0:break
    q=q//k
 return q.monic()
P3=AB*(X-s)
F=[I(P3*X**j) for j in range(3)]
E0=[I(P3*(X-m)**2*X**j) for j in range(3)]
G0=minors(list(zip(F,E0)))
print('disjoint minors degree',G0.degree(D),flush=True)
G0=strip(G0,[D,s-a,s-b])
print('disjoint guarded degree',G0.degree(D),flush=True)
assert G0.degree(D)==0
for f,o in ((a,b),(b,a)):
    d=1+f;assert d
    def ID(p,j):return I(p*X**j).evaluate(D,d)
    A=[ID(AB*(X-m)**2,j) for j in range(4)]
    B=[ID(AB,j) for j in range(4)]
    mat=[[A[i],B[i+1],-B[i]] for i in range(3)];rhs=A[1:]
    pivot=det(mat)
    assert pivot
    ns=[]
    for j in range(3):
      m0=[r[:] for r in mat]
      for i in range(3):m0[i][j]=rhs[i]
      ns.append(det(m0)/pivot)
    print('one overlap at s, bilinear product contradiction',ns[0]*ns[1]!=ns[2],flush=True)
    assert ns[0]*ns[1]!=ns[2]
    rr=2*m-f
    P4=AB*(X-s)*(X-rr)
    m0,m1,m2,m3=[I(P4*X**j) for j in range(4)]
    Q1=minors([(m0,m1),(m1,m2),(m2,m3)])
    QQ=strip(Q1,[D,s-a,s-b,rr-a,rr-b,rr-s])
    assert QQ.degree(D)==0
    print('one overlap at pair, raw/guarded gcd',Q1.degree(D),QQ.degree(D),flush=True)
for d,third in ((1+a,2*(1+a-2)-b),(1+b,2*(1+b-2)-a),(2+(a+b)/2,1+(a+b)/2)):
    assert d and third not in (a,b)
    P3=AB*(X-third)
    m0=[I(P3*X**j).evaluate(D,d) for j in range(5)]
    H=det([[m0[i+j] for j in range(3)] for i in range(3)])
    print('double overlap determinant',bool(H),flush=True)
    assert H
