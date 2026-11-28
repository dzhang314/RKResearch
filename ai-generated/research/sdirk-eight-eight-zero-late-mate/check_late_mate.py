"""Two determinant gates for a repeat connecting a late forward zero to a rear zero."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from time import monotonic
from sys import argv
kind=argv[1]
assert kind in ('ghost','arith','star')
vdegree=3 if kind=='ghost' else 6
T0=monotonic()
def now(*a):print(round(monotonic()-T0,2),*a,flush=True)
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
Hv=(v_**3-4*v_**2-v_+2 if kind=='ghost' else
    (8*v_**6-44*v_**5+22*v_**4+97*v_**3-55*v_**2-13*v_+6))
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
slot=int(argv[2])
if kind=='star':
  assert slot==0
  q=s
  U0=F*(T-co(s))
  masks=[U0,U0*(T-co(D-2))**2]
  baseguards=[s-a,s-b]
else:
  t=s-v;r=s-2*v
  k=1+2*v-v*v
  q=[s,t,r][slot]
  U0=F*(T-co(s))*(T-co(t))*(T-co(r))
  Fs=U0//(T-co(s));Ft=U0//(T-co(t));Fr=U0//(T-co(r))
  H0=v**3-4*v*v-v+2
  Q0=4*v**3-12*v*v+3*v+2
  M=(co(k)*Ft-Fs if slot==2 else
     Fr if kind=='ghost' else
     co(Q0)*Fr+co(H0)*Ft if slot==0 else
     co(k*Q0)*Fr+co(H0)*Fs)
  masks=[U0,M]
  baseguards=[x-y for x in (s,t,r) for y in (a,b)]
def I1(P):
 return sum((x*D**j*C(1,j+1) for (j,),x in P.items()),R.zero)
def J1(P):
 return P.ring.from_dict({(j+1,):x*C(1,j+1) for (j,),x in P.items()})
def det3(M):
 a,b,c=M
 return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
rows=[[I1(F*T**j) for j in range(2)] for F in masks]
(w,x),(y,z)=rows
A0=w*z-y*x
L=(T-co(q))*F; R0=(T-co(q))*J1(F)
mm=[I1(T**i*L) for i in range(4)]
nn=[I1(T**i*R0) for i in range(3)]
A1=det3([(mm[i],mm[i+1],nn[i]) for i in range(3)])
mins=[A0,A1]
def asD(p):
 return D1.from_dict({(i,):z for (i,j),z in p.items()})
print('raw eq degrees',[(m.degree(D),m.degree(X)) for m in mins],flush=True)
def strip_linear(p,s):
 while p.degree()>0:
  a,b=divmod(p,s)
  if b:break
  p=a
 return p
def rr(a,p):
    s=S.Rational(str(a));return int(s.p)*pow(int(s.q),-1,p)%p
def evk(a,z0,p):
    n=0
    for k in a.to_list():n=(n*z0+rr(k,p))%p
    return n
def specialize(pol,p,z0,degree=True):
    q=nmod_poly([evk(pol.get((i,),K.zero),z0,p) for i in range(pol.degree()+1)],p)
    if degree and q.degree()!=pol.degree(): raise ValueError("lead drops")
    return q
ns=[]
for m in mins:
 p=stripC2(nrm(m))
 print("norm",p.degree(),flush=True)
 for guard in [DD]+list(map(asD,baseguards)):
  p=strip_linear(p,guard)
 ns.append(p)
print("guarded degrees",tuple(n.degree() for n in ns),flush=True)
assert tuple(n.degree() for n in ns)==((26,30) if kind=="star" else (28,30))
assert l2.gcd(l1).degree()==0
eval_at_linear_c=lambda m:sum((ccollect(m,j)*(-l0)**j*l1**(m.degree(X)-j) for j in range(m.degree(X)+1)),D1.zero)
ls=[eval_at_linear_c(m)%l2 for m in mins]
def on_fiber(p,z0):
    gp=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
    if gp(z0)!=0 or gp.derivative()(z0)==0:return
    try:
        regular=[specialize(n,p,z0) for n in ns]
        l2p=specialize(l2,p,z0)
        line=[specialize(n,p,z0,False) for n in ls]
    except ValueError:return
    if regular[0].gcd(regular[1]).degree()!=0:return
    if l2p.gcd(line[0]).gcd(line[1]).degree()!=0:return
    return (p,z0)
fixed = {
    'ghost': {0:(17,1), 1:(17,1), 2:(17,1)},
    'arith': {0:(31,8), 1:(31,19), 2:(31,19)},
    'star': {0:(13,9)},
}
p,z0=fixed[kind][slot]
assert p>7 and S.isprime(p)
assert on_fiber(p,z0)
print("fixed",kind,slot,p,z0,flush=True)
