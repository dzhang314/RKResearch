"""Distinct seven-zero charts with the eighth row itself a quadratic zero."""
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

C=lambda h,k=1:K.convert(S.Rational(h,k))
R,D,X=ring('D X',K)
I=lambda P:sum((c*C(1,j+1)*D**(i+j) for (i,j),c in P.items()),R.zero)
J=lambda P:sum((c*C(1,j+1)*D**i*X**(j+1) for (i,j),c in P.items()),R.zero)
s=D-1
if kind=='star':
    m=D-2
    Pe=(X-a)*(X-b)
    F0=Pe*(X-s)
    F1=F0*(X-m)**2
    F2=Pe*((X-m)**2-2)
else:
    Qv=4*v**3-12*v*v+3*v+2
    Hv=v**3-4*v*v-v+2
    kk=1+2*v-v*v
    assert v and kk
    if kind=='arith':assert Hv and Qv
    t=s-v
    r=s-2*v
    F0=(X-a)*(X-b)*(X-s)*(X-t)*(X-r)
    Fs=F0//(X-s); Ft=F0//(X-t); Fr=F0//(X-r)
    assert Fs*(X-s)==F0 and Ft*(X-t)==F0 and Fr*(X-r)==F0
    F1=kk*Ft-Fs
    F2=Fr if kind=='ghost' else -kk*Qv*Fr-Hv*Fs
m0,m1,m2=[I(F0*X**i) for i in range(3)]
l0,l1,l2=[I(F1*X**i) for i in range(3)]
n0,n1,n2=[I(F2*X**i) for i in range(3)]
A=m0*l1-m1*l0
B=m2*l0-m0*l2
CC=m1*l2-m2*l1
det=n0*CC+n1*B+n2*A
now('det degree',det.degree(D),'ordinary pivot degree',A.degree(D))
assert det

Z2=(X-a)*(X-b);Z3=X*Z2
J2,J3=J(Z2),J(Z3)
ex=lambda P,x:sum((c*x**j for (i,j),c in P.items()),K.zero)
J2a,J2b=ex(J2,a),ex(J2,b)
J3a,J3b=ex(J3,a),ex(J3,b)
assert J2a*J3b-J2b*J3a==a*a*b*b*(a-b)**3*C(1,24)
inv=C(24)/(a*a*b*b*(a-b)**3)
L=lambda x:70*x**4-140*D*x**3+90*D**2*x*x-20*D**3*x+D**4
al=(-L(a)*J3b+L(b)*J3a)*inv
be=(-J2a*L(b)+J2b*L(a))*inv
F=al*(Z2-J2)+be*(Z3-J3)-L(X)
F3,rem=divmod(F,Z2)
assert not rem and F3.degree(X)==2
d,e,f=[sum((c*D**i for (i,j),c in F3.items() if j==k),R.zero) for k in (2,1,0)]
res=(A*f-CC*d)**2-(A*e-B*d)*(B*f-CC*e)
now('resultant degree',res.degree(D))

# The only exact factor removed is the forbidden D=0.
det,rem=divmod(det,D**6)
assert not rem and det.degree(D)==9
assert res.degree(D)==(30 if kind=='star' else 32)
now('guarded determinant degree',det.degree(D),'resultant degree',res.degree(D))

def rr(a,p):
    s=S.Rational(str(a));return int(s.p)*pow(int(s.q),-1,p)%p
def evk(a,z0,p):
    n=0
    for k in a.to_list():n=(n*z0+rr(k,p))%p
    return n
def reduce(P,z0,p):
    return nmod_poly([evk(P.get((i,0),K.zero),z0,p) for i in range(P.degree(D)+1)],p)
CERTS = {
  'ghost': (17,1,(16,7,6)),
  'arith': (59,12,(10,4,58)),
  'star': (13,11,(4,7)),
}
p,zz,values=CERTS[kind]
assert p>7 and S.isprime(p)
gg=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
assert gg.degree()==G.degree() and gg(zz)==0 and gg.derivative()(zz)!=0
assert tuple(evk(x,zz,p) for x in ((u,b) if kind=='star' else (u,b,v)))==values
d0=reduce(det,zz,p); n0=reduce(res,zz,p)
assert d0.degree()==det.degree(D) and n0.degree()==res.degree(D)
assert d0.gcd(n0).degree()==0
now('exact unit gcd by good reduction',kind,p,zz,values)
