"""Silent two-clock varying triple and zero reflected ratio at six zeros."""
import sympy as S
from sympy.polys.rings import ring
u,v,z=S.symbols("u v z")
Q=u**3-3*u**2+S.Rational(3,4)*u+S.Rational(1,2)
H=v**2-2*v-1
red=lambda p:S.rem(S.rem(S.expand(p),Q,u),H,v)
basis=[u**i*v**j for i in range(3) for j in range(2)]
vec=lambda a:S.Matrix([S.Poly(a,u,v).coeff_monomial(e) for e in basis])
B=S.Matrix.hstack(*(vec(red((u+2*v)**k)) for k in range(6)))
M=B.inv()
ucoef=M*vec(u);vcoef=M*vec(v)
assert red(sum(c*(u+2*v)**i for i,c in enumerate(ucoef))-u)==0
assert red(sum(c*(u+2*v)**i for i,c in enumerate(vcoef))-v)==0
f=S.Poly(S.resultant(Q,H.subs(v,(z-u)/2),u),z).monic()
assert f.degree()==6 and f.is_irreducible and red(f.as_expr().subs(z,u+2*v))==0
K=S.QQ.algebraic_field((f,z));Z=K.unit
U=sum((K.convert(c)*Z**i for i,c in enumerate(ucoef)),K.zero)
V=sum((K.convert(c)*Z**i for i,c in enumerate(vcoef)),K.zero)
assert U+2*V==Z
C=lambda a,b=1:K.convert(S.Rational(a,b))

R,X=ring('X',K)
for i in (0,1):
 D=2+i*U
 a=1+2*U
 P=[1+U,-2-U,K.one]
 ev=lambda z:sum((p*z**j for j,p in enumerate(P)),R.zero)
 J=lambda k,z:sum((p*z**(j+k+1)*C(1,j+k+1) for j,p in enumerate(P)),R.zero)
 def L(t):return 70*t**4-140*D*t**3+90*D*D*t*t-20*D**3*t+D**4
 def I(P0):return sum((c*D**j*C(1,j+1) for (j,),c in P0.items()),K.zero)
 for rear in ('star','arith'):
    W=(2-V) if rear=='star' else 2*V
    s=D-1-W;t=D-1-V;d=D-1
    assert len({a,s,t,d})==4
    P4=(X-a)*(X-s)*(X-t)*(X-d)
    m0,m1,m2,m3=[I(P4*X**j) for j in range(4)]
    Delta=m0*m2-m1*m1
    assert Delta
    q0=(m1*m3-m2*m2)/Delta
    q1=(m1*m2-m0*m3)/Delta
    assert not (m0*q0+m1*q1+m2) and not (m1*q0+m2*q1+m3)
    qq=X*X+q1*X+q0
    assert L(a)
    F=L(a)*(a*(J(0,X)-ev(X))+X*ev(X)-J(1,X))-L(X)*(a*ev(R(a))-J(1,R(a)))
    hh=F.gcd(qq)
    print(i,rear,'forward gate gcd',hh.degree())
    assert hh.degree()==0
