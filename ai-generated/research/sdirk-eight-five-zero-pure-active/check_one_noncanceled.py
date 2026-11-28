"""Nonzero aggregate pure support: fixed clock, two remaining literal zero labels."""
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

T,X=ring('X',K)
def L(x,D):return 70*x**4-140*D*x**3+90*D*D*x*x-20*D**3*x+D**4
for i in (0,1):
 D=2+i*U
 a=1+2*U
 off=D-1
 PP=[1+U,-2-U,K.one]
 ev=lambda t:sum((p*t**j for j,p in enumerate(PP)),T.zero)
 J=lambda k,t:sum((p*t**(j+1+k)*C(1,j+1+k) for j,p in enumerate(PP)),T.zero)
 assert J(0,T(a))==ev(T(a))
 for rear in ('star','arith'):
    W=(2-V) if rear=='star' else 2*V
    s=D-1-V;t=D-1-W
    assert D and len({a,s,t,off})==4
    qmask=(X-a)*(X-s)*(X-t)*(X-off)
    m=[sum((c*D**j*C(1,j+1) for (j,),c in (qmask*X**i).items()),K.zero) for i in range(4)]
    m0,m1,m2,m3=m
    dl=m0*m2-m1*m1
    assert dl
    q0=(m1*m3-m2*m2)/dl
    q1=(m1*m2-m0*m3)/dl
    assert not (m0*q0+m1*q1+m2) and not (m1*q0+m2*q1+m3)
    poly=X*X+q1*X+q0
    assert L(T(a),D)
    g=(L(T(a),D)*(a*(J(0,X)-ev(X))+X*ev(X)-J(1,X))-L(X,D)*(a*ev(T(a))-J(1,T(a))))
    gg=poly.gcd(g)
    print("nonzero aggregate active clock at",i+1,rear,"two-clock G gcd",gg.degree(),flush=True)
    assert gg.degree()==0
