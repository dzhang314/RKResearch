"""Four exact ordinary projections for pure support and one canceled off clock."""
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
for i in (0,1):
 D=2+i*U
 a=1+2*U
 for rear in ('star','arith'):
    W=(2-V) if rear=='star' else 2*V
    s=D-1-V;t=D-1-W
    assert D and a!=s and a!=t and s!=t
    P=(X-a)*(X-s)*(X-t)
    m=[sum((c*D**j*C(1,j+1) for (j,),c in (P*X**i).items()),K.zero) for i in range(5)]
    m0,m1,m2,m3,m4=m
    H0=m0*(m2*m4-m3*m3)-m1*(m1*m4-m3*m2)+m2*(m1*m3-m2*m2)
    # First zero may be silent only in the already excluded four-label
    # ordinary case; with five ordinary labels this is a true 3-clock mask.
    assert H0
    print('canceled chart active clock at',i+1,rear,'nonzero mapped third Hankel')
