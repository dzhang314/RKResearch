"""Two varying off groups at six zeros, all off weights silent: duplicate terminal ordinary clock."""
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

S0,D=ring('D',K)
R,X=ring('X',S0.to_domain())
Y=lambda t:R(S0(t))
def I(P):
    return sum((q*D**i*C(1,i+1) for (i,),q in P.items()),S0.zero)
def det(M):
    a,b,c=M
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
a=1+2*U
T10=D-1;T9=D-1-V
for rear in ('star','arith'):
 W=(2-V) if rear=='star' else 2*V
 T8=D-1-W
 # Case a=T10: the other four ordinary labels do not duplicate a.
 P3=(X-Y(T8))*(X-Y(T9))*(X-Y(T10))
 m=[I(P3*X**k) for k in range(5)]
 H=det([[m[i+j] for j in range(3)] for i in range(3)])
 h0=H.evaluate(D,1+a)
 print(rear,'first equals terminal ordinary:',bool(h0),flush=True)
 assert h0
 # Otherwise all four known clocks are distinct; 5th via nonzero pivot.
 P4=P3*(X-Y(a))
 m0,m1,m2,m3=[I(P4*X**k) for k in range(4)]
 Z=(m0*m2-m1*m1).gcd(m0*m3-m1*m2)
 print('ordinary gcd raw',Z.degree(),flush=True)
 for guard in [D,m0,T8-a,T9-a,T10-a]:
    while True:
      gg=Z.gcd(guard)
      if gg.degree()==0:break
      Z=Z//gg
 print('ordinary gcd guarded',Z.degree(),str(Z.as_expr())[:1100],flush=True)
 assert Z.degree()==0
