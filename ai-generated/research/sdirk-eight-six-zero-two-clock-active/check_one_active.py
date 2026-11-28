"""Six zeros, two physical off clocks with one varying group and one active clock."""
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
def det(M):
    a,b,c=M
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
for i in (0,1):
 D=2+i*U
 a=1+2*U
 P=[1+U,-2-U,K.one]
 ev=lambda z:sum((p*z**j for j,p in enumerate(P)),T.zero)
 J=lambda k,z:sum((p*z**(j+k+1)*C(1,j+k+1) for j,p in enumerate(P)),T.zero)
 assert J(0,T(a))==ev(T(a))
 def L(t):return 70*t**4-140*D*t**3+90*D*D*t*t-20*D**3*t+D**4
 assert L(a)
 def I(P0):return sum((c*D**j*C(1,j+1) for (j,),c in P0.items()),K.zero)
 for rear in ('star','arith'):
    W=(2-V) if rear=='star' else 2*V
    s=D-1-W;t=D-1-V
    assert D and a!=s and a!=t and s!=t
    A0=(X-a)*(X-s)*(X-t)
    m=[I(A0*X**j) for j in range(5)]
    H=det([[m[j+k] for k in range(3)] for j in range(3)])
    assert H # at least three remaining unknown nodes have nonzero mass
    p=(2*W*V+1+2*W-W*W)/(2*V)
    R0=p*(A0//(X-s))-V*(A0//(X-t))
    r=[I(R0*X**j) for j in range(4)]
    M=[[m[0],m[1],m[2]],[m[1],m[2],m[3]],[r[0],r[1],r[2]]]
    E=det(M)
    print(i,rear,"three-coefficient pivot",bool(E),flush=True)
    assert E
    rhs=[-m[3],-m[4],-r[3]]
    ns=[]
    for k in range(3):
      U0=[z[:] for z in M]
      for j in range(3):U0[j][k]=rhs[j]
      ns.append(det(U0)/E)
    assert all(sum((M[i][k]*ns[k] for k in range(3)),K.zero)==rhs[i] for i in range(3))
    q=X**3+ns[2]*X**2+ns[1]*X+ns[0]
    Hgate=L(a)*(a*(J(0,X)-ev(X))+X*ev(X)-J(1,X))-L(X)*(a*ev(T(a))-J(1,T(a)))
    hh=q.gcd(Hgate)
    print('forward gate gcd degree',hh.degree(),flush=True)
    assert hh.degree()==0
