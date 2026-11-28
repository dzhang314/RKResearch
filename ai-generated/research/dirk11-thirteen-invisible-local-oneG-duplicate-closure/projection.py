"""Independent exact ordinary projection for the one-label clean duplicate."""
import sympy as S
from itertools import combinations
from functools import reduce
X,z,r=S.symbols("X z r")
J4=lambda t:42*t**4-84*t**3+56*t*t-14*t+1
J5=lambda t:(2*t-1)*(66*t**4-132*t**3+84*t*t-18*t+1)
H,rem=S.div(J5(z*X)*J4(z)-J4(z*X)*J5(z),X-1,X)
assert rem==0
H=S.Poly(H,X,domain=S.QQ[z]); hs=[H.nth(i) for i in range(5)]
assert S.expand(hs[4]-132*z**5*J4(z))==0

# Before V: IP(x)=I²P(x)=0 requires old ratios u+v=6x/5, uv=3x²/10.
Y=S.Symbol("Y")
R=(Y-z)*(Y*Y-S.Rational(6,5)*z*Y+S.Rational(3,10)*z*z)
J=[S.integrate(Y**(i+1)*(1-Y)*R,(Y,0,1)) for i in range(6)]
mins=[S.Poly(S.Matrix([[J[i+j] for j in range(3)]for i in rows]).det(),z,domain=S.QQ)
      for rows in combinations(range(4),3)]
assert reduce(lambda a,b:a.gcd(b),mins).is_one

s=S.Symbol("s")
m=X*X+r*X+s
P=X*m; IP=S.integrate(P,X); I2P=S.integrate(IP,X)
d=10*(2*r*r-9*s)
Psi=((8*r*r-42*s)*X-2*r*s)/d
Xi=-X*((r*r-6*s)*X-r*s)/d
assert S.cancel(I2P-Psi*IP-Xi*P)==0
assert S.cancel(d.subs(s,r*r/(r+6))-10*r*r*(2*r+3)/(r+6))==0
# The reduced primitive IP/X² in the monic old quadratic has norm
# s(9s-2r²)/144; verify the two-by-two multiplication determinant.
f=S.rem(S.cancel(IP/X**2),m,X)
fm=S.rem(f*X,m,X)
fn=S.det(S.Matrix([[f.coeff(X,0),fm.coeff(X,0)],[f.coeff(X,1),fm.coeff(X,1)]]))
assert S.cancel(fn-s*(9*s-2*r*r)/144)==0

# After V: the two marked old roots form a monic quadratic factor of H4.
m=X*X+r*X+r*r/(r+6)
M=S.rem(H.as_expr(),m,X)
v=[S.Poly(S.cancel((r+6)**2*S.expand(M).coeff(X,i)),r,z,domain=S.QQ) for i in range(2)]
p0,p1=[S.cancel(vv.as_expr()/k) for vv,k in zip(v,(z,z*z*(r+6)))]
assert [S.Poly(p,r,z).degree_list() for p in (p0,p1)]==[(5,8),(4,7)]
A=S.Poly(S.resultant(p0,p1,r),z,domain=S.QQ)
fs=A.factor_list()[1]
assert A.degree()==55 and sorted((a.degree(),e)for a,e in fs)==[(1,13),(4,3),(30,1)]
assert next(a for a,e in fs if e==13).monic()==S.Poly(z,z,domain=S.QQ)
assert next(a for a,e in fs if e==3).monic()==S.Poly(J4(z),z,domain=S.QQ).monic()
D=next(a for a,e in fs if a.degree()==30)
assert D.is_irreducible
K=D.monic()
a,b=(S.Poly(p,r,domain=S.QQ[z]) for p in (p0,p1))
for n in (3,2,1):
    q,t=a.pdiv(b)
    assert t.degree()==n
    assert b.LC()**(a.degree()-b.degree()+1)*a==q*b+t
    g,t=t.primitive()
    assert S.gcd(S.Poly(g,z,domain=S.QQ),K).is_one
    a,b=b,t
n0,n1=(S.Poly(b.nth(i),z,domain=S.QQ).rem(K) for i in range(2))
assert S.gcd(n1,K).is_one
print("Exact pre-fourth primitive/Hankel exclusion and degree55 clock projection: z^13 J4^3 D30, unique live r ratio",flush=True)
