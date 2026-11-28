"""Independent exact arithmetic for the all-open three-pair obstruction."""
from itertools import permutations
import sympy as S

x,z,j,k,c,T,L,a,b = S.symbols("x z j k c T L a b")
q = S.Rational
N = lambda x,i,j: 3*x*x - 4*(i+j)*x + 6*i*j
R = lambda x,d,i,j: x*x*N(x,i,j)/(12*d*(d-i)*(d-j))
primitive = lambda x: S.Matrix([x**2/2,x**3/3,x**4/4])
residual = S.Matrix([[d**i for d in (z,j,k)] for i in range(1,4)]) * \
    S.Matrix([R(x,z,j,k),R(x,j,z,k),R(x,k,z,j)]) - primitive(x)
assert all(S.cancel(t)==0 for t in residual)
numerator = S.factor(N(z,z,k)*N(j,z,j)-N(z,z,j)*N(j,z,k))
assert S.expand(numerator+6*z*(z-j)**2*(j-k))==0
print("cleared cross determinant:", numerator)
det = S.factor(R(z,j,z,k)*R(j,k,z,j)-R(z,k,z,j)*R(j,j,z,k))
expected = j*z**3*(z-j)/(24*k*(j-k)*(z-k))
assert S.cancel(det-expected)==0
print("effective tap determinant:", det)
for p in permutations((a,b,c)):
    sub = dict(zip((z,j,k),p))
    assert S.cancel(det.subs(sub, simultaneous=True)) != 0
print("all six first/second closure orders: nonzero determinant")
E2 = c**2*L+2*c*T-z**2
E3 = c**3*L+3*c**2*T-z**3
E4 = c**4*L+4*c**3*T-z**4
assert S.expand(c*c*E2-2*c*E3+E4+z*z*(z-c)**2)==0
print("leakage cancellation:",S.factor(c*c*E2-2*c*E3+E4))
hilbert = S.Matrix(5,5,lambda i,j:q(1,i+j+2))
assert hilbert.det()==q(1,2**12*3**7*5**5*7**4)
print("shifted Hilbert pivot:",hilbert.det())

J = lambda f,x: S.integrate(f,(y,0,x))
y,p = S.symbols("y p")
assert S.cancel(J(y*(y-z)*(y-j),z)-z**3*(2*j-z)/12)==0
assert S.cancel(J(y*(y-z)*(y-j),j)-j**3*(2*z-j)/12)==0
assert S.expand(((3*p/2)**2-2*p*p)-p*p/4)==0
print("zero-score and zero-pool scalar eliminations: exact")
a1,a2,w,m = S.symbols("a1 a2 w m")
opposed_score_tap = a1*w-a2*w
opposed_mode_tap = a1*m-a2*m
assert S.cancel(opposed_mode_tap-(m/w)*opposed_score_tap)==0
assert opposed_score_tap.subs(w,0)==0
print("zero pool: both donor appearances tracked, including zero scalar score")
