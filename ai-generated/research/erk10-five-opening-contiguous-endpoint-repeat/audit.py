"""Independent arithmetic and count for the contiguous endpoint block."""
import sympy as S
from fractions import Fraction
q=S.symbols("q")
counts=[(r,m,11-r-m) for r in range(2,11) for m in range(7,11)
        if 0<=11-r-m]
assert counts==[(2,7,2),(2,8,1),(2,9,0),(3,7,1),(3,8,0),(4,7,0)]
print("paid physical counts (endpoint multiplicity, distinct labels, interior excess):",counts)
H=S.Matrix(5,5,lambda i,j:S.Rational(1,i+j+2))
assert H.det()==S.Rational(1,2**12*3**7*5**5*7**4)
print("shifted Hilbert determinant:",H.det())
assert S.expand(q**4-2*q**3+q**2-q*q*(q-1)**2)==0
print("first-two-forward-coordinate second difference:",q*q*(q-1)**2)
a,t,w,T=S.symbols("a t w T")
p2=2*a*T-w*t*t
p3=3*a*a*T-w*t**3
p4=4*a**3*T-w*t**4
assert S.expand(3*a*p2-2*p3-w*t*t*(2*t-3*a))==0
assert S.expand(2*a*a*p2-p4-w*t*t*(t*t-2*a*a))==0
assert Fraction(3,2)**2-Fraction(2)==Fraction(1,4)
print("single scalar donor after paid Y,Y²,Y³ has incompatible ratio square: 1/4")
