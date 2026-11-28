"""Exact chronology-specific triple-pair elimination factors."""
import sympy as S
a,b,z,t,A,B,w,d,al = S.symbols("a b z t A B w d al")
q = S.Rational

nodal = z**4/4-(a+b)*z**3/3+a*b*z*z/2
assert S.expand(nodal.subs(a,2*b)-z*z*(z-2*b)**2/4)==0
assert S.expand(nodal.subs(b,2*a)-z*z*(z-2*a)**2/4)==0
print("repeated first exact-cubic target: second target double-root factor")

# Chronology a,b,a. No division by w of the second a.
al1=b*(a-b)/a
U1=a*al1-b*b/2
S1=2*U1*t/(a*a)
u1=a*S1+b*t-w*a*a/2
Va1=-2*u1/(a*a)
k1=a**3*S1+b**3*t-w*a**4/4
lam=b*(a-b)*(a-2*b)/2
assert S.cancel(k1+a**4*Va1/4-lam*t)==0
test=2*(a*al-b*b/2)/3+b*(b-2*a/3)
assert S.expand(test-2*(a*al+b*b-a*b)/3)==0
print("a,b,a exceptional quotient:",S.factor(lam))

# Chronology b,a,a. The shift by al*w avoids dividing by the second weight.
U=b*al-a*a/2
G=b*b*al-a**3/3
H=-b*b*al/2
M=S.Matrix([[a,b,-U],[a*a,b*b,-G],[U,-b*b/2,-H]])
D=-a*a*b*(a**3-a*a*b-2*a*al*b+3*al*b*b)/6
assert S.expand(M.det()-D)==0
al2=a*a*(a-b)/(b*(2*a-3*b))
U2=S.factor(U.subs(al,al2))
S2=-a*(2*a-3*b)*d/(6*(a-b))
T2=-(a**3-6*a*al2*b+6*al2*b*b)*d/(6*b*(a-b))
assert all(S.cancel(f)==0 for f in M.subs(al,al2)*S.Matrix([S2,T2,d]))
k0=b**3*al2-a**4/4
L2=a*a*(a-2*b)*(a-b)/(2*(2*a-3*b))
assert S.cancel(a**3*S2+b**3*T2-k0*d-L2*S2)==0
assert S.cancel(L2*b*b/(2*U2)-lam)==0
print("b,a,a exceptional determinant:",S.factor(D))
print("b,a,a quotient after h transfer:",S.factor(lam))

# Ordinary target comparison, arbitrary denominator-cleared group mean.
bTap=z*z*(2*z-3*a)/(6*b*(b-a))
aTap=z*z*(3*b-2*z)/(6*a*(b-a))
assert S.cancel(a*aTap+b*bTap-z*z/2)==0
assert S.cancel(a*a*aTap+b*b*bTap-z**3/3)==0
k=a**3*aTap+b**3*bTap-z**4/4
assert S.cancel(k-lam*bTap+z*z*(z-a)**2/4)==0
print("both exceptional next-target residuals:",S.factor(k-lam*bTap))
