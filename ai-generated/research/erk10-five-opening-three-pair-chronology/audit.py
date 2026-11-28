"""Exact free-target determinant and early/post-open scalar factors."""
import sympy as S
s,t,j,k,ell,T,w,u,A,B = S.symbols("s t j k ell T w u A B")
N = lambda x,y,z: 3*x**2-4*(y+z)*x+6*y*z
R = lambda x,d,y,z: x**2*N(x,y,z)/(12*d*(d-y)*(d-z))
cleared = N(s,s,k)*N(t,s,j)-N(s,s,j)*N(t,s,k)
assert S.expand(cleared+6*s*(j-k)*(t-s)**2)==0
det = R(s,j,s,k)*R(t,k,s,j)-R(s,k,s,j)*R(t,j,s,k)
assert S.cancel(det-t**2*s**3*(t-s)**2/(24*j*k*(s-j)*(j-k)*(s-k)))==0
print("arbitrary second-target determinant:", S.factor(det))
e2=s*s*ell+2*s*T-t*t
e3=s**3*ell+3*s*s*T-t**3
e4=s**4*ell+4*s**3*T-t**4
assert S.expand(s*s*e2-2*s*e3+e4+t*t*(t-s)**2)==0
print("next target differs only by own-site tap:",S.factor(s*s*e2-2*s*e3+e4))
assert S.expand(w*A-w*B-w*(A-B))==0
assert S.expand(u*A-u*B-u*(A-B))==0
print("opposed weights and opposed raw defects have the same column difference")
assert S.expand((3*s/2)**2-2*s*s-s*s/4)==0
print("single-live-donor cubic contradiction: square difference s^2/4")
