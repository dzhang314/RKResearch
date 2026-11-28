"""Exact ancillary factors for three or more high endpoint copies."""
import sympy as S
a,t,x,w,S0,T=S.symbols("a t x w S0 T", nonzero=True)
assert [(r,m,11-r-m) for r in range(3,11) for m in range(7,11) if 11-r-m>=0] == [(3,7,1),(3,8,0),(4,7,0)]
print("remaining counts: triple endpoint with or without one interior pair; four endpoints needs all singles")
g=a*a*S0/3+t*(t-2*a/3)*T
k=5*a**3*S0/8+t*(t*t-a*a/2)*T
assert S.expand(g.subs(t,3*a/2)-a*a*(S0/3+5*T/4))==0
assert S.expand(k.subs(t,3*a/2)-a**3*(5*S0+21*T)/8)==0
D=S.det(S.Matrix([[S.Rational(1,3),S.Rational(5,4)],[5,21]]))
assert D==S.Rational(3,4)
print("intervening a-row reduced determinant:",D)
S_first=w*t*t/(2*a)
assert S.cancel(((a**3*S_first-w*t**4/4)/(a*a*S_first/2)).subs(t,3*a/2)+a/4)==0
print("first live singleton k/Q equals -a/4")
e2=a*S0+t*T-w*x*x/2
e3=a*a*S0+t*t*T-w*x**3/3
e4=S.Rational(9,8)*a**3*S0+t**3*T-w*x**4/4
assert S.expand(4*t*t*e2-12*t*e3+8*e4-a*(2*t-3*a)**2*S0+2*w*x*x*(x-t)**2)==0
print("next live singleton corrected cubic square:",S.factor((4*t*t*e2-12*t*e3+8*e4).subs(t,3*a/2)))
