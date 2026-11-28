"""Exact scalar audit of the raw fourfold-block argument."""
import sympy as S
a,t,s,A,T,w,M = S.symbols("a t s A T w M")
q = S.Rational
change = S.Matrix([[-a*a/2,a],[-a**3/3,a*a]])
assert S.expand(change.det()+a**4/6)==0
oldU=a*M-a*a*w/2
oldG=a*a*M-a**3*w/3
oldH=-a*a*M/2
oldK=a**3*M-a**4*w/4
oldKG=-a**3*M/3
assert S.expand(a*oldU-q(3,2)*oldG-oldH)==0
assert S.expand(oldK+q(3,4)*oldKG-q(3,4)*a*oldG)==0
print("two-dimensional change determinant:",S.factor(change.det()))
A0=w*t*t/(2*a)
k0=a**3*A0-w*t**4/4
kg0=a**3*A0/6
assert S.expand(kg0.subs(t,3*a/2)-3*a**4*w/16)==0
assert S.expand(k0.subs(t,3*a/2)+9*a**4*w/64)==0
assert S.expand((k0+q(3,4)*kg0).subs(t,3*a/2))==0
print("first singleton at 3a/2: defects (-9/64,3/16)·w·a^4")
U=a*A+t*T-w*a*a/2
G=a*a*A+t*t*T-w*a**3/3
K=a**3*A+t**3*T-w*a**4/4
H=a*U-q(3,2)*G
KG=a*H+a**3*A/6
F=K+q(3,4)*KG-q(3,4)*a*G
assert S.expand(F.subs(t,3*a/2)-9*a**3*T/32)==0
print("feedback into an intervening a-copy:",S.factor(F.subs(t,3*a/2)))
E2=2*(a*A+t*T)-s*s
E3=3*(a*a*A+t*t*T)-s**3
E4=9*a**3*A+8*t**3*T-2*s**4
assert S.expand(2*t*t*E2-4*t*E3+E4-a*(2*t-3*a)**2*A+2*s*s*(s-t)**2)==0
print("next live singleton obstruction:",S.factor((2*t*t*E2-4*t*E3+E4).subs(t,3*a/2)))
