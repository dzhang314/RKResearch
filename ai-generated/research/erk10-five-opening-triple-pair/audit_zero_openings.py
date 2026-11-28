"""Exact exceptional scalar coefficient with zero first a-score."""
import sympy as S
a,b,U,w,T = S.symbols("a b U w T")
H = -b*U/2
u=b*T-w*a*a/2
g=b*b*T-w*a**3/3
assert S.expand(g-b*u-w*a*a*(b/2-a/3))==0
Q=b*a*a*w/(4*U)
assert S.expand(U*Q-b*b*T/2-H*u/U)==0
k=a*a*b*b*w/2-a**4*w/4
L=S.cancel((k/Q)*b*b/(2*U))
assert S.expand(L-b*(2*b*b-a*a)/2)==0
target=b*(a-b)*(a-2*b)/2
assert S.expand((L-target).subs(a,3*b/2))==0
print("zero-first-a exceptional quotient again equals",S.factor(target))
