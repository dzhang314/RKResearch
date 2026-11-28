"""Exact scalar arithmetic for the full three-pair chronology exit."""
import sympy as S
a,b,c,z,T,L,p,q,U,V,W,W0 = S.symbols("a b c z T L p q U V W W0")
tapmat = S.Matrix([[a,b],[a*a,b*b]])
assert S.expand(tapmat.det()-a*b*(b-a))==0
assert S.expand(S.Matrix([[U,V],[a*U,b*V]]).det()-U*V*(b-a))==0
print("blind two-label coefficient determinants:",S.factor(tapmat.det()),U*V*(b-a))
assert S.expand(U*W0-V*W0-(U-V)*W0)==0
assert (U*W0-V*W0).subs(W0,0)==0
print("one column difference covers a folded live or score-zero pair")
E2 = a*a*L+2*a*T-z*z
E3 = a**3*L+3*a*a*T-z**3
E4 = a**4*L+4*a**3*T-z**4
assert S.expand(a*a*E2-2*a*E3+E4+z*z*(z-a)**2)==0
print("only new uncalibrated scalar donor equals target:",S.factor(a*a*E2-2*a*E3+E4))
assert S.factor(q**4-2*q**3+q**2)==q**2*(q-1)**2
print("first two distinct forward residuals: second difference",S.factor(q**4-2*q**3+q**2))
