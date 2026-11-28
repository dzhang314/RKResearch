"""Exact scalar replay for the split-host grade-five observer space."""
from itertools import product
import sympy as S
Y,b,c,d,e,k,H=S.symbols("Y b c d e k H")
L4=lambda z:42*z**4-84*z**3+56*z**2-14*z+1
for j in range(4):
    assert S.integrate(Y*(1-Y)*Y**j*L4(Y),(Y,0,1))==0
CL=Y*L4(Y/H)
D=S.expand(S.diff(CL,Y))
expected=lambda z:210*z**4-336*z**3+168*z*z-28*z+1
assert S.expand(D-expected(Y/H))==0
mod=[210,-336,168,-28,1]
assert all(sum(q*a**(4-j)*b**j for j,q in enumerate(mod))%11
           for a,b in product(range(11),repeat=2) if a or b)
print("exact Jacobi moments; derivative quartic projectively rootless modulo 11")
N=(2*(4*b*k*k*Y-4*b*k*k+2*b*k*Y+2*b*k-2*k*Y+Y)/(2*k-1))
assert S.cancel(N.subs(Y,0)+4*b*k)==0
assert S.cancel((N.subs(Y,c)/N.subs(Y,0)+(c-1)*(c-b)/b).subs(c,4*b*k/(2*k-1)))==0
M=Y**2*(Y-c)**2
JM=S.integrate(M,(Y,0,Y))
assert S.factor(JM.subs(Y,c))==c**5/30
PZ=JM-JM.subs(Y,c)*CL/CL.subs(Y,c)
P3=S.cancel(PZ/(Y*(Y-c)))
assert S.cancel(-P3.subs(Y,c)/P3.subs(Y,0)-expected(c/H))==0
assert S.factor(S.solve((c-d)*(c-e)-expected(c/H)*d*e,e)[0]-
       c*(c-d)/(c+(expected(c/H)-1)*d))==0
JG=S.integrate((Y-d)*S.diff(M,Y)/4,(Y,0,Y))
PG=JG-JG.subs(Y,c)*CL/CL.subs(Y,c)
assert S.cancel(PZ+4*PG-(Y-d)*M)==0
print("head cofactor quotient, both nominal primitives, and exact Möbius formula")
