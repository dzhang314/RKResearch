"""Separate exact QQ matrix and quadratic-resultant coordinate checks."""
from random import Random
import sympy as S
rng=Random(13017)
for _ in range(8):
    n=7
    A=S.Matrix(n,n,lambda i,j:S.Rational(rng.randint(-30,30),rng.randint(1,13)) if i>=j else 0)
    CC=[S.Rational(i,29)for i in rng.sample(range(-17,19),n)]
    C=S.diag(*CC)
    Y=S.diag(*(1-c for c in CC))
    N=A.T
    Ccm=(C*A-A*C-A*A).T
    rev=Y*N-N*Y-N*N
    assert rev==Ccm
    ri=list(reversed(range(n)))
    Ya=Y.extract(ri,ri);Na=N.extract(ri,ri)
    # Old reverse 0,1,2, first ghost 3, V=4, first middle=5,
    # B=6. Only V and B can have nonzero inputs in this test.
    u=S.Matrix([0,0,0,0,S.Rational(2,3),0,S.Rational(-3,8)])
    actual=((Ya*Na-Na*Ya-Na*Na)*u)[5]
    expected=(Ya[5,5]-Ya[4,4]-Na[5,5]-Na[4,4])*Na[5,4]*u[4]
    assert actual==expected
a,b,c,d,e,f,x=S.symbols('a b c d e f x')
assert S.expand(S.resultant(a*x*x+b*x+c,d*x*x+e*x+f,x)-
                ((a*f-c*d)**2-(a*e-b*d)*(b*f-c*e)))==0
p,q,z,J0,J1,J2,J3=S.symbols('p q z J0 J1 J2 J3')
D=(q*q*J1+p*q*J2+p*p*J3)+(q*q*J2+p*q*J3)*x+q*q*J3*x*x
F=lambda y:J0+J1*y+J2*y*y+J3*y*y*y
assert S.expand(((x-z)*D-q*q*(F(x)-F(z))).subs(p,q*z))==0
print('QQ reflection and literal transpose commute in 8 nonsymmetric examples; symbolic quadratic resultant and divided difference agree.')
