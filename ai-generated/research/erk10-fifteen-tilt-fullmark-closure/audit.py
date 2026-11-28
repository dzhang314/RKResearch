"""Exact scalar and raw-projection replay for the dense dirt closure."""
from itertools import product
import sympy as S
R=S.Rational
x,c=S.symbols("x c")
J=lambda f:S.integrate(f,(x,0,1))
L=42*x**4-84*x**3+56*x*x-14*x+1
assert all(J(x*(1-x)*L*x**j)==0 for j in range(4))
mat=S.Matrix([[J(x*(1-x)*(x-c)*x**(i+j)) for j in range(4)] for i in range(4)])
assert S.factor(mat.det()-L.subs(x,c)/2240421120000)==0
assert all((9*a**4+4*a**3*b+a*a*b*b+8*a*b**3+b**4)%11
           for a,b in product(range(11),repeat=2) if a or b)
print("Jacobi quartic moments, exact shifted determinant and projectively rootless mod 11")
for m in range(7,11):
    cases=[(r,e,10-m-r-e) for r in range(11-m) for e in range(11-m-r)]
    print("m=%s (high zeros, endpoint excess, ordinary excess):"%m,cases)

# A nonzero deleted score, signed model-blind survivor, and scaled live one.
a,b=R(1,3),R(2,3)
C=S.diag(a,a,a,b,1); y=S.eye(5)-C
w=S.Matrix([[1,-2,2,0,1]])
B=S.zeros(5)
for i in range(3):
    B[4,i]=(1-a)*w[0,i]
d=S.Matrix([2,2,1,0,0]); e=S.eye(5)[:,3]
P=S.eye(5)-d*S.eye(5)[0,:]/2-e*S.eye(5)[3,:]
assert P*P==P and P*C==C*P and w*P==w and w*B==w*y
ind=[1,2,4]; Scl=S.diag(1,R(1,2),1)
Jp=S.eye(5)[:,ind]*Scl; Rq=Scl.inv()*S.eye(5)[ind,:]
Bq=Rq*P*B*Jp; Cq=Rq*C*Jp; wq=w*Jp
assert wq==S.Matrix([[-2,1,1]]) and wq*Bq==wq*(S.eye(3)-Cq)
assert Rq*P*S.ones(5,1)==S.Matrix([0,1,1])
for n in range(5):
    for letters in product(range(2),repeat=n):
        W=S.eye(5); Wq=S.eye(3)
        for z in letters:
            W=W*[B,C][z]
            Wq=Wq*[Bq,Cq][z]
        assert w*W*d==w*W*e==S.zeros(1,1)
        assert w*W==wq*Wq*Rq*P
print("all 31 raw words through four preserved by two earliest-pivot cuts; masked survivor kept with score -2")

# Endpoint-blind feedback and corrected exact cubic square.
a,t,z,S0,T0,W0=S.symbols("a t z S T W")
assert S.factor((S0/3+5*T0/4).coeff(S0)*(5*S0+21*T0).coeff(T0)
                -(S0/3+5*T0/4).coeff(T0)*(5*S0+21*T0).coeff(S0))==R(3,4)
lhs=2*t*t*(2*(a*S0+t*T0))-4*t*(3*(a*a*S0+t*t*T0))+(9*a**3*S0+8*t**3*T0)
assert S.expand(lhs-a*(2*t-3*a)**2*S0)==0
assert S.expand(2*t*t*W0*z*z-4*t*W0*z**3+2*W0*z**4-2*W0*z*z*(z-t)**2)==0
print("endpoint-blind tracking minor and corrected cubic square checked")
