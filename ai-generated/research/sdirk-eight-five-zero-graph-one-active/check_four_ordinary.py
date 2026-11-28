"""Exact Gaussian rear projection with a single canceled live off clock."""
import sympy as S
x,y,v=S.symbols("x y v")
def L(x): return 70*x**4-140*x**3+90*x**2-20*x+1
Q=v*v-2*v-1
J,rem=S.div(L(y)-L(x),y-x,y)
assert rem==0
for phase,numer in [("arithmetic",1+2*v),("star",3-v)]:
    denom=1+v
    K=sum(c*(x*numer)**(3-j)*denom**j for j,c in enumerate(S.Poly(J,y).all_coeffs()))
    bound=S.resultant(Q,S.resultant(L(x),K,x),v)
    assert bound
    print(phase,"nonzero resultant",bound,"prime factors",S.factorint(abs(bound)))
