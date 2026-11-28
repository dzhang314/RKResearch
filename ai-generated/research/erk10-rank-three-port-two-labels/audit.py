#!/usr/bin/env python3
"""Exact compatibility determinants for both rank-three two-dirty-pair chronologies."""
import sympy as S
s,a,b,k0=S.symbols('s a b k')
one=S.S.One
e=-one/2
d=k0-s*s/2
rho=k0*e/d
l=(k0-s**3/3)/d
A=S.Matrix([[e,d],[one/3,s*(s-2*one/3)]])
assert S.cancel(A.det()-(s*(one-s)-k0)/3)==0
A=S.Matrix([[e-rho,d-rho*s],[one-l,s*(s-l)]])
assert S.cancel(A.det()+s**2*(-s**3+s**2+2*s*k0-3*k0)/(3*(-s**2+2*k0)))==0
p,q,y,v=S.symbols('p q y v')
rows=[y+p*v-q*q/2,2*p*y/3+p*p*v-q**3/3,p*p*y/2+p**3*v-q**4/4]
assert S.expand(-p*p*rows[0]/2+3*p*rows[1]/2-rows[2]-q*q*(p-q)**2/4)==0
print("singleton/singleton normalized pressure:",q**2*(p-q)**2/4)
for early in (one,s):
    k=S.factor(s*(1-s) if early==one else s*s*(s-1)/(2*s-3))
    f=S.factor(k-s*s/2)
    lam=S.factor((k-s**3/3)/f)
    rho=S.factor(k*e/f)
    d0={one:e,s:f}
    T0={one:S.S.Zero,s:k*e}
    G0={one:-one/4,s:k-s**4/4}
    def slopes(x,defect,isfirst):
        m1=x*x/2+defect
        m2=x**3/3+(S.Rational(2,3) if x==one else lam)*defect
        Y=S.factor((m2-m1)/(s*(s-1)))
        X=S.factor(m1-s*Y)
        T=X*e if isfirst or x==one else rho*defect-Y*f
        G=X+s**3*Y-x**4/4
        return tuple(S.factor((z/defect-o[x]/d0[x])/(defect-d0[x]))
                     for z,o in [(T,T0),(G,G0)])
    late=s if early==one else one
    L=slopes(early,a,True)
    R=slopes(late,b,False)
    determinant=S.factor(L[0]*R[1]-L[1]*R[0])
    expected=s*(s-1)/(12*a*b) if early==one else -s*(s-1)*(2*s-3)/(12*a*b)
    assert S.cancel(determinant-expected)==0
    print("first repeat",early,"initial tap",k,"slopes",L,R,"determinant",determinant)
