#!/usr/bin/env python3
"""Exact independent algebra for the conditional seven-opening pure-high obstruction."""
import sympy as S
Q=S.Rational
r,s,T,U,J,z,t,X=S.symbols("r s T U J z t X")
eq=[
 T+U+r*J-s**2/2,
 Q(2,3)*T+U+r**2*J-s**3/3,
 (3-2*r)*(U+r**2*(3-2*r)*J)-2*(s-1)*T,
 (3-2*r)*(U+r**3*J-s**4/4)+(3-2*r+(r-1)*(s-1))*T/2,
]
A,m=S.linear_eq_to_matrix(eq,T,U,J)
det=S.factor(A.row_join(m).det())
assert det==r*s**2*(r-1)*(r-s)**2*(2*r-3)*(s-1)/2
print("fifth-row augmented determinant:",det)
for R,v,expected in [(r,0,(0,0,0)),(r,1,(Q(1,2),0,0)),
                     (r,r,(r**2*(3-2*r)/2,r**2*(r-1),0)),
                     (Q(1,2),0,(0,0,0)),(-1,1,(Q(1,2),0,0)),
                     (2,2,(6*J-2,4-8*J,J))]:
    got=next(iter(S.linsolve([f.subs({r:R,s:v},simultaneous=True)for f in eq],T,U,J)))
    assert all(S.cancel(x-y)==0 for x,y in zip(got,expected)),(R,v,got,expected)
    print("fifth row at (r,s) =", (R,v),":",got)
m5=S.Matrix([s**2/2,s**3/3,s**4/4])
M=S.Matrix([[1,1,Q(3,2)],[Q(2,3),1,Q(9,4)],[Q(1,2),Q(9,8),Q(27,8)]])
sol=list(map(S.factor,M.inv()*m5))
assert sol==[s**2*(2*s-3)**2/2,-2*s**2*(s-1)*(5*s-9)/3,4*s**2*(s-1)*(2*s-3)/9]
assert {p:tuple(j.subs(s,p)for j in sol)for p in (0,1,Q(3,2))}=={
    0:(0,0,0),1:(Q(1,2),0,0),Q(3,2):(0,Q(9,8),0)}
print("proportional V,CV: fifth-row starter coefficient",sol[0])
M=S.Matrix([[1,1,2],[Q(2,3),1,4],[(2-s)/2,1,8]])
assert S.factor(M.det())==2-s
assert S.cancel((M.inv()*m5)[0]-s**2*(2-s)/2)==0
print("one repetition and sixth clock: starter coefficient", s**2*(2-s)/2)
w1=S.integrate(X*(X-2)*(X-t),(X,0,z))/((1-2)*(1-t))
wt=S.integrate(X*(X-1)*(X-2),(X,0,z))/(t*(t-1)*(t-2))
v=z*(12*z*z-45*z+40)/(15*(z-2)**2)
T0=S.integrate(X*(X-1)*(X-2)*(X-t),(X,0,z))
assert S.cancel(T0+z**2*(15*t*(z-2)**2-z*(12*z*z-45*z+40))/60)==0
end=S.factor((w1+t*t*(t-2)**2*wt).subs(t,v))
assert end==z**3*(3*z*z-15*z+20)/15
assert S.discriminant(3*z*z-15*z+20,z)==-15
print("post-quadrature weighted direction:",end)
