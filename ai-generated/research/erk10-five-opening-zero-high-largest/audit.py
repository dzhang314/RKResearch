"""Symbolic ingress replay; no numerical or finite-field search."""
import sympy as S

a,b,c,z,r,H,X,Y,w = S.symbols("a b c z r H X Y w")
d=3*b-2*c
Z=lambda t:S.cancel(t)==0
assert Z(r**2-2*r**3+r**4-r**2*(r-1)**2)
print("two actual forward residual rows: r^2 second difference = r^2*(r - 1)^2")
H5=S.Matrix([[S.Rational(1,i+j+1) for j in range(5)] for i in range(1,6)])
print("shifted Hilbert determinant:",H5.det(),S.factorint(S.denom(H5.det())))
assert H5.det()==S.Rational(1,67212633600000)
assert set(S.factorint(S.denom(H5.det()))) <= {2,3,5,7}
assert Z(S.integrate(X*(1-X),(X,0,1))/H-S.Rational(1,6)/H)
assert Z(S.integrate(X*(1-X)**2,(X,0,1))/H**2-S.Rational(1,12)/H**2)
print("normalized half/zero moment obstructions: 1/6, 1/12")

F=lambda r,s,z:-z*z/4+(r+s)*z/3-r*s/2
beta=(4*b-6*a)/(3*a)
phiB=b*b/a-2*a
hB=-a*b*b/4
# The first normal row has one positive-degree donor, the high zero.
assert Z(a*(b*b/(2*a))-b*b/2)
assert Z(a*a*(b*b/(2*a))-b**3/3-beta*hB)
assert Z(a**3*(b*b/(2*a))-b**4/4-phiB*hB)
# Next normal row: exact first two taps, third primitive and Kh read.
Ac=c*c*d/(2*a*b); Bc=c*c*(c-b)/b**2
hc=-a*c*c*d/(4*b)
assert Z(a*Ac+b*Bc-c*c/2)
assert Z(a*a*Ac+b*b*Bc-c**3/3-beta*hc)
assert Z(hc+a*a*Ac/2)
phiC=c*c*F(a,b,c)/hc+(a+b)*beta
assert Z(hc*phiC-(a**3*Ac+b**3*Bc-c**4/4))
psi=b*(z-b)/d
assert Z(psi.subs(z,c)*hc-Bc*hB)
phi=phiB+(z-b)*(phiC-phiB)/(c-b)
P,Q,D=-a*c/2,a*(2*c-b)/(4*b),-c+a*(2*c-b)/(2*b)
eta=-a/(2*(a-b)*(a-c))
for y,u,h in [(0,0,0),(a,-a*a/2,0),(b,0,hB),(c,0,hc)]:
    assert Z(P*y+Q*y*y+D*u-h)
    assert Z(eta*y*(y-b)*(y-c)-u)
L=5*b*c-3*b*z-4*c*c+3*c*z
N=b*c+3*b*z-2*c*c
M=-3*z*z+4*(b+c)*z-6*b*c
T=(2*c-b)*z-3*b*c
assert Z((phi-(b+c)*beta-1/eta)*3*a*d-b*L)
assert Z((psi-Q*beta-D)*3*d-N)
assert Z(12*F(b,c,z)-M)
assert Z((P/2+Q*z/3)*12*b-a*T)
assert Z(L*T-N*M-9*b*(z-b)*(z-c)**2)
assert Z(L.subs(z,b)-(2*c-b)*d)
assert Z(N.subs(z,b)-(b+c)*d)
assert Z(L.subs(z,c)-c*(2*b-c))
assert Z(N.subs(z,c)-2*c*(2*b-c))
print("actual one-active-ghost head before fourth distinct row: cleared determinant",S.factor(L*T-N*M))
print("inactive repeat checks: b factors (2c-b,b+c); c factor 2b-c")
