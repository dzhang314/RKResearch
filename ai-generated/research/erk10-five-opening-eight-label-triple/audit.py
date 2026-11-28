"""Independent rational-function replay of the three head routes and raw collapse."""
import sympy as S
a,b,c,d,z,y,E,F,G,L,A,T,w = S.symbols("a b c d z y E F G L A T w")
q=S.Rational
Fa=lambda r,s,z:-z*z/4+(r+s)*z/3-r*s/2
det=lambda m,n,P,Q,r,s:S.factor(m*(P/2+Q*z/3)-n*Fa(r,s,z))

# Head a,a,b: all a donors h=-au/2-a³w/4 up to b.
beta=-q(2,3)
phi=-a-(b-a)*(z-a)/(2*b-3*a)
psi=-a*(z-a)/(2*b-3*a)
P,Q,D=-a*b/2,(2*b-a)/4,-a/2
D1=det(phi-(a+b)*beta,psi-Q*beta-D,P,Q,a,b)
assert S.cancel(D1-a*(z-a)*(z-b)**2/(4*(3*a-2*b)))==0
print("a,a,b next-singleton determinant:",D1)
u=a*A+b*T-a*a*w/2
g=a*a*A+b*b*T-a**3*w/3
k=a**3*A+b**3*T-a**4*w/4
assert S.expand(k+a*a*u/2-3*a*g/2-b*(b-a)*(b-a/2)*T)==0
assert S.expand((a*u-3*g/2).subs(b,a/2)-(-a*a*A/2+a*a*T/8))==0
assert S.expand(-a*a*A/2+a*(-a*T/4)-(-a*a*A/2-a*a*T/4))==0
print("a,a,b,a at b=a/2: the two h-reads differ by 3*a^2*T/8")

# Head a,b,a: actual a2 tap ratio, then the next singleton determinant.
beta=(4*b-6*a)/(3*a)
phiB=b*b/a-2*a
ratio=2*a*(a-b)/(b*(3*b-2*a))
phiA=-a-2*b*(b*b-a*a/2)*ratio/(a*a)
psiA=S.cancel((-a*b*b/4)*ratio/(-a*a/2))
assert S.cancel(phiA-((a+b)*beta-b*(a-2*b)/(3*(3*b-2*a))))==0
assert S.cancel(psiA-b*(a-b)/(3*b-2*a))==0
phi=phiB+(z-b)*(phiA-phiB)/(a-b)
psi=(z-b)*psiA/(a-b)
P,Q,D=-a*a/2,a*(2*a-b)/(4*b),-a*(3*b-2*a)/(2*b)
assert S.cancel((P*a+Q*a*a)-D*a*a/2)==0
assert S.cancel(D*(a+b*ratio)+a*a/2)==0
assert S.cancel(P*b+Q*b*b+a*b*b/4)==0
D2=det(phi-(a+b)*beta,psi-Q*beta-D,P,Q,a,b)
assert S.cancel(D2+b*(z-a)**2*(z-b)/(4*(2*a-3*b)))==0
assert S.factor(S.Matrix([[a*a/3,b*(b-2*a/3)],[a**3/2,b*(b*b-a*a/2)]]).det()-a*a*b*(b-a)*(2*b-a)/6)==0
print("a,b,a next-singleton determinant:",D2)
assert S.cancel(phi.subs(b,a/2)+3*a/2+z/2)==0
assert S.cancel(psi.subs(b,a/2)-a/2+z)==0
assert S.cancel((Fa(a,b,z)).subs(b,a/2)+(z-a)**2/4)==0

# Head a,b,c: evaluate the next singleton comparison and potential a-copy.
hc=a*c*c*(2*c-3*b)/(4*b)
phiC=c*c*Fa(a,b,c)/hc+(a+b)*beta
phi=S.factor(phiB+(z-b)*(phiC-phiB)/(c-b))
psi=-b*(z-b)/(2*c-3*b)
P,Q,D=-a*c/2,a*(2*c-b)/(4*b),-c+a*(2*c-b)/(2*b)
eta=-a/(2*(a-b)*(a-c))
assert S.cancel(P*a+Q*a*a-D*a*a/2)==0
assert S.cancel(P*b+Q*b*b+a*b*b/4)==0
assert S.cancel(P*c+Q*c*c-hc)==0
D3=det(phi-(b+c)*beta-1/eta,psi-Q*beta-D,P,Q,b,c)
assert S.cancel(D3-b*(z-b)*(z-c)**2/(4*(3*b-2*c)))==0
print("a,b,c next-singleton determinant:",D3)
M=S.Matrix([[a*a/3+beta*a*a/2,b*(b-2*a/3),c*(c-2*a/3)],
            [a**3/2+phi.subs(z,a)*a*a/2,b*(b*b-a*a/2),c*(c*c-a*a/2)],
            [psi.subs(z,a)*a*a/2,-a*b*b/4,hc]])
D4=-a*a*b*b*c*(a-b)*(a-c)**2*(b-c)/(4*(3*b-2*c))
assert S.cancel(M.det()-D4)==0
print("a,b,c,a2 exact coefficient determinant:",S.factor(D4))
delta=3*b-2*c
numphi=6*a*a*b-4*a*a*c+a*b*b-a*b*c-4*b**3+3*b*b*c
cleared=S.Matrix([[2*a*(b-a),b*(3*b-2*a),c*(3*c-2*a)],
 [a**3*delta-a*numphi,delta*b*(2*b*b-a*a),delta*c*(2*c*c-a*a)],
 [2*a*a*b*b*(a-b),-a*b**3*delta,-a*c*c*delta**2]])
assert all(S.cancel(x)==0 for x in cleared-S.diag(3,2*delta,4*b*delta)*M)
assert S.expand(cleared.det()+6*a*a*b**3*c*delta*(a-b)*(a-c)**2*(b-c))==0
print("a,b,c,a2 denominator-cleared determinant checked")

# Terminal raw collapse: common old chart, large node a=2b.
V=y*y*(y-a)**2
W=y*(y-b)*(y-a)*(y-c)
I=lambda f:S.integrate(f,(y,0,z))
assert S.expand((S.diff(V,y)/4-y*(y-b)*(y-a)).subs(a,2*b))==0
assert S.expand((4*I(W)-(z-c)*V.subs(y,z)+I(V)).subs(a,2*b))==0
assert S.cancel(1/((b-c)*(b-d))+1/((c-b)*(c-d))+1/((d-b)*(d-c)))==0
print("blind primitive transfer and three-site cofactor checked without score divisions")
