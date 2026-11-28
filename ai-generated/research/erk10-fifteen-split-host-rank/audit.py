"""Exact necessary row calculus for the rank-two split-host branch."""
from itertools import product
import sympy as S

t,z,k,X=S.symbols("t z k X")
E=lambda a:S.Matrix([[a**i for i in range(1,5)]])
J=lambda a:S.Matrix([[a**(i+1)/S.Integer(i+1) for i in range(1,5)]])
det=lambda rows:S.factor(S.Matrix.vstack(*rows).det(method="domain-ge"))
M=S.Matrix.vstack(J(1),J(t),E(1),E(t))
D0=S.factor(M.det())
assert D0==-t**4*(t-1)**4/120 or S.expand(D0+t**4*(t-1)**4/120)==0
coef=[]
for i in range(4):
    N=M.copy(); N[i,:]=J(z)
    coef.append(S.factor(N.det()/D0))
A,B,U,V=coef
expr=2*z**4*(z-t)**3*(z-1)**3*(t*t+t+(t*t-4*t+1)*z)/(t**3*(1-t)**5)
assert S.cancel(A*(z-1)*V+B*(t-z)*U-expr)==0
D=t*t-4*t+1
z0=-t*(t+1)/D
dh=-t**3*(t-2)/(2*t-1)
dz=t**3*(t-2)*(t+1)**2*(5*t*t-14*t+5)/D**4
assert S.cancel((A*(z-1)/(B*(t-z))).subs(z,z0)-dh)==0
assert S.cancel((A*(t-1)/(t-z)).subs(z,z0)-dz)==0
print("independent first reads and exact third debut z, d_t, d_z checked")

H=X*(X-1)*(X-t)*(X-z)
Jh=lambda a:S.factor(S.integrate(H,(X,0,a)).subs(z,z0))
h1=Jh(1)
ht=Jh(t)
hz=Jh(z0)
h0=S.factor(-(t*h1-ht/dh)/(t-1))
assert h1== (5*t**3-6*t*t+4*t-1)/(20*D) or S.cancel(h1-(5*t**3-6*t*t+4*t-1)/(20*D))==0
assert S.cancel(ht+t**4*(t**3-4*t*t+6*t-5)/(20*D))==0
assert S.cancel(hz-t**4*(t+1)**3*(t*t-3*t+1)*(5*t*t-14*t+5)/(20*D**5))==0
assert S.cancel(h0+t*(t+1)*(3*t*t-7*t+3)/(20*(t-2)*D))==0
print("all four exact dirty-repeat/zero probes checked")

R=lambda a:-((t-a)*J(1)+(a-1)*J(t)/dh)/(t-1)
F=E(t)-dh*E(1)
G=E(z0)-dz*E(1)
want=k*k*t**3*(t-k)*(k-1)*(t-1)**3*(t+1)*(k-z0)**2/(10*D**2)
assert S.cancel(det([F,G,J(k),R(k)])-want)==0
print("fourth distinct row compatibility determinant forces a previous clock")

guards=[(1,-4,1),(5,-6,4,-1),(1,-4,6,-5),(1,-3,1),(5,-14,5),(3,-7,3)]
for v in guards:
 n=len(v)-1
 assert all(sum(c*a**(n-i)*b**i for i,c in enumerate(v))%7
            for a,b in product(range(7),repeat=2) if a or b)
print("all six projective guard polynomials have no root modulo 7")

r,tau,s,p,h=S.symbols("r tau s p h")
P=X*(X-r)*(X-tau)
JP=S.integrate(P,(X,0,X))
assert S.cancel(JP.subs(X,r)-r**3*(-r+2*tau)/12)==0
assert S.expand(JP.subs(tau,r/2)-X**2*(X-r)**2/4)==0
F=lambda z:z*(z-2*r/3)
al=p*p*(3*s-2*p)/s**3
assert S.cancel(F(p)-al*F(s)+2*p*(p-s)*(2*p*r-3*p*s-r*s)/(3*s*s))==0
assert S.cancel(S.integrate(F(X),(X,0,h))/F(r)-h*h*(h-r)/r**2)==0
assert S.expand((3*h*h-4*(1+tau)*h+6*tau)*(2*h-1)
                +h*(h-2)*(2*tau-1)+6*(-h+tau)*(h-1)**2)==0
assert S.cancel((JP.subs({X:z0,r:1,tau:t})/JP.subs({X:1,r:1,tau:t}))-dz)==0
print("literal host primitive, fixed-q quadratic, and both rank-two prefix dirt gates checked")
