"""Nine-site four-distinct three-cross (same selected free) edge-dormant gates."""
import sympy as s
from sympy import QQ
from sympy.polys.rings import ring
from pathlib import Path
a,b=s.symbols('a b')
R,aa,bb=ring('a,b',QQ);X,x=ring('x',R)
h=aa/2; e=1-bb/2; d=1-bb
Vb=(1-x)**2*(x-d)**2
W=x*x*(x-aa)**2*Vb
def it(f,j=0):return sum(v/(k[0]+j+1) for k,v in f.items())
I0,I1,I2=[it(W,j) for j in range(3)]
JV=x**3*(6*x*x-15*aa*x+10*aa*aa)/30
H=it(JV*Vb);C=it(JV*Vb,1)
M=I1*H-I0*C;N=I2*H-I1*C
K=I2*H*H-2*C*H*I1+C*C*I0
P=(x-aa)*(x-h)*(x-d)*(x-e)*(H*x-C)
m=[it(x*(1-x)*P,j) for j in range(4)]
p,q,r=[M*m[j+1]-N*m[j] for j in range(3)]
guards=[aa,bb,aa-1,aa-2,bb-1,bb-2,aa+bb-1,aa+bb-2,2*aa+bb-2,aa+2*bb-2,
        H,M,C,C-H,C-aa*H,C-h*H,C-d*H,C-e*H,N,N-M,N-aa*M,N-h*M,N-d*M,N-e*M,H*N-C*M]
def clean(f,gs):
    assert f
    f0=f
    for g in gs:
        while True:
            z,w=f0.div(g)
            if w:break
            f0=z
    return s.Poly(f0.as_expr(),a,b).clear_denoms()[1].primitive()[1]
def pr(a):return [(x.degree(),n) for x,n in s.factor_list(s.Poly(a))[1]]
# Singular chart e0=0 entails e1=e2=0 even without ordering.
E0,E1,E2=[clean(f,guards) for f in [p,q,r]]
rho=[s.resultant(E0.as_expr(),X.as_expr(),b) for X in [E1,E2]]
G=s.gcd(*rho)
print('singular residual degrees', [E.degree(b) for E in [E0,E1,E2]], [s.degree(z,a) for z in rho],pr(G),flush=True)
# Regular chart selected clock t=q/p.
T=lambda x:1-32*x+216*x*x-480*x**3+330*x**4
UC=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
MAT=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],[-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
Uab=sum(t*aa**i*bb**j for i,uu in enumerate(UC) for j,t in enumerate(uu))
L0=(aa-e)*(aa*p-q); L1=-e*q
R0=(h-d)*(q-d*p); R1=-(1-h)*(p-q)
Xi=L0*R0+T(aa)*L1*R0+T(bb)*L0*R1+Uab*L1*R1
Dvec=[aa**5*N**(i+1)*M**(4-i)-aa**(i+1)*N**3*(6*N**2-15*aa*N*M+10*aa**2*M**2) for i in range(5)]
Rderb=[d**j-(bb*j*d**(j-1) if j else R.zero) for j in range(5)]
PhiR=[R0+R1*r0 for r0 in Rderb]
Dgate=sum(Dvec[i]*MAT[i][j]*PhiR[j] for i in range(5) for j in range(5))
Amp=K*(N-h*M)*(N-e*M)*(p*N-q*M)*M*M + (p*m[1]-q*m[0])*N*(N-M)*(N-aa*M)*(N-d*M)*(H*N-C*M)
guards2=guards+[p,q,q-p,q-aa*p,q-h*p,q-d*p,q-e*p,H*q-C*p,M*q-N*p]
Dp=clean(p*r-q*q,guards2)
Xp=clean(Xi,guards2);Gp=clean(Dgate,guards2);Ap=clean(Amp,guards2)
print('regular polynomials (a,b,tot):',[(P.degree(a),P.degree(b),P.total_degree()) for P in [Dp,Xp,Gp,Ap]],flush=True)
assert Dp.gcd(Xp).total_degree()==0
print('Regular width polynomials are coprime over Q[a,b].',flush=True)

S,T=a,b
class Coeff:
    def __init__(self,g):
        self.g=s.Poly(g,S,domain=s.QQ)
        self.o=s.Poly(0,S,domain=s.QQ);self.i=s.Poly(1,S,domain=s.QQ)
    def at(self,v):return s.Poly(v,S,domain=s.QQ).rem(self.g)
    def add(self,x,y):return (x+y).rem(self.g)
    def sub(self,x,y):return (x-y).rem(self.g)
    def mul(self,x,y):return (x*y).rem(self.g)
    def inv(self,x):return x.invert(self.g)
    def coeffs(self,p):
        p=s.Poly(p,T)
        return [self.at(p.nth(i)) for i in range(p.degree()+1)]

def trim(a):
    r=list(a)
    while r and not r[-1]:r.pop()
    return r
def rem(K,a,b):
    a=trim(a);b=trim(b)
    c=K.inv(b[-1]);m=len(b)-1
    while len(a)>m:
        i=len(a)-1-m
        w=K.mul(a[-1],c)
        for j,bj in enumerate(b):a[i+j]=K.sub(a[i+j],K.mul(w,bj))
        a=trim(a)
    return a
def gcd(K,a,b):
    a,b=trim(a),trim(b)
    while b:a,b=b,rem(K,a,b)
    c=K.inv(a[-1])
    return [K.mul(x,c) for x in a]
def mul(K,a,b):
    z=[K.o]*(len(a)+len(b)-1)
    for i,aa in enumerate(a):
        for j,bb in enumerate(b):z[i+j]=K.add(z[i+j],K.mul(aa,bb))
    return trim(z)


sf=s.factor_list(G,a)[1]
assert [(s.degree(f,a),j) for f,j in sf]==[(1,8),(8,4),(12,1)]
assert sf[0][0]==a
for p,n in sf[1:]:
    Rb=Coeff(p)
    gg=gcd(Rb,gcd(Rb,Rb.coeffs(E0.as_expr()),Rb.coeffs(E1.as_expr())),Rb.coeffs(E2.as_expr()))
    guard=C-d*H if s.degree(p,a)==8 else M
    assert len(gg)==(3 if s.degree(p,a)==8 else 2)
    assert not rem(Rb,Rb.coeffs(guard.as_expr()),gg)
    print('Exact singular same-b fiber',s.degree(p,a),'excluded.',flush=True)
