"""Explore the four-distinct same-free-pair crossover equations over Q."""
import sympy as s
from sympy.polys.rings import ring
from sympy import QQ
a,b=s.symbols('a b')
R,aa,bb=ring('a,b',QQ)
X,x=ring('x',R)
P=(x-aa)*(x-aa/2)*(x+bb-1)*(x+bb/2-1)
def it(i):
    return sum(P.get((j,),0)/((i+j+2)*(i+j+3)) for j in range(5))
m=[it(i) for i in range(5)]
m0,m1,m2,m3,m4=m
D=m0*m2*m4+2*m1*m2*m3-m0*m3**2-m1**2*m4-m2**3
DL=m0*m2-m1**2
U=m1*m2-m0*m3;V=m1*m3-m2*m2
l0=aa**2*DL+aa*U+V;l1=-V
d=1-bb;r0=d*d*DL+d*U+V;r1=-DL-U-V
T=lambda a:1-32*a+216*a*a-480*a**3+330*a**4
UC=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
PGRAM=sum(t*aa**i*bb**j for i,r in enumerate(UC) for j,t in enumerate(r))
C1=l0*r0+T(aa)*l1*r0+T(bb)*l0*r1+PGRAM*l1*r1
H=P*(DL*x*x+U*x+V)
J=-sum(sum(H.get((i,),0)/((i-j+1)*(i-j+2)) for i in range(j+1,7))*x**j for j in range(6))
Xi=J*x*(1-x)*(aa-x)*(x-d)
z0=R.zero;z1=R.zero
for i in range(9,-1,-1):
    z0,z1=Xi.get((i,),0)*DL**(9-i)-DL*V*z1,z0-U*z1
C2=z1
S,Tt=s.symbols('S T')
C=[]
for label,f in [('D',D),('Delta',DL),('contact',C1),('cross',C2)]:
    q,rem,_=s.symmetrize(f.as_expr(),[a,b],formal=True)
    assert rem==0,(label,rem)
    q=q.subs({s.Symbol('s1'):S,s.Symbol('s2'):Tt})
    n=s.Poly(q,S,Tt).clear_denoms()[1].primitive()[1]
    print(label,n.total_degree(),n.degree(S),n.degree(Tt),'terms',len(n.terms()),flush=True)
    C.append(n.as_expr())
D,DL,C1,C2=C
r0=s.resultant(D,C1,Tt)
r1=s.resultant(D,C2,Tt)
rg=s.resultant(D,DL,Tt)
assert [s.degree(q,S) for q in [r0,r1,rg]]==[72,234,24]
S,T=S,Tt
g=s.gcd(r0,r1)
assert s.degree(g,S)==24 and s.rem(rg,g,S)==0
gfs=s.factor_list(g,S)[1]
assert [(s.degree(q,S),i) for q,i in gfs]==[(4,1),(10,2)]

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

for f,n in gfs:
    K=Coeff(f)
    d,l,h1,h2=map(K.coeffs,[D,DL,C1,C2])
    F=gcd(K,gcd(K,d,h1),h2)
    fdeg=len(F)-1
    good=all(not x for x in rem(K,mul(K,l,l),F))
    print('fiber degree',s.degree(f,S),'common T degree',fdeg,'divides Delta²',good,flush=True)
    assert fdeg==1 and good
