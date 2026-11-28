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
S,Tt=s.symbols('S T')
def symm(p):
    q,r,_=s.symmetrize(p.as_expr(),[a,b],formal=True)
    assert r==0
    return s.Poly(q.subs({s.Symbol('s1'):S,s.Symbol('s2'):Tt}),S,Tt).clear_denoms()[1].primitive()[1].as_expr()
pair=x*x+U*x+DL*V
H0=aa/2;E0=1-bb/2
CrossHE=R(Xi.evaluate(x,H0)-Xi.evaluate(x,E0))
CrossHE=CrossHE.exquo(H0-E0)
det1=symm(D); pivot1=symm(DL); chem=symm(CrossHE)
width=DL
def evalSym(g):
    c0=g.get((0,),R.zero);c1=g.get((1,),R.zero)
    return c0*c0-U*c0*c1+DL*V*c1*c1
def choose_same(tc):
    l0=(aa-E0)*(DL*aa-x);l1=-E0*x
    r0=(H0-d)*(tc-DL*d);r1=-(1-H0)*(DL-tc)
    return evalSym((l0*r0+T(aa)*l1*r0+T(bb)*l0*r1+PGRAM*l1*r1).rem(pair))
def strips(p,g):
    assert p
    while True:
        v,w=p.div(g)
        if w:return p
        p=v
def swap(p):
    return R.from_dict({(j,i):c for (i,j),c in p.items()})
def symmetrized_norm(q):
    q=strips(q,DL)
    return symm(q*swap(q))

W=x*x*(x-aa)**2*(1-x)**2*(x-d)**2
I=[sum(W.get((i,),R.zero)/(i+j+1) for i in range(9)) for j in range(3)]
def support(h):
    A0=DL*(I[2]-h*I[1]);A1=h*I[0]-I[1]
    return strips(evalSym(A0+A1*x),DL)
Es=symm(support(H0)*support(E0))
Eq=symm(DL*I[2]+U*I[1]+V*I[0])

cSame=symm(strips(choose_same(x),DL))
def contact_opposite(r):
    l0=(aa-E0)*(DL*aa-x);l1=-E0*x
    rv=DL*H0 if r=='half' else x
    r0=(aa-d)*(rv-DL*d);r1=-(1-aa)*(DL-rv)
    ew=(l0*r0+T(aa)*l1*r0+T(bb)*l0*r1+PGRAM*l1*r1).rem(pair)
    return symmetrized_norm(evalSym(ew))
def check(D,C,E,S,T):
    R0=s.resultant(D,C,T);R1=s.resultant(D,E,T);g=s.gcd(R0,R1)
    return s.degree(R0,S),s.degree(R1,S),s.factor_list(g,S)[1]

D,Dm=symm(D),symm(DL)
cs=[('opposite-half',contact_opposite('half'),Eq,180,36,1),
    ('opposite-free',contact_opposite('free'),Es,216,108,2)]
T=Tt
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



for name,C,E,D0,D1,k in cs:
    m,n,gg=check(D,C,E,S,T)
    assert [m,n]==[D0,D1]
    assert [(s.degree(f,S),r) for f,r in gg]==[(4,1),(10,k)]
    for f,r in gg:
        K=Coeff(f)
        d,z,c,e=map(K.coeffs,[D,Dm,C,E])
        F=gcd(K,d,e)
        rv=rem(K,mul(K,z,z),F)
        if rv:
            F=gcd(K,F,c)
            rv=rem(K,mul(K,z,z),F)
        assert len(F)==2 and not rv
        print(name,'actual guard fiber',s.degree(f,S),'closed',flush=True)
