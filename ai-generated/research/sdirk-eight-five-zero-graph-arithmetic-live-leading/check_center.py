"""Exact symmetric-tail exception in the live arithmetic rear."""
from flint import fmpq as Q, fmpq_poly as P
r=P([0,1]);O=P([1]);Z=P()
d=Q(1,80)-r*r*Q(1,12)
mu=Q(1,448)-r*r*Q(1,80)
square=d*mu  # square of the signed scaled centered early clock
class E:
    def __init__(self,a=0,b=0):
        if isinstance(a,E):self.a,self.b=a.a,a.b;return
        self.a=a if isinstance(a,P) else P([a])
        self.b=b if isinstance(b,P) else P([b])
    def __add__(self,f):
        f=E(f);return E(self.a+f.a,self.b+f.b)
    __radd__=__add__
    def __neg__(self):return E(-self.a,-self.b)
    def __sub__(self,f):return self+-E(f)
    def __rsub__(self,f):return -self+E(f)
    def __mul__(self,f):
        f=E(f);return E(self.a*f.a+square*self.b*f.b,self.a*f.b+self.b*f.a)
    __rmul__=__mul__
    def __pow__(x,n):
        if n==0:return E(1)
        if n%2==0:return (x*x)**(n//2)
        return x*x**(n-1)
    def norm(self):return self.a*self.a-square*self.b*self.b
    def __repr__(self):return str((self.a,self.b))
    def __bool__(self):return bool(self.a) or bool(self.b)

g=E(d*(Q(1,2)-r))
d=E(d)
a=d*Q(1,2)+E(0,1);b=d*Q(1,2)-E(0,1);c=g
def L(t):return 70*t**4-140*d*t**3+90*d*d*t*t-20*d**3*t+d**4
def L3(t):return t**3-Q(3,2)*d*t*t+Q(3,5)*d*d*t-Q(1,20)*d**3
la,lb,lc=L(a),L(b),L(c)
ya,yb,yc=L3(a),L3(b),L3(c)
def ev(P,T):return sum((z*T**i for i,z in enumerate(P)),E(0))
def J(P,k,T):return sum((z*T**(i+k+1)*Q(1,i+k+1) for i,z in enumerate(P)),E(0))
def gate(P):
    E0=J(P,0,a)-g*ev(P,a)
    eta=g*a*ev(P,a)-J(P,1,a)
    F=la*(a*(J(P,0,b)-g*ev(P,b))+g*b*ev(P,b)-J(P,1,b))-lb*eta
    da=g*a*a*ev(P,a)-J(P,2,a)
    db=g*b*b*ev(P,b)+a*a*(J(P,0,b)-g*ev(P,b))-J(P,2,b)
    dc=(g*c*c*ev(P,c)+(a+b)*(J(P,1,c)-g*c*ev(P,c))-a*b*(J(P,0,c)-g*ev(P,c))-J(P,2,c))*la+lc*(eta*(a+b))
    H=(ya*lb-yb*la)*dc+(yb*lc-yc*lb)*(la*da)+(yc*la-ya*lc)*(la*db)
    return E0,F,H
P0=[-g*g,2*g,E(Q(-1,2))]
R1=[-g*g,g];R2=[g*g,-2*g,E(1)]
F0,G0,H0=gate(P0);F1,G1,H1=gate(R1);F2,G2,H2=gate(R2)
D=F1*G2-F2*G1
BN=F2*G0-F0*G2;AN=F0*G1-F1*G0
X=D*H0+BN*H1+AN*H2
Y=-2*AN**3-BN*AN*AN+4*BN*BN*AN+BN**3+(3*BN*AN+2*AN*AN)*D
guards=[('diag',g.a),('ordinary-pivot',d.a),('discriminant',square),('rear repeat',r),
        ('known clock collision',square-r*r*d.a*d.a),('early Gauss',la.norm()),('late Gauss',lc.norm())]
def strip(f):
    for name,q in guards:
        k=0
        while True:
            h=f.gcd(q)
            if h.degree()==0:break
            f,r0=divmod(f,h);assert not r0
            k+=h.degree()
        print(name,k)
    return f
def project(fs):
    norms=[z.norm() for z in fs]
    print("initial norm degrees",list(n.degree() for n in norms))
    common=norms[0]
    for n in norms[1:]:common=common.gcd(n)
    print("common degree",common.degree())
    f=strip(common)
    print('remaining gcd',f.degree(),[(c.degree(), e) for c,e in f.factor()[1]])
    if f.degree()<5:print("remaining", f)
    return f
R=project([X,Y]);S=project([D,AN,BN])
assert R.degree()==S.degree()==0
