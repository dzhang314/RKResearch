"""Nested norm projection for the nonsingular leading live-eighth branches."""
import sys
import json
from pathlib import Path
from time import monotonic
from flint import fmpq, fmpq_poly
phase=sys.argv[1]
t0=monotonic()
def now(*a):print(round(monotonic()-t0,2),phase,*a,flush=True)
def C(a,b=1):return fmpq(int(a),int(b))
P=fmpq_poly
Z=P([]);O=P([1]);m=P([0,1])
if phase=='arith':
    ss=[
     P([-2,32,-242,1148,-3374,6104,-6608,3920,-980]),
     P([39,-546,2688,-7224,10962,-8820,2940]),
     P([-126,1512,-4452,5880,-2940]),
     P([98,-980,980]),
    ]
elif phase=='star':
    ss=[
     P([-3,54,-459,2048,-4830,4620,4270,-15540,14700,-4900]),
     P([168,-1488,5460,-10920,5880,16380,-29400,14700]),
     P([-210,3780,-8190,2100,14700,-14700]),
     P([0,-2940,0,4900]),
    ]
else:raise ValueError(phase)
lead=ss[3]
# R=lead*r, E=R^2. The scaled monic relation is a cubic in E.
qE=[ss[i]*lead**(5-2*i) for i in range(3)]
dty=type(Z)
def h(x):
    if isinstance(x,dty):return x
    return P([x])
aa=(Z,Z,Z);oo=(O,Z,Z)
class U:
    def __init__(self,*a):
        if len(a)==1:
            if isinstance(a[0],U): self.c=a[0].c;return
            a=(h(a[0]),Z,Z)
        self.c=a
    def __bool__(self):return any(self.c)
    def __eq__(x,y):return x.c==U(y).c
    def __neg__(x):return U(*(-q for q in x.c))
    def __add__(x,y):
        if isinstance(y,(V,T)):return NotImplemented
        return U(*(a+b for a,b in zip(x.c,U(y).c)))
    __radd__=__add__
    def __sub__(x,y):return x+-U(y)
    def __rsub__(x,y):return -x+U(y)
    def __mul__(x,y):
        if isinstance(y,(V,T)):return NotImplemented
        out=[Z]*5
        for i,a in enumerate(x.c):
            if a:
                for j,b in enumerate(U(y).c):
                    if b:out[i+j]=out[i+j]+a*b
        for k in range(4,2,-1):
            if out[k]:
                for j in range(3):out[k+j-3]=out[k+j-3]-out[k]*qE[j]
        return U(*out[:3])
    __rmul__=__mul__
    def __pow__(x,n):
        if n==0:return U(1)
        if n%2==0:return (x*x)**(n//2)
        return x*x**(n-1)
    def norm(x):
        y,z=x*e,x*e*e
        a,b,c=x.c;d,f,g=y.c;h,i,j=z.c
        return a*(f*j-g*i)-d*(b*j-c*i)+h*(b*g-c*f)
    def deg(x):return max(q.degree() for q in x.c)
    def exact(x,d):
        qr=[divmod(f,d) for f in x.c]
        assert not any(r for _,r in qr)
        return U(*(q for q,_ in qr))
    def guard_gcd(x,d):
        for f in x.c:
            d=d.gcd(f)
            if d.degree()==0:break
        return d
class V:
    def __init__(x,a=0,b=0):
        if isinstance(a,V):x.a,x.b=a.a,a.b;return
        x.a,x.b=U(a),U(b)
    def __eq__(x,y):
        y=V(y);return x.a==y.a and x.b==y.b
    def __bool__(x):return bool(x.a) or bool(x.b)
    def __neg__(x):return V(-x.a,-x.b)
    def __add__(x,y):
        if isinstance(y,T):return NotImplemented
        y=V(y);return V(x.a+y.a,x.b+y.b)
    __radd__=__add__
    def __sub__(x,y):return x+-V(y)
    def __rsub__(x,y):return -x+V(y)
    def __mul__(x,y):
        if isinstance(y,T):return NotImplemented
        y=V(y);return V(x.a*y.a+e*x.b*y.b,x.a*y.b+x.b*y.a)
    __rmul__=__mul__
    def __pow__(x,n):
        if n==0:return V(1)
        if n%2==0:return (x*x)**(n//2)
        return x*x**(n-1)
    def deg(x):return max(x.a.deg(),x.b.deg())
    def norm(x):return (x.a*x.a-e*x.b*x.b).norm()
    def guard_gcd(x,d):return x.b.guard_gcd(x.a.guard_gcd(d))
    def exact(x,d):return V(x.a.exact(d),x.b.exact(d))
class T:
    def __init__(x,a=0,b=0):
        if isinstance(a,T):x.a,x.b=a.a,a.b;return
        x.a,x.b=V(a),V(b)
    def __bool__(x):return bool(x.a) or bool(x.b)
    def __neg__(x):return T(-x.a,-x.b)
    def __add__(x,y):
        y=T(y);return T(x.a+y.a,x.b+y.b)
    __radd__=__add__
    def __sub__(x,y):return x+-T(y)
    def __rsub__(x,y):return -x+T(y)
    def __mul__(x,y):
        y=T(y);bb=x.b*y.b
        return T(x.a*y.a-bb*q0,x.a*y.b+x.b*y.a-bb*q1)
    __rmul__=__mul__
    def __pow__(x,n):
        if n==0:return T(1)
        if n%2==0:return (x*x)**(n//2)
        return x*x**(n-1)
    def norm(x):return (x.a*x.a-q1*x.a*x.b+q0*x.b*x.b).norm()
    def deg(x):return max(x.a.deg(),x.b.deg())
    def guard_gcd(x,d):return x.b.guard_gcd(x.a.guard_gcd(d))
    def exact(x,d):return T(x.a.exact(d),x.b.exact(d))
e=U(Z,O,Z)
r=V(0,1);l=V(lead);m=V(lead*m)
if phase=='arith':
    t8,t9,t10=m-r,m,m+r
else:
    t8,t9,t10=m+r,m-r,(l+m)*C(1,2)
s1=t8+t9+t10;s2=t8*t9+t8*t10+t9*t10;s3=t8*t9*t10
# These are lead^3 times the unscaled masked ordinary moments.
ms=[l**3*C(1,k+4)-s1*l*l*C(1,k+3)+s2*l*C(1,k+2)-s3*C(1,k+1) for k in range(5)]
m0,m1,m2,m3,m4=ms
S0=m0*(m2*m4-m3*m3)-m1*(m1*m4-m2*m3)+m2*(m1*m3-m2*m2)
assert not S0
Delta=m0*m2-m1*m1
Nl=m1*m2-m0*m3;Nq=m1*m3-m2*m2
q1=l*Nl;q0=l*l*Delta*Nq
d=T(l*Delta);g=T((l-t10)*Delta);a=T(0,1);b=T(-q1)-a;c=T(t8*Delta)
def L(t):return 70*t**4-140*d*t**3+90*d*d*t*t-20*d**3*t+d**4
def L3(t):return t**3-C(3,2)*d*t*t+C(3,5)*d*d*t-C(1,20)*d**3
la,lb,lc=L(a),L(b),L(c)
ya,yb,yc=L3(a),L3(b),L3(c)
def ev(P,T0):return sum((z*T0**i for i,z in enumerate(P)),T(0))
def J(P,k,T0):return sum((z*T0**(i+k+1)*C(1,i+k+1) for i,z in enumerate(P)),T(0))
def gate(P):
    E0=J(P,0,a)-g*ev(P,a)
    eta=g*a*ev(P,a)-J(P,1,a)
    F=la*(a*(J(P,0,b)-g*ev(P,b))+g*b*ev(P,b)-J(P,1,b))-lb*eta
    da=g*a*a*ev(P,a)-J(P,2,a)
    db=g*b*b*ev(P,b)+a*a*(J(P,0,b)-g*ev(P,b))-J(P,2,b)
    dc=(g*c*c*ev(P,c)+(a+b)*(J(P,1,c)-g*c*ev(P,c))-a*b*(J(P,0,c)-g*ev(P,c))-J(P,2,c))*la+lc*(eta*(a+b))
    H=(ya*lb-yb*la)*dc+(yb*lc-yc*lb)*(la*da)+(yc*la-ya*lc)*(la*db)
    return E0,F,H
def strip_l(ps):
    ps=list(ps)
    while True:
        d=lead
        for q in ps:d=q.guard_gcd(d)
        if d.degree()==0:return ps
        ps=[h.exact(d) for h in ps]
P0=[-g*g,2*g,T(C(-1,2))]
R1=[-g*g,g];R2=[g*g,-2*g,T(1)]
F0,G0,H0=gate(P0);F1,G1,H1=gate(R1);F2,G2,H2=gate(R2)
F0,F1,F2=strip_l([F0,F1,F2]);G0,G1,G2=strip_l([G0,G1,G2]);H0,H1,H2=strip_l([H0,H1,H2])
now("gate degrees",[q.deg() for q in [F0,F1,F2,G0,G1,G2,H0,H1,H2]])
D=F1*G2-F2*G1
BN=F2*G0-F0*G2;AN=F0*G1-F1*G0
X=D*H0+BN*H1+AN*H2
Y=-2*AN**3-BN*AN*AN+4*BN*BN*AN+BN**3+(3*BN*AN+2*AN*AN)*D
now("element degrees",[q.deg() for q in [X,Y,D,AN,BN]])
norms=[]
for q in [X,Y,D,AN,BN]:
    norms.append(strip_l([q])[0].norm())
    now("norm degree",norms[-1].degree())
G0=norms[0].gcd(norms[1])
G1=norms[2].gcd(norms[3]).gcd(norms[4])

expected=(2670,1170) if phase=="arith" else (3378,1476)
record=json.loads(Path(__file__).with_name("projection-factors.json").read_text())[phase]
for g0,n in zip((G0,G1),expected):
    assert g0.degree()==n
    radical=g0//g0.gcd(g0.derivative())
    # Only the leading coefficient is removed at this projection. Its exact
    # fibers are checked in the live-leading companion, not inferred here.
    no_lead=radical//radical.gcd(lead)
    ff=no_lead.factor()[1]
    assert all(e==1 for _,e in ff)
    actual=[[str(x) for x in q0.coeffs()] for q0,e in ff]
    assert sorted(actual)==sorted(record)
    now("exact gcd degree",n,"non-leading factor degrees",
        sorted(q0.degree() for q0,_ in ff))
