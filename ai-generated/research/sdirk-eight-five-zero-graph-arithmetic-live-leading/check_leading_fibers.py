"""All zero-leading live-rear fibers aside from arithmetic center m=1/2."""
import sympy as S
from sympy.polys.rings import ring
M=S.symbols('m')
def run(case,mpoly,mvalue=None):
    if mvalue is None:
        K=S.QQ.algebraic_field((S.Poly(mpoly,M),M));m=K.unit
        assert S.Poly(mpoly,M).is_irreducible
    else:
        K=S.QQ;m=K.convert(mvalue)
    C=lambda q,b=1:K.convert(S.Rational(q,b))
    Ra,A,r=ring(('aA,rA' if case=='arith' else ('aS0,rS0' if mvalue is not None else 'aS1,rS1')),K)
    Rr=Ra.drop(0)
    if case=="arith":
        t8,t9,t10=Ra(m)-r,Ra(m),Ra(m)+r
    else:
        t8,t9,t10=Ra(m)+r,Ra(m)-r,Ra((1+m)*C(1,2))
    e1=t8+t9+t10;e2=t8*t9+t8*t10+t9*t10;e3=t8*t9*t10
    moments=[Ra(C(1,k+4))-e1*C(1,k+3)+e2*C(1,k+2)-e3*C(1,k+1) for k in range(5)]
    m0,m1,m2,m3,m4=moments
    H=m0*(m2*m4-m3*m3)-m1*(m1*m4-m3*m2)+m2*(m1*m3-m2*m2)
    h=H.drop(0)
    assert h.degree()==4, (case,mpoly,h)
    h=h.monic()
    Hr=Ra.from_dict({(0,i):c for (i,),c in h.items()})
    Delta=(m0*m2-m1*m1)%Hr
    Lnum=(m1*m2-m0*m3)%Hr
    Qnum=(m1*m3-m2*m2)%Hr
    Bconst=(Qnum*Delta)%Hr
    Qa=A*A+Lnum*A+Bconst
    def rd(x):return (x%Qa)%Hr
    class E:
        def __init__(self,p=0):
            self.p=p.p if isinstance(p,E) else rd(Ra(p))
        def __add__(self,f):return E(self.p+E(f).p)
        __radd__=__add__
        def __neg__(self):return E(-self.p)
        def __sub__(self,f):return self+-E(f)
        def __rsub__(self,f):return -self+E(f)
        def __mul__(self,f):return E(self.p*E(f).p)
        __rmul__=__mul__
        def __pow__(x,n):
            if n==0:return E(1)
            if n%2==0:return (x*x)**(n//2)
            return x*x**(n-1)
        def norm(self):
            ca=Ra.from_dict({(0,k):c for (i,k),c in self.p.items() if i==0})
            cb=Ra.from_dict({(0,k):c for (i,k),c in self.p.items() if i==1})
            return ((ca*ca-Lnum*ca*cb+Bconst*cb*cb)%Hr).drop(0)
    d=E(Delta);g=d*E(1-t10);a=E(A);b=E(-Lnum)-a;c=d*E(t8)
    def L(t):return 70*t**4-140*d*t**3+90*d*d*t*t-20*d**3*t+d**4
    def L3(t):return t**3-C(3,2)*d*t*t+C(3,5)*d*d*t-C(1,20)*d**3
    la,lb,lc=L(a),L(b),L(c)
    ya,yb,yc=L3(a),L3(b),L3(c)
    def ev(P,T):return sum((z*T**i for i,z in enumerate(P)),E(0))
    def J(P,k,T):return sum((z*T**(i+k+1)*C(1,i+k+1) for i,z in enumerate(P)),E(0))
    def gate(P):
        E0=J(P,0,a)-g*ev(P,a)
        eta=g*a*ev(P,a)-J(P,1,a)
        F=la*(a*(J(P,0,b)-g*ev(P,b))+g*b*ev(P,b)-J(P,1,b))-lb*eta
        da=g*a*a*ev(P,a)-J(P,2,a)
        db=g*b*b*ev(P,b)+a*a*(J(P,0,b)-g*ev(P,b))-J(P,2,b)
        dc=(g*c*c*ev(P,c)+(a+b)*(J(P,1,c)-g*c*ev(P,c))-a*b*(J(P,0,c)-g*ev(P,c))-J(P,2,c))*la+lc*(eta*(a+b))
        H=(ya*lb-yb*la)*dc+(yb*lc-yc*lb)*(la*da)+(yc*la-ya*lc)*(la*db)
        return E0,F,H
    P0=[-g*g,2*g,E(C(-1,2))]
    R1=[-g*g,g];R2=[g*g,-2*g,E(1)]
    F0,G0,H0=gate(P0);F1,G1,H1=gate(R1);F2,G2,H2=gate(R2)
    D=F1*G2-F2*G1
    BN=F2*G0-F0*G2;AN=F0*G1-F1*G0
    X=D*H0+BN*H1+AN*H2
    Y=-2*AN**3-BN*AN*AN+4*BN*BN*AN+BN**3+(3*BN*AN+2*AN*AN)*D
    print(case,mpoly,"r modulus degree",h.degree(),flush=True)
    for name,forms in [("regular",[X,Y]),("singular",[D,AN,BN])]:
        common=h
        for f in forms:common=common.gcd(f.norm())
        print(name,"degree before any guard stripping",common.degree(),flush=True)
        assert common.degree()==0

run('arith',10*M*M-10*M+1)
run('star',None,S.Integer(0))
run('star',5*M*M-3)
