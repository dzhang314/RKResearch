"""D,D,D against literal D,S,S star at doubled endpoints."""
import sympy as S
from sympy.polys.rings import ring
from itertools import combinations
from fractions import Fraction as FQ
x=S.Symbol('Y')
h0,m0,d0=FQ(2,5),FQ(7,5),FQ(6,5)
assert 35*h0*h0*d0*d0-21*m0*m0*(h0*h0+d0*d0)+15*m0**4==-FQ(21,125)
def cases():
    # Distinct even graph forces m=2. Distinct split never fits (see scalar cases).
    yield 'distinct midpoint',S.QQ,S.QQ(2),S.QQ(156,49)
    F=S.Poly(35*x*x-112*x+8,x);assert F.is_irreducible
    E=S.QQ.algebraic_field((F,x))
    yield 'shared clock',E,E.one,E.unit

def compute(label,K,m,S0):
    R,t=ring('t',K)
    c42=K.convert(S.Rational(6,7))*m*m
    c40=K.convert(S.Rational(3,35))*m**4
    c3=K.convert(S.Rational(3,5))*m*m
    L=t**4-t*t*c42+c40
    L3=t**3-c3*t
    c=m-2; h=m-1; ell=2*m
    W=(t-c)**2-S0
    if label=='distinct midpoint':
        P=t*(t*t-1)
        T=(t+2)/2
        A0=R(c40)-(2*L.evaluate(t,1)/3)*t+(4*L.evaluate(t,1)/3-c40)*t*t
        beta=-4*L.evaluate(t,1)/3
    else:
        V=(t-1)**2-S0
        P=t*V
        T=1-(t-1)**2/2
        ka=2-S0
        A=(2*L/ka)%V
        A0=A+((2*c40-A.evaluate(t,K.zero))/(1-S0))*V
        beta=-4*c40
    assert not ((T*A0-L)%P)
    if label=='distinct midpoint':mu=(1-c3)/L.evaluate(t,1)
    else:
       # Leading coefficient of Q0: monic Q support determines slope
       # from coefficient t^3 in L3 = Q0+μ t L4.
       mu=K.one/((t*L-P*W).get((3,),K.zero))
    Q0=L3-mu*t*L
    assert Q0==-mu*P*W and S0 and W.gcd(W.diff(t)).degree()==0
    def inv(f,v):
        a,b,g=f.gcdex(v)
        assert g==R.one
        return a%v
    W1=W.get((1,),K.zero)
    def trace_w(f):
        q=f%W
        return 2*q.get((0,),K.zero)-W1*q.get((1,),K.zero)
    P2,P1=(P.get((i,),K.zero) for i in (2,1))
    def trace_p(f):
        q=f%P
        return 3*q.get((0,),K.zero)-P2*q.get((1,),K.zero)+(P2*P2-2*P1)*q.get((2,),K.zero)
    uc=-trace_w(L.diff(t)*inv(L*W.diff(t),W))
    N=(inv(Q0,L**2)*(4*m**6/175))%(L**2)
    def width(v):return ((v*N)%(L**2)).get((7,),K.zero)
    const=2*uc-ell*width(L*inv(W,L**2))
    Li=inv(L,W);Lp=inv(L,P)
    def tra(f):
        return 2*(trace_w(f*Li)+trace_p(f*Lp))-ell*width(f)
    # At the two true S sites t=c±sqrt(X), t-c squared is X.
    RR,Y=ring('X',K)
    def vals(f):
        a=RR.zero; b=RR.zero
        s=f.compose(t,t+c)
        for (i,),v in s.items():
           if i%2:a0=Y**((i-1)//2)*v;b+=a0
           else:a+=Y**(i//2)*v
        return a,b
    vv=(2-Y)/2
    Lr,Tr,Ar=(vals(v) for v in (L,T,A0))
    eq=[]
    for i in range(2):
        eq.append((-vv*(Ar[i]+(beta*vv if i==0 else 0)),Lr[i]+beta*vv*Tr[i]))
    eq.append((tra(A0)*(2-Y),2*const*(Y-S0)-beta*tra(T)*(2-Y)))
    g=RR.zero
    for (a,b),(c,d) in combinations(eq,2):g=g.gcd(a*d-b*c)
    for guard in [Y,Y-1,Y-2,Y-S0]:
        while (z:=g.gcd(guard)).degree()>0:g=g.exquo(z)
    print(label,'guarded rank gcd',g.degree(),g.monic().as_expr(),flush=True)
    assert g.degree()==0
for z in cases():compute(*z)
