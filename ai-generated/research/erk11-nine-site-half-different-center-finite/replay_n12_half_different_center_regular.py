"""Exact, standalone half-half different-extra central finite-atlas replay.

The only modular specialization is a test of a polynomial coefficient, not
of an unknown tableau. All vertical-fiber arithmetic is over the rationals.
"""
from sympy import QQ, GF
from sympy.polys.rings import ring

N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],[-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
T4=[1,-32,216,-480,330]
U4=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]

def ev(cs,q):return sum(c*q**i for i,c in enumerate(cs))
def dot(g,h):return sum(g[i]*N[i][j]*h[j] for i in range(5) for j in range(5))
def integ(f,j=0):return sum(c/(q[0]+j+1) for q,c in f.items())
def at(f,z):return sum(c*z**q[0] for q,c in f.items())
def coefficient_gates(K,aval=None):
    if aval is None:
        R,a=ring('a',K)
    else:
        R=K; a=K(aval)
    T,x=ring('x',R)
    P,z=ring('z',T)
    S,X=ring('X',T)
    b=2-a; h=a/2; d=a-1
    V=X**2*(X-S(T(a)))**2
    U=(1-X)**2*(X-S(T(d)))**2
    primitive=lambda f:sum(c*X**(q[0]+1)/(q[0]+1) for q,c in f.items())
    Prim=primitive(V)
    _Q=primitive(U)
    Back=S(sum(_Q.values()))-_Q
    H=integ(Prim*U);C1=integ(Prim*U,1);C2=integ(V*Back,1);J=integ(Prim*Back)
    I0,I1,I2=[integ(V*U,j) for j in range(3)]
    A=H*H-J*I0;B=J*I1-H*C1;C=J*I1-H*C2;D=C1*C2-J*I2
    E=A*x+C;Y=-(B*x+D)
    II=E*(I2-x*I1)+Y*(x*I0-I1)
    al=E*C1-Y*H;be=C2-x*H
    assert al*be==J*II
    P5=(X-S(T(a)))*(X-S(T(h)))*(X-S(T(d)))*(X-S(x))*(S(E)*X-S(Y))
    mo=[integ(X*(1-X)*P5,j) for j in range(4)]
    e0,e1,e2=[P(mo[j+1])-z*P(mo[j]) for j in range(3)]
    F=e0*e2-e1**2
    xp,yN,yD=P(x),P(Y),P(E)
    aa,bb,hh,dd=P(T(a)),P(T(b)),P(T(h)),P(T(d))
    evalL=lambda q:[q**(i+1) for i in range(5)]
    evalR=lambda q:[(1-q)*q**i for i in range(5)]
    l0=[P.one]+[P.zero]*4;l1=[(i+1)*aa**i for i in range(5)]
    r0=[P.one]*5;r1=[dd**i-(bb*i*dd**(i-1) if i else 0) for i in range(5)]
    lf=30*(P(al)*(z-xp)*at(V,z)-P(II)*at(Prim,z))
    rg=30*(P(be)*(z*yD-yN)*at(U,z)-P(II)*at(Back,z))
    EL=[(aa**5*P(II)*v+lf*w).exquo(z*(z-aa)) for v,w in zip(evalL(z),evalL(aa))]
    ER=[(bb**5*P(II)*v+rg*w).exquo((1-z)*(z-dd)) for v,w in zip(evalR(z),evalR(dd))]
    Di=210*dot(EL,ER)-aa**5*bb**5*P(II)*(z-xp)*(z*yD-yN)*z*(z-aa)*(1-z)*(z-dd)
    Out=[dict(F=F,Di=Di,mo=mo,e0=e0,E=E,Y=Y,I=II,al=al,be=be,x=x,a=a,ring=P)]
    for which in [0,1]:
        un,ud,vn,vd=(xp,P.one,yN,yD) if not which else (yN,yD,xp,P.one)
        lC=(aa*e0-e1)*(aa*ud-un);lB=-e1*un
        rC=(e1-dd*e0)*(vn-dd*vd);rB=-(e0-e1)*(vd-vn)
        L=[lC*v+lB*w for v,w in zip(l0,l1)]
        RR=[rC*v+rB*w for v,w in zip(r0,r1)]
        Out.append(dict(contact=dot(L,RR),left=dot(L,ER),right=dot(EL,RR)))
    return Out

def verify_transverse():
    K=GF(101)
    G,L,R=coefficient_gates(K,3)
    F,S=G["F"],G["Di"]
    assert (F.degree(),S.degree())==(2,6)
    r=F.resultant(S)
    assert r.degree()==32 and r.LC==K(25)
    for j,(chart,lead,res) in enumerate(((L,13,33),(R,44,26))):
        C=chart["contact"]
        assert C.degree()==2
        q=F.resultant(C)
        assert q.degree()==20 and q.LC==K(lead)
        assert r.resultant(q)==K(res)
        for eq in ("left","right"):
            assert chart[eq].degree()==4
            assert F.resultant(chart[eq]).degree()==26
        print(f"orientation {j}: fixed-degree width projection at a=3 is {res} mod 101")

def verify_vertical():
    G,L,R=coefficient_gates(QQ)
    a,x=G["a"],G["x"]
    F,S=G["F"],G["Di"]
    coeff_degree=lambda f:max(u.degree() for v in f.values() for u in v.values())
    assert coeff_degree(F)==22 and coeff_degree(S)==35
    assert all(coeff_degree(chart["contact"])<=38 for chart in (L,R))
    P,z=ring("z",a.ring)
    def specialize(F,k):
        return P.from_dict({i:g.evaluate(x,k) for i,g in F.items()})
    common=None
    for k in (3,4,5):
        f,s=specialize(F,k),specialize(S,k)
        assert (f.degree(),s.degree())==(2,6)
        u=f.resultant(s)
        assert u.degree()==202
        common=u if common is None else common.gcd(u)
        print(f"exact dormant-diagonal projection at x={k}: width degree 202")
    assert common.monic()==a*a*(a-2)**6
    print("common vertical width gcd: a^2(a-2)^6")

if __name__=="__main__":
    verify_transverse()
    verify_vertical()
