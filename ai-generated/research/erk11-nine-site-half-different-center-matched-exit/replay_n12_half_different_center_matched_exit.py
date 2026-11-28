"""Exact standalone half-half matched central exit; SymPy and python-flint.

The arithmetic is rational or in exact irreducible rational coefficient
fields. There is no numerical root scouting or finite-field tableau test.
"""
import sympy as sy
from sympy import QQ
from sympy.polys.rings import ring
from functools import reduce
import flint
N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],[-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
T4=[1,-32,216,-480,330]
U4=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
def ev(cs,q):return sum(c*q**i for i,c in enumerate(cs))
def dot(g,h):return sum(g[i]*N[i][j]*h[j] for i in range(5) for j in range(5))
def integ(f,j=0):return sum(c/(q[0]+j+1) for q,c in f.items())
def at(f,z):return sum(c*z**q[0] for q,c in f.items())
def hom(f,z,zD):
    n=f.degree()
    return sum(T(c)*z**i[0]*zD**(n-i[0]) for i,c in f.items())
def build(K):
    ar,a0=ring('a',K)
    global T
    T,x=ring('x',ar)
    W,X=ring('X',T)
    a=T(a0); b=2-a; h=a/2; d=a-1
    V=X**2*(X-a)**2
    U=(1-X)**2*(X-d)**2
    prim=lambda f:sum(c*X**(q[0]+1)/(q[0]+1) for q,c in f.items())
    P=prim(V)
    _Q=prim(U)
    Q=W(sum(_Q.values()))-_Q
    H=integ(P*U);C1=integ(P*U,1);C2=integ(V*Q,1);J=integ(P*Q)
    I0,I1,I2=[integ(V*U,j) for j in range(3)]
    A=H*H-J*I0;B=J*I1-H*C1;C=J*I1-H*C2;D=C1*C2-J*I2
    Del=A*D-B*C
    E=A*x+C;Y=-(B*x+D);II=E*(I2-x*I1)+Y*(x*I0-I1)
    al=E*C1-Y*H;be=C2-x*H
    P5=(X-a)*(X-h)*(X-d)*(X-x)*(E*X-Y)
    mo=[integ(X*(1-X)*P5,j) for j in range(4)]
    EL=lambda q:[q**(i+1) for i in range(5)]
    ER=lambda q:[(1-q)*q**i for i in range(5)]
    dl0=[T.one]+[T.zero]*4;dl1=[(i+1)*a**i for i in range(5)]
    dr0=[T.one]*5;dr1=[d**i-(b*i*d**(i-1) if i else 0) for i in range(5)]
    Dx=[a**5*q-30*at(P,x)*r for q,r in zip(EL(x),EL(a))]
    Fx=[b**5*q-30*at(Q,x)*r for q,r in zip(ER(x),ER(d))]
    K0,K1=[dot(Dx,r).exquo(a*x*(a-x)) for r in [dr0,dr1]]
    KL0,KL1=[dot(l,Fx).exquo(b*(1-x)*(x-d)) for l in [dl0,dl1]]
    Ta,Tb=ev(T4,a),ev(T4,b)
    Uab=ev([ev(row,b) for row in U4],a)
    Gam0=K1-Tb*K0;Gam1=Ta*K1-Uab*K0
    td=(Y-d*E)*K0+(E-Y)*K1
    tn=d*(Y-d*E)*K0+(E-Y)*K1
    En0,En1,En2=[td*mo[j+1]-tn*mo[j] for j in range(3)]
    F1=(a*td-tn)*(a-x)*Gam0-tn*x*Gam1
    F2=Gam1*hom(KL0,Y,E)-Gam0*hom(KL1,Y,E)
    F3=En0*En2-En1**2
    return locals()

def lift_polynomial(f, ar, K, x_ring):
    aa=K.unit
    def c(u):
        out=K.zero
        for j in range(u.degree(),-1,-1):
            out=out*aa+K.convert(u.get((j,),0))
        return out
    return x_ring.from_dict({k:c(u) for k,u in f.items()})

def field(f,degree):
    assert f.degree()==degree and f.is_irreducible
    K=QQ.algebraic_field(sy.CRootOf(f,0))
    assert K.mod.degree()==degree
    return K

def from_sympy_rational(u):
    return flint.fmpq(int(u.numerator),int(u.denominator))

def setup():
    q=build(QQ)
    a,b,x=q["a"],q["b"],q["x"]
    # These are all the removed factors, every one live.
    p1=q["F1"].exquo(a*b*b*x*(x-a))
    p2=q["F2"].exquo(a*b**5)
    p3=q["F3"].exquo(b*b)
    return q,p1,p2,p3

def verify_singular(q):
    a0=q["a0"]; aa=a0.as_expr()
    K0,K1=q["K0"],q["K1"]
    res=K0.resultant(K1)
    fs=res.factor_list()[1]
    assert sorted((f.degree(),k) for f,k in fs)==[(1,3),(1,12),(21,1)]
    assert {f.monic() for f,k in fs if f.degree()==1}=={a0,a0-2}
    f=sy.Poly(next(f for f,k in fs if f.degree()==21).as_expr(),aa,domain=QQ)
    K=field(f,21)
    R,X=ring("X",K)
    cv=lambda g:lift_polynomial(g,q["ar"],K,R)
    common=cv(K0).gcd(cv(K1)).monic()
    assert common.degree()==1
    xv=-common[(0,)]
    evaluate=lambda p:cv(p).evaluate(X,xv)
    a=K.unit
    assert all(xv-r for r in (K.zero,K.one,a,a-1,a/2))
    Ed=evaluate(q["E"])
    assert Ed and evaluate(q["Del"])
    yv=evaluate(q["Y"])/Ed
    r0=cv(q["KL0"]).evaluate(X,yv)
    r1=cv(q["KL1"]).evaluate(X,yv)
    assert r0 and r1
    td=(a-xv)*r0+xv*r1
    tn=a*(a-xv)*r0
    assert td
    t=tn/td
    m0,m1,m2,m3=map(evaluate,q["mo"])
    p0,p1,p2=m1-t*m0,m2-t*m1,m3-t*m2
    assert p0 and p0*p2-p1*p1
    print("true K0=K1 dropout: exact degree-21 fiber contradicted")
    return f.monic()

def verify_regular(q,p1,p2,p3,singular):
    ctx=flint.fmpq_mpoly_ctx.get(("a","x"))
    cv=lambda p:ctx.from_dict({(j,i):from_sympy_rational(c)
                       for (i,),u in p.items() for (j,),c in u.items()})
    f1,f2,f3=map(cv,(p1,p2,p3))
    assert [f.degrees() for f in (f1,f2,f3)]==[(24,6),(34,6),(52,12)]
    r,s=f1.resultant(f2,"x"),f1.resultant(f3,"x")
    assert (r.degrees(),s.degrees())==((326,0),(556,0))
    common=r.gcd(s)
    assert common.degrees()==(194,0)
    aa=q["a0"].as_expr()
    g=sy.Poly(sy.sympify(str(common)),aa,domain=QQ)
    fs=g.factor_list()[1]
    assert sorted((f.degree(),k) for f,k in fs)==[(1,2),(1,46),(4,3),(6,8),(17,1),(21,2),(27,1)]
    seen=set()
    for f,k in fs:
        d=f.degree()
        if d in (1,4,6):
            assert not sy.rem(q["Del"][(0,)].as_expr(),f.as_expr(),aa)
            continue
        K=field(f,d)
        R,X=ring("X",K)
        into=lambda v:lift_polynomial(v,q["ar"],K,R)
        common_x=into(p1).gcd(into(p2)).gcd(into(p3)).monic()
        assert common_x.degree()==1
        if d==17:
            guard=q["Y"]-q["E"]
            note="y=1"
        elif d==21:
            assert f.monic()==singular
            guard=q["K0"]
            note="K0=0 (already closed full dropout)"
        elif d==27:
            guard=q["Y"]-q["d"]*q["E"]
            note="y=d"
        else:
            raise AssertionError(d)
        assert not into(guard).rem(common_x)
        seen.add(d)
        print(f"exact degree-{d} width fiber: linear gcd forces {note}")
    assert seen=={17,21,27}

if __name__=="__main__":
    q,p1,p2,p3=setup()
    s=verify_singular(q)
    verify_regular(q,p1,p2,p3,s)
