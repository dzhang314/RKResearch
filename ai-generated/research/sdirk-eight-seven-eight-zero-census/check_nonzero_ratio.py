"""Seven-zero, low-label, pure varying pair and singleton, nonzero reflected ratio."""
import sympy as S
from sympy.polys.rings import ring
U0,V0,X0=S.symbols("u v x")
def Q(t):return t**3-3*t**2+S.Rational(3,4)*t+S.Rational(1,2)
red=lambda p:S.rem(S.rem(S.expand(p),Q(U0),U0),Q(V0),V0)
basis=[U0**i*V0**j for i in range(3) for j in range(3)]
vec=lambda a:S.Matrix([S.Poly(a,U0,V0).coeff_monomial(e) for e in basis])
B=S.Matrix.hstack(*(vec(red((U0+2*V0)**k)) for k in range(9)))
I=B.inv()
ucoef=I*vec(U0);vcoef=I*vec(V0)
assert red(sum(c*(U0+2*V0)**i for i,c in enumerate(ucoef))-U0)==0
assert red(sum(c*(U0+2*V0)**i for i,c in enumerate(vcoef))-V0)==0
f=S.Poly(S.resultant(Q(U0),Q((X0-U0)/2),U0),X0).monic()
assert f.degree()==9 and red(f.as_expr().subs(X0,U0+2*V0))==0
parts=f.factor_list()[1]
assert sorted(q.degree() for q,e in parts)==[3,6] and all(e==1 for q,e in parts)
def det(M):
 a,b,c=M
 return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
def L(t,D):return 70*t**4-140*D*t**3+90*D**2*t*t-20*D**3*t+D**4
for ff,e in parts:
    sym=S.Symbol("theta"+str(ff.degree()))
    K=S.QQ.algebraic_field((S.Poly(ff.as_expr().subs(X0,sym),sym),sym));z=K.unit
    C=lambda a,b=1:K.convert(S.Rational(a,b))
    u=sum((K.convert(c)*z**i for i,c in enumerate(ucoef)),K.zero)
    v=sum((K.convert(c)*z**i for i,c in enumerate(vcoef)),K.zero)
    assert u+2*v==z
    assert all(not (t**3-3*t*t+C(3,4)*t+C(1,2)) for t in (u,v))
    assert (u==v)==(ff.degree()==3)
    a=1+2*u

    R,X=ring(f"X{ff.degree()}",K)
    P0=[1+u,-2-u,K.one]
    ev=lambda X:sum((q*X**i for i,q in enumerate(P0)),R.zero)
    J=lambda k,X:sum((q*X**(i+k+1)*C(1,i+k+1) for i,q in enumerate(P0)),R.zero)
    assert J(0,R(a))==ev(R(a))
    for d0 in (0,1):
        D=1+a+d0*v
        s=D-1;t=D-1-v;r=D-1-2*v
        other=t if d0==0 else s
        assert a in (s,t) and len({s,t,r})==3
        # The four-mass case must have the repeated clock a canceled, so
        # both the other terminal label and the live third label are Gaussian.
        assert L(other,D) or L(r,D)
        # If all five labels live, the two unknown ordinary clocks are
        # roots of a monic quadratic from the mask on the three known.
        P=(X-s)*(X-t)*(X-r)
        def I(p):return sum((c*D**i*C(1,i+1) for (i,),c in p.items()),K.zero)
        m0,m1,m2,m3,m4=[I(P*X**k) for k in range(5)]
        H=det([[m0,m1,m2],[m1,m2,m3],[m2,m3,m4]])
        print(ff.degree(),d0,'equal first-and-terminal H nonzero?',bool(H),flush=True)
        if H:continue
        delta=m0*m2-m1*m1
        if not delta:
            print("zero ordinary pivot, impossible at two distinct live unknowns");continue
        q0=(m1*m3-m2*m2)/delta;q1=(m1*m2-m0*m3)/delta
        q=X*X+q1*X+q0
        g=L(a,D)*(a*(J(0,X)-ev(X))+X*ev(X)-J(1,X))-L(X,D)*(a*ev(R(a))-J(1,R(a)))
        print('second is other terminal possible?',not g.evaluate(X,other),'unseen gcd',q.gcd(g).degree(),flush=True)
        assert g.evaluate(X,other) and q.gcd(g).degree()==0
    T,D=ring(f"D{ff.degree()}",K)
    Z,Y=ring(f"Y{ff.degree()}",T.to_domain())
    x=lambda u:Z(T(u))
    S0=D-1;T0=D-1-v;R0=D-1-2*v
    P=(Y-x(S0))*(Y-x(T0))*(Y-x(R0))*(Y-x(a))
    def I(p):return sum((c*D**i*C(1,i+1) for (i,),c in p.items()),T.zero)
    m0,m1,m2,m3=[I(P*Y**k) for k in range(4)]
    g=(m0*m2-m1*m1).gcd(m0*m3-m1*m2)
    print(ff.degree(),'four-known exact ordinary gcd',g.degree(),flush=True)
    for guard in (D,m0,S0-a,T0-a,R0-a):
        while True:
            h=g.gcd(guard)
            if h.degree()==0:break
            g=g//h
    print("guarded",g.degree(),flush=True)
    assert g.degree()==0
