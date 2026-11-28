"""Eight exact two-active graph frames with first zero at physical row 3."""
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
    P0=[C(-1),C(2),C(-1,2)]
    P1=[1+u,-2-u,C(1)]
    for i in range(2):
        for rear in (9,10):
            D=2+i*u+(v if rear==9 else 0)
            print("frame",ff.degree(),i+1,rear,flush=True)
            if not D:
                print("zero D");continue
            s=D-1-2*v
            assert s != D-1 and s != D-1-v
            assert L(s,D), (ff.degree(),i,rear,"four Gaussian clocks still possible")
            if a==s:
                print("first/last ordinary repeat");continue
            def Jraw(P,k,t):return sum((z*t**(n+k+1)*C(1,n+k+1) for n,z in enumerate(P)),K.zero)
            def evraw(P,t):return sum((z*t**n for n,z in enumerate(P)),K.zero)
            def revF(P):return Jraw(P,0,D)-Jraw(P,0,s)-evraw(P,s)
            assert Jraw(P0,0,a)==evraw(P0,a) and Jraw(P1,0,a)==evraw(P1,a)
            s10=D-1;s9=D-1-v
            Rback=[s10*s9,-s10-s9,C(1)]
            assert not revF(Rback)
            r0=revF(P0);r1=revF(P1)
            if not r1:
                assert r0
                print("reverse first inconsistent");continue
            lam=-r0/r1
            P=[x+lam*y for x,y in zip(P0,P1)]
            assert evraw(P,a) and evraw(P,s10) and evraw(P,s9)
            m=[D**(k+2)*C(1,k+3)-(a+s)*D**(k+1)*C(1,k+2)+a*s*D**k*C(1,k+1) for k in range(6)]
            MM=[[m[i+j] for j in range(3)] for i in range(3)]
            Delta=det(MM)
            if not Delta:
                print("ordinary pivot zero");continue
            N=[]
            for p in range(3):
                XX=[t[:] for t in MM]
                for j in range(3):XX[j][p]=-m[j+3]
                N.append(det(XX)/Delta)
            n0,n1,n2=N
            for j in range(3):assert sum((m[j+k]*N[k] for k in range(3)),K.zero)==-m[j+3]
            T,Bc=ring(f"b{ff.degree()}_{i}_{rear}",K)
            qq=Bc**3+n2*Bc**2+n1*Bc+n0
            if qq.gcd(qq.diff(Bc)).degree()>0 or not qq.evaluate(Bc,a) or not qq.evaluate(Bc,s):
                print("ordinary cubic collision");continue
            assert L(a,D), (ff.degree(),i,rear,"first ordinary Gauss")
            def ev(poly,t):return sum((c*t**j for j,c in enumerate(poly)),T.zero)
            def J(poly,k,t):return sum((c*t**(j+k+1)*C(1,j+k+1) for j,c in enumerate(poly)),T.zero)
            def gate(P,bb):
                return L(a,D)*(a*(J(P,0,bb)-ev(P,bb))+bb*ev(P,bb)-J(P,1,bb)) \
                     - L(bb,D)*(a*evraw(P,a)-Jraw(P,1,a))
            gg=(gate(P,Bc)%qq).gcd(qq)
            print("parameter fixed, forward second gcd",gg.degree(),flush=True)
            assert gg.degree()==0
