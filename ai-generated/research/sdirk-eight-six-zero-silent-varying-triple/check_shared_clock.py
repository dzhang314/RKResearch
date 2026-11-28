"""Silent varying triple, its clock among the six zero labels."""
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
    for j in (0,1):
      d=1+j*u
      for repeated_other in (9,10):
        # d is the LIVE terminal ordinary site that does not require duplicate.
        nd=10 if repeated_other==9 else 9
        D=1+d+(v if nd==9 else 0)
        if not D:continue
        s=D-1;t=D-1-v;r=D-1-2*v
        assert d in (s,t) and len({s,t,r})==3
        known=set((s,t,r,a))
        if len(known)==3:
          assert a==(t if repeated_other==9 else s), (ff.degree(),j,nd,'unphysical coincidence')
          assert d*2==D and L(d,D)  # canceled ordinary duplicate would require d Gaussian
        P=R.one
        for x in known:P*=X-x
        def I(p):return sum((c*D**k*C(1,k+1) for (k,),c in p.items()),K.zero)
        if len(known)==3:
          m=[I(P*X**k) for k in range(5)]
          H=det([[m[i+j] for j in range(3)] for i in range(3)])
          if H:
            print(ff.degree(),j,nd,'rank-two ordinary contradiction');continue
          m0,m1,m2,m3,m4=m
          delta=m0*m2-m1*m1
          assert delta
          k=(m1*m2-m0*m3)/delta
          q=(m1*m3-m2*m2)/delta
          assert all(not (m[j]*q+m[j+1]*k+m[j+2]) for j in range(3))
          q2=X*X+k*X+q
          P0=[1+u,-2-u,K.one]
          ev=lambda z:sum((p*z**i for i,p in enumerate(P0)),R.zero)
          J=lambda k,z:sum((p*z**(i+k+1)*C(1,i+k+1) for i,p in enumerate(P0)),R.zero)
          assert J(0,R(a))==ev(R(a)) and L(a,D)
          F=L(a,D)*(a*(J(0,X)-ev(X))+X*ev(X)-J(1,X))-L(X,D)*(a*ev(R(a))-J(1,R(a)))
          assert F.gcd(q2).degree()==0
          print(ff.degree(),j,nd,'ordinary recurrence possible; forward gate gcd degree zero')
        else:
          m0,m1,m2,m3=[I(P*X**k) for k in range(4)]
          assert not m0 or m0*m2-m1*m1 or m0*m3-m1*m2
          print(ff.degree(),j,nd,'single unseen ordinary label contradiction')
