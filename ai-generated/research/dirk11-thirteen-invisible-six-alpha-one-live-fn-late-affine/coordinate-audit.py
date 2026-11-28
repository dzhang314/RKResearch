"""Independent exact rational audit of the pinned first-middle gate."""
import sympy as S
Y=S.symbols('Y')
I=lambda p:S.Poly(S.integrate(p,Y),Y).as_expr()
ev=lambda f,x:S.expand(f).subs(Y,x)
cf=lambda f,i:S.Poly(f,Y).nth(i)
rat=S.Rational
def audit(r,s,c,L,h,q):
    c0=s*s*(3*c-4*r)/(r*r-3*s)
    c1=6*s*(c-r)/r
    R=Y**3+c*Y**2+c1*Y+c0
    m=h*(Y**2+r*Y+s)
    P=Y*m;P0=Y*R
    J4=L**4-14*L**3*Y+56*L*L*Y**2-84*L*Y**3+42*Y**4
    mi=S.invert(m,R,Y);n=S.resultant(m,R,Y)
    fit=lambda f:S.rem(mi*f,R,Y)
    M,W,e,rho=map(fit,(J4,I(P0)/Y,I(P)/Y,I(I(P))/Y))
    z=r*s/(r*r-6*s);p=q*z
    K=(cf(rho,2)-cf(e,1)-1)/cf(W,2)
    x=z-ev(S.diff(rho,Y),z)+K*ev(S.diff(W,Y),z)
    eta=rat(6,5)*(h+K)
    Q4=(Y-z)*P+K*P0
    V=x*cf(Q4,1)/(eta*c0)
    assert x!=z and V!=z and ev(R,V)!=0
    assert S.expand(I(Q4)+(Y-x)*Q4-eta*(Y-V)*P0)==0
    cK=n*cf(W,2);aK=n*(cf(rho,2)-cf(e,1)-1)
    xn=p*n*cK-cK*n*(q*cf(rho,1)+2*p*cf(rho,2))+aK*n*(q*cf(W,1)+2*p*cf(W,2))
    xd=q*n*cK
    assert x==xn/xd
    zeta=q*(V-z);pv=ev(P0,V);rv=ev(R,V);jv=ev(J4,V)
    k=ev(P,V)+K*pv/(V-z)
    Kv=cK*zeta*ev(P,V)+q*aK*pv
    assert Kv==cK*zeta*k
    U=M+(V*jv/k-ev(M,V))*R/rv
    Sg=Kv*(rv*n*M-ev(n*M,V)*R)+n*cK*zeta*V*jv*R
    assert S.expand(Sg-Kv*n*rv*U)==0
    dv=(ev(I(P0),V)-k*ev(W,V))/pv
    Dden=n*cK*zeta*pv
    Dnum=n*cK*zeta*ev(I(P0),V)-ev(n*W,V)*Kv
    assert Dnum/Dden==dv
    CM=ev(n*M,z)*R-ev(R,z)*n*M
    # Literal transpose uses (x−V−d_V)W0+Q_c with the zero x diagonal.
    Qc=-dv**2*V/k*(R-ev(R,z)*U/ev(U,z))
    gate=q**5*xd**2*(ev(Sg,z)*((x-V)*Dden-Dnum)*ev(n*W,x)-Dnum**2*ev(CM,x))/(x-z)
    assert gate==q**5*xd**2*ev(Sg,z)*Dden*n*((x-V-dv)*ev(W,x)+ev(Qc,x))/(x-z)
for xx in [(2,3,5,1,7,11),(-4,7,9,3,-5,8),(5,-4,7,5,12,13),(3,1,-2,7,16,31)]:
    audit(*map(rat,xx))
print('Four QQ evaluations verify the homogeneous late-slope pin and literal first-middle scale.')
