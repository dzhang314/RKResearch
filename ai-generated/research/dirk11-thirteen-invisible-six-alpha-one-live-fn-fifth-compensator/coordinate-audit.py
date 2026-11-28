"""Independent rational-coordinate audit of the two cleared beta-one gates."""
import sympy as S
Y=S.symbols('Y')
R0=S.Rational
I=lambda f:S.Poly(S.integrate(f,Y),Y).as_expr()
E=lambda f,y:S.expand(f).subs(Y,y)
cf=lambda f,i:S.Poly(f,Y).nth(i)
eq=lambda f,g: S.expand(f-g)==0
def verify(r,s,c,V,B,A,m0,K,q):
    c0=s*s*(3*c-4*r)/(r*r-3*s);c1=6*s*(c-r)/r
    R=Y**3+c*Y**2+c1*Y+c0
    m=m0*(Y**2+r*Y+s);P=Y*m;P0=Y*R;P5=(Y-V)*P0
    z=r*s/(r*r-6*s);p=q*z;Z=q*Y-p;e=q*K
    J4=A**4-14*A**3*Y+56*A*A*Y**2-84*A*Y**3+42*Y**4
    n=S.resultant(m,R,Y);mi=S.invert(m,R,Y)
    fit=lambda g:S.rem(mi*g,R,Y)
    M,W,l,rho=map(fit,(J4,I(P0)/Y,I(P)/Y,I(I(P))/Y))
    Q4=(Y-z)*P+K*P0
    Qh=Z*P+e*P0
    LL=(Y-z)*l-rho+K*W;Lh=n*q*LL
    lm=cf(LL,2);x=-cf(LL,1)/lm-z
    assert x!=z and eq(LL,lm*(Y-z)*(Y-x))
    xn=-(q*cf(Lh,1)+p*cf(Lh,2));xd=q*cf(Lh,2)
    assert x==xn/xd
    hp=E(Qh,V);rv=E(R,V);jv=E(J4,V);zv=q*(V-z)
    k=E(P,V)+K*E(P0,V)/(V-z)
    assert hp==zv*k
    U=M+(V*jv/k-E(M,V))*R/rv
    SM=n*(rv*M-E(M,V)*R)
    Sh=hp*SM+n*zv*V*jv*R
    assert eq(Sh,n*rv*hp*U)
    fB=n*rv*hp*Z*Y*J4-Qh*Sh
    Bz,rem=S.div(fB,P5,Y)
    assert eq(rem,0)
    ub=E(Sh,B);bb=A-B;Bx=B-x
    eB=((B-z)*B*E(J4,B)/E(U,B)-E(Q4,B))/E(P5,B)
    assert E(Bz,B)==q*ub*eB
    Ju=I((A-Y)*Sh)
    jb=E(Ju,A)-E(Ju,B)
    db=jb/(bb*ub)
    assert db==(E(I(Y*U.subs(Y,A-Y)),bb))/(bb*E(U,B))
    assert jb*xd-bb*ub*(B*xd-xn)==xd*bb*ub*(db-Bx)
    eta=(R0(1,5)-lm)*cf(Q4,4)
    etaN=(n*q/5-cf(Lh,2))*cf(Qh,4)
    etaD=n*q*q
    OmN=(B*xd-xn)*E(Bz,B);OmD=xd*q*ub
    assert etaN/etaD==eta and OmN/OmD==Bx*eB
    nu=eta-(1+lm)*Bx*eB
    nuN=etaN*OmD-q*(n*q+cf(Lh,2))*OmN;nuD=etaD*OmD
    assert nuN/nuD==nu
    assert jb*xd*nuN-bb*ub*(B*xd-xn)*(nuN+etaD*OmN)==xd*bb*ub*nuD*(db*nu-Bx*(nu+Bx*eB))
    adj=q*etaN*V*c0+xn*cf(Qh,1)
    aux,rem=S.div(I(Qh)-lm*(Y-x)*Qh,P0,Y)
    assert eq(rem,0)
    assert adj==c0*n*q*q*E(aux,V)
    Dc=(I(Y*P0)-V*I(P0))/Y
    F=fit(Dc)
    Fe=F+(E(Dc,V)*E(U,V)/jv-E(F,V))*R/rv
    Q5=Fe-E(Fe,z)*U/E(U,z)
    SD=n*(rv*F-E(F,V)*R)
    X=lambda a,b:q**3*(E(a,z)*b-E(b,z)*a)
    Qp=hp*X(SM,SD)+n*zv*V*E(Dc,V)*X(SM,R)-n*zv*V*jv*X(SD,R)
    Sz=q**3*E(Sh,z)
    assert eq(Qp,n*rv*Sz*Q5)
    # The quotient arithmetic is exact even on these off-chart probes;
    # at a true candidate its discarded remainder is zero.
    dd=q*q*S.div(Qp,Y-z,Y)[0]
    L5=S.div(Q5,(Y-z)*(Y-x),Y)[0]
    C0=xd*cf(dd,1)+xn*cf(dd,2);C1=xd*cf(dd,2)
    Cd=xd*q*q*n*rv*Sz
    assert eq(C0+C1*Y,Cd*L5)
    yn=xn*nuD*Cd+n*q*q*nuN*C0
    yd=q*cf(Lh,2)*nuD*Cd-n*q*q*nuN*C1
    assert yn==n*q*q*nuD*Cd*(lm*x+nu*cf(L5,0))
    assert yd==n*q*q*nuD*Cd*(lm-nu*cf(L5,1))
    y=yn/yd
    Dc4=(Y-V)*R
    sx=xd**3*E(Sh,x); dz=q**4*E(Dc4,z); dx=xd**4*E(Dc4,x)
    dXZ=q*xn-p*xd
    Tden=dXZ*Sz*sx
    Cn=Tden*Dc4-Sh*((xn-xd*Y)*dz*sx+Z*dx*Sz)
    Ed=Dc4-Sh*((x-Y)*E(Dc4,z)/E(Sh,z)+(Y-z)*E(Dc4,x)/E(Sh,x))/(x-z)
    assert eq(Cn,Tden*Ed)
    Cr,rem=S.div(Cn,(Y-z)*(Y-x),Y)
    assert eq(rem,0)
    Cq=q**3*xd*xd*Cr
    chi=-db*db*E(U,B)/E(J4,B)
    Late=bb*n*rv*hp*E(J4,B)*q**3*xd*xd*Tden*((Y-B)*bb*ub-jb)*(C0+C1*Y)-jb*jb*Cd*Cq
    scale=bb**2*ub*n*rv*hp*E(J4,B)*q**3*xd*xd*Tden*Cd
    pure=(Y-B-db)*L5+chi*S.cancel(Ed/((Y-z)*(Y-x)))
    assert eq(Late,scale*pure)
    assert E(Late,y)==scale*E(pure,y)
for sample in [(2,3,5,R0(2,3),R0(6,7),1,7,R0(-3,7),6),
               (-4,7,9,R0(3,7),R0(7,8),3,9,R0(7,8),11),
               (5,-4,7,R0(1,3),R0(5,7),5,12,R0(3,11),-5),
               (3,1,-2,R0(2,7),R0(3,7),7,16,R0(4,5),7)]:
    verify(*map(R0,sample))
print('Four QQ coordinate audits reproduce the B kernel gate, and the affine and quadratic late gates.')
