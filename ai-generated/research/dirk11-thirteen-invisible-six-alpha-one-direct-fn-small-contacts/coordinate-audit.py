"""Independent exact rational numerator checks for Adj, Q and middle gates."""
import sympy as S
Y=S.symbols('Y')
I=lambda p:S.Poly(S.integrate(p,Y),Y).as_expr()
ev=lambda f,x:S.expand(f).subs(Y,x)
deg=lambda f:S.Poly(f,Y).degree()
J4=42*Y**4-84*Y**3+56*Y**2-14*Y+1
rat=S.Rational
def check(r,s,c2,V,K,p,q):
    c0=s*s*(3*c2-4*r)/(r*r-3*s)
    c1=6*s*(c2-r)/r
    R=Y**3+c2*Y**2+c1*Y+c0
    m=Y**2+r*Y+s
    z=p/q
    P=Y*m
    P0=Y*R
    P5=(Y-V)*P0
    L0=S.cancel(I(P0)/Y)
    L1=S.cancel(I(Y*P0)/Y)
    inv=S.invert(m,R,Y)
    fit=lambda t:S.rem(inv*t,R,Y)
    M,w,ell,rho=[fit(a) for a in (J4,L0,S.cancel(I(P)/Y),S.cancel(I(I(P))/Y))]
    assert all(ev(a,z)==0 for a in (w,ell,rho))
    n=S.resultant(m,R,Y)
    L=(Y-z)*ell-rho+K*w
    x=-S.Poly(L,Y).nth(1)/S.Poly(L,Y).nth(2)-z
    assert ev(L,x)==0 and x!=z
    Q=(Y-z)*P+K*P0
    rv=ev(R,V); pv=ev(P0,V)
    jv=ev(J4,V); hv=V*jv
    k=ev(P,V)+K*pv/(V-z)
    assert k!=0
    d=(ev(I(P0),V)-ev(w,V)*k)/pv
    U=M+(hv/k-ev(M,V))*R/rv
    D=L1-V*L0
    DD=fit(D)
    Beff=DD + (ev(D,V)*ev(U,V)/jv-ev(DD,V))*R/rv
    Q5=Beff-ev(Beff,z)*U/ev(U,z)
    Qc=-d*d*V/k*(R-ev(R,z)*U/ev(U,z))
    ac=ev(L,V)*k-ev(I(Q),V)
    # Independently reconstruct the homogenized short exact formulas.
    QR=q*ev(Q,V); zeta=q*(V-z)
    Mhat=n*M; Dhat=n*DD
    SM=rv*Mhat-ev(Mhat,V)*R; SD=rv*Dhat-ev(Dhat,V)*R
    Sg=QR*SM+n*zeta*hv*R
    assert S.expand(Sg-n*rv*QR*U)==0
    Q4=q*Q; ML=q*n*L
    xden=q*S.Poly(ML,Y).nth(2); xnum=-(q*S.Poly(ML,Y).nth(1)+p*S.Poly(ML,Y).nth(2))
    assert xnum==x*xden
    adj=S.div(S.expand(ML*Q4-n*(q*Y-p)*I(Q4)),P0,Y)
    assert adj[1]==0 and ev(adj[0],V)==q*n*zeta*ac/pv
    cross=lambda a,b:q**3*(ev(a,z)*b-ev(b,z)*a)
    QS=QR*cross(SM,SD)+n*zeta*V*ev(D,V)*cross(SM,R)-n*zeta*hv*cross(SD,R)
    GQ=xden*xden*q*q*ev(QS,x)/(x-z)
    assert GQ==xden*xden*q**5*(n*rv)**2*QR*ev(U,z)*ev(Q5,x)/(x-z)
    Dden=n*zeta*pv
    Dnum=n*zeta*ev(I(P0),V)-n*ev(w,V)*QR
    assert Dnum==Dden*d
    CExpr=q**3*ev(Sg,z)*((Y-V)*Dden-Dnum)*(n*w)-Dnum**2*cross(Mhat,R)
    GM=xden*xden*q*q*ev(CExpr,x)/(x-z)
    assert GM==xden*xden*q**5*ev(Sg,z)*Dden*n*((x-V-d)*ev(w,x)+ev(Qc,x))/(x-z)
    # Check the reflection used by the independently audited optional B read.
    B=rat(7,9); b=1-B
    assert ev(I((1-Y)*Sg),1)-ev(I((1-Y)*Sg),B)==ev(I(Y*Sg.subs(Y,1-Y)),b)
for r,s,c,V,K,q in [(2,3,5,rat(2,3),rat(-3,7),6),(-4,7,9,rat(3,7),rat(7,8),11),
                       (5,-4,7,rat(1,3),rat(3,11),-5),(3,1,-2,rat(2,7),rat(4,5),7)]:
    r,s,c,q=map(S.Integer,(r,s,c,q))
    z=r*s/(r*r-6*s)
    check(r,s,c,V,K,z*q,q)
print('QQ coordinate audit: exact Adj, Q, middle and reflection identities in four independent scaled evaluations.')
