"""Independent QQ scale and exterior-square check for the compact seed."""
import sympy as s
Y=s.symbols('Y')
I=lambda f:s.expand(s.integrate(f,Y))
E=lambda f,z:s.expand(f).subs(Y,z)
cf=lambda f,i:s.Poly(f,Y).nth(i)
eq=lambda a,b:s.cancel(a-b)==0

def check(r,t,c,V,B,L,mult,K,q):
    c0=t*t*(3*c-4*r)/(r*r-3*t)
    c1=6*t*(c-r)/r
    R=Y**3+c*Y**2+c1*Y+c0
    m=mult*(Y**2+r*Y+t);P=Y*m;P0=Y*R
    J4=L**4-14*L**3*Y+56*L**2*Y**2-84*L*Y**3+42*Y**4
    D0=(I(Y*P0)-V*I(P0))/Y
    A=s.Matrix(3,3,lambda i,j: cf(s.rem(Y**j*m,R,Y),i))
    n=A.det()
    assert n!=0
    mi=s.invert(m,R,Y)
    fit=lambda f:s.rem(n*mi*f,R,Y)
    M,D,W,l,rho=map(fit,(J4,D0,I(P0)/Y,I(P)/Y,I(I(P))/Y))
    z=r*t/(r*r-6*t);p=q*z;Z=q*Y-p
    assert all(eq(E(f,z),0)for f in (W,l,rho))
    e=q*K;L0=Z*l-q*rho;Lh=L0+e*W
    x=-cf(Lh,1)/cf(Lh,2)-z
    assert x!=z
    N=-(q*cf(L0,1)+p*cf(L0,2)+q*cf(L0,2)*x)
    Den=q*cf(W,1)+p*cf(W,2)+q*cf(W,2)*x
    assert Den!=0 and e==N/Den
    Q=Z*P+e*P0;Qx=Den*Z*P+N*P0
    assert eq(Qx,Den*Q)
    a=cf(Lh,2)
    ax=cf(L0,2)*Den+N*cf(W,2)
    AdjX=(n*q*Den/5-ax)*cf(Qx,4)*V*c0+ax*x*cf(Qx,1)
    Adj=q*(n*q/5-a)*cf(Q,4)*V*c0-(q*cf(Lh,1)+p*a)*cf(Q,1)
    assert q*AdjX==Adj*Den**2
    Rv=E(R,V);SM=Rv*M-E(M,V)*R;SD=Rv*D-E(D,V)*R
    C=lambda f,g:s.cancel(q*q*(E(f,z)*g-E(g,z)*f)/(Y-z))
    v3=lambda f:s.Matrix([cf(s.rem(f,R,Y),i)for i in range(3)])
    ww=A.T*(v3(J4).cross(v3(D0)))
    assert v3(M).cross(v3(D))==n*ww
    Delta=0
    for i,j,k,sg in [(0,1,2,1),(0,2,1,-1),(1,2,0,1)]:
        Delta+=sg*ww[k]*(Rv*C(Y**i,Y**j)-V**j*C(Y**i,R)+V**i*C(Y**j,R))
    assert eq(Delta,C(SM,SD)/(n*Rv))
    new=E(Qx,V)*Delta+(q*V-p)*V*Den*(E(D0,V)*C(M,R)-E(J4,V)*C(D,R))
    CC=lambda f,g:s.expand(q**3*(E(f,z)*g-E(g,z)*f))
    old=E(Q,V)*CC(SM,SD)+n*(q*V-p)*V*(E(D0,V)*CC(SM,R)-E(J4,V)*CC(SD,R))
    assert eq(new,Den*old/(q*n*Rv*(Y-z)))
    assert eq(E(new,x),Den*E(old,x)/(q*n*Rv*(x-z)))
for t in [(2,3,5,s.Rational(2,3),s.Rational(6,7),1,7,s.Rational(-3,7),6),
          (-4,7,9,s.Rational(3,7),s.Rational(7,8),3,9,s.Rational(7,8),11),
          (5,-4,7,s.Rational(1,3),s.Rational(5,7),5,12,s.Rational(3,11),-5),
          (3,1,-2,s.Rational(2,7),s.Rational(3,7),7,16,s.Rational(4,5),7)]:
    check(*map(s.Rational,t))
print("Four independent exact QQ checks: Möbius carrier, primitive sign, exterior square, compact true quintic.")
