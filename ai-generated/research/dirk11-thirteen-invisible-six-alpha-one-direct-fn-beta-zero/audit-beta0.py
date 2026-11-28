"""Independent QQ audit of both actual primitive and affine pins."""
import sympy as s
Y,X,t=s.symbols('Y X t')
ev=lambda f,y:s.expand(f).subs(Y,y)
I=lambda f:s.expand(s.integrate(f,Y))
eq=lambda a,b:s.cancel(a-b)==0

def check(r,u,c,c0,V,B,L,scale):
    c1=6*u*(c-r)/r
    assert c0*(r*r-3*u)==u*u*(3*c-4*r)
    R=Y**3+c*Y**2+c1*Y+c0
    m=scale*(Y**2+r*Y+u);P=Y*m;P0=Y*R
    J4=L**4-14*L**3*Y+56*L**2*Y**2-84*L*Y**3+42*Y**4
    q=3*u*c-4*r*u-3*c0;p=r*c0;z=p/q;Z=q*Y-p
    n=s.resultant(R,m,Y);assert n!=0
    mi=s.invert(m,R,Y)
    fit=lambda f:s.rem(n*mi*f,R,Y)
    M,W,L1,Rho=map(fit,(J4,I(P0)/Y,I(P)/Y,I(I(P))/Y))
    assert s.Poly(L1,Y).degree()<=1
    U=M+t*R
    UV=ev(U,V);k=n*V*ev(J4,V)/UV
    Cq=ev(P0,V)*UV
    Kq=ev(Z,V)*(n*V*ev(J4,V)-ev(P,V)*UV)
    K=(V-z)*(k-ev(P,V))/ev(P0,V)
    assert eq(Kq,Cq*q*K)
    Q4=(Y-z)*P+K*P0
    T4=(Y-z)*L1/n-Rho/n+K*W/n
    Qnum=Cq*Z*P+Kq*P0
    Lnum=Cq*(Z*L1-q*Rho)+Kq*W
    assert eq(Qnum,Cq*q*Q4) and eq(Lnum,Cq*q*n*T4)
    fwd=U.subs(Y,L-X)
    JF=s.integrate(X*fwd,(X,0,L-B))
    JI=I((L-Y)*U)
    J=ev(JI,L)-ev(JI,B)
    assert eq(J,JF)
    C0,C1=(s.Poly(J,t).nth(i)for i in range(2))
    assert C1!=0
    for a in (V,B):
       UA=ev(U,a)
       hg=UA*ev(I(Qnum),a)-a*ev(J4,a)*ev(Lnum,a)
       raw=ev(I(Q4),a)-n*a*ev(J4,a)*ev(T4,a)/UA
       assert eq(hg, Cq*q*UA*raw)
       hp=s.Poly(hg,t)
       assert hp.degree()<=2
       y0,y1,y2=(hp.nth(i)for i in range(3))
       assert eq(C1*C1*y0-C1*C0*y1+C0*C0*y2,C1*C1*hg.subs(t,-C0/C1))

# Different live scales, the adjacent V=z contact, and r²=3s are all tested.
F=s.Rational
for row in [
    (2,3,5,-F(63,5),F(2,3),F(6,7),1,7),
    (2,3,5,-F(63,5),F(-3,7),F(6,7),1,7),
    (3,3,4,5,F(3,7),F(7,8),3,9),
    (-4,7,9,-F(2107,5),F(3,7),F(7,8),3,9),
]:
    check(*map(F,row))
print("Four independent QQ audits of J_B, both reverse primitive rows, and both pins.")
