"""Check the literal reverse polynomial coordinate formulas over QQ."""
import sympy as S
Y,E=S.symbols('Y E')
I=lambda a:S.Poly(S.integrate(a,Y),Y).as_expr()
rat=S.Rational
cf=lambda f,i:S.Poly(f,Y).nth(i)
def audit(r,s,c,V,L,m0,q):
    c0=s*s*(3*c-4*r)/(r*r-3*s);c1=6*s*(c-r)/r
    R=Y**3+c*Y**2+c1*Y+c0
    m=m0*(Y**2+r*Y+s)
    n=S.resultant(m,R,Y)
    P=Y*m;P0=Y*R;P5=(Y-V)*P0
    z=r*s/(r*r-6*s);Z=q*(Y-z)
    mI=S.invert(m,R,Y)
    fit=lambda f:n*S.rem(mI*f,R,Y)
    el,rho,W=map(fit,(I(P)/Y,I(I(P))/Y,I(P0)/Y))
    Q=Z*P+E*P0
    Lh=Z*el-q*rho+E*W
    assert S.expand(I(Q)-(Z*I(P)-q*I(I(P))+E*I(P0)))==0
    assert S.rem(S.expand(Lh*Q-n*Z*I(Q)),P0,Y)==0
    H=Y*(L**4-14*L**3*Y+56*L*L*Y**2-84*L*Y**3+42*Y**4)
    C1=I(P5)-Y*P5/6;C2=L**4*P5-cf(P5,1)*H
    assert all(cf(f,i)==0 for f in (C1,C2,I(Q),I(P0))for i in (0,1))
    assert all(S.degree(f,Y)<=5 for f in (C1,C2,I(Q),I(P0)))
    def trim(f):
        ff=Z*f
        return ff-cf(ff,6)*Y*P5
    I0,I1=trim(I(Z*P)),trim(I(P0))
    assert S.expand(trim(I(Q))-(I0+E*I1))==0
    assert all(cf(f,i)==0 for f in (I0,I1,trim(I(Q)))for i in (0,1,6))
    def det(*fs):
        return S.Matrix.hstack(*(S.Matrix([cf(f,i)for i in range(2,6)])for f in fs)).det()
    assert S.expand(det(C1,C2,trim(I(Q)),I1)-det(C1,C2,I0,I1))==0
for w in [(2,3,5,rat(2,3),3,7,11),(-4,7,9,rat(3,7),5,-5,8),
          (5,-4,7,rat(1,3),7,12,13),(3,1,-2,rat(2,7),6,16,31)]:
    audit(*map(rat,w))
print('Four QQ coordinate audits: exact primitive, old adjacent division, scaled endpoint, leading removal and K-independent determinant.')
