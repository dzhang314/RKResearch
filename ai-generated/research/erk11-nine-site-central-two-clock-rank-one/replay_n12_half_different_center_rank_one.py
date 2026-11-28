"""Standalone exact replay for all rank-one central half-different fibers.

SymPy rational polynomial arithmetic only. The CRootOf is solely the
generator of the complete irreducible rational coefficient field; no
root selection, sign filtering, or numerical approximation is used.
"""
import sympy as s
from sympy import QQ
from sympy.polys.rings import ring

A0=s.Symbol("a")
F4=33*A0**4-132*A0**3+176*A0**2-88*A0+16
F6=2475*A0**6-14850*A0**5+34140*A0**4-37560*A0**3+20136*A0**2-4752*A0+352
W4=[1,-32,216,-480,330]
U4=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],
    [216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],
    [330,-9240,55440,-110880,69300]]
N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],
   [-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]

def integral(f,j=0):
    return sum(c/(i[0]+j+1) for i,c in f.items())

def at(f,q):
    return sum(c*q**i[0] for i,c in f.items())

def ev(cs,v):
    return sum(c*v**i for i,c in enumerate(cs))

def dots(L,R):
    return sum(L[i]*N[i][j]*R[j] for i in range(5) for j in range(5))

def coefficient_field(f,n):
    p=s.Poly(f,A0,domain=QQ)
    assert p.degree()==n and p.is_irreducible
    K=QQ.algebraic_field(s.CRootOf(p,0))
    assert K.mod.degree()==n
    return K,K.unit

def model(R,a):
    b=2-a
    d=a-1
    h=a/2
    S,X=ring("X",R)
    VL=X**2*(X-a)**2
    VR=(1-X)**2*(X-d)**2
    primitive=lambda f: sum(c*X**(i[0]+1)/(i[0]+1) for i,c in f.items())
    P=primitive(VL)
    Q0=primitive(VR)
    Q=S(R(sum(Q0.values())))-Q0
    H=integral(P*VR)
    assert H==integral(VL*Q)
    C1=integral(P*VR,1)
    C2=integral(VL*Q,1)
    J=integral(P*Q)
    assert J==C1-C2
    I=[integral(VL*VR,j) for j in range(3)]
    Ta,Tb=ev(W4,a),ev(W4,b)
    Uab=ev([ev(row,b) for row in U4],a)
    return b,d,h,X,VL,VR,P,Q,H,C1,C2,J,I,Ta,Tb,Uab

def verify_width_identities():
    R,a=ring("a",QQ)
    b,d,h,X,V,B,P,Q,H,C1,C2,J,I,Ta,Tb,Uab=model(R,a)
    I0,I1,I2=I
    A=H**2-J*I0
    B=J*I1-H*C1
    C=J*I1-H*C2
    D=C1*C2-J*I2
    p4,p6=R.from_expr(F4),R.from_expr(F6)
    assert 41580*J==p4
    assert Uab-Ta*Tb==-16*a*(a-2)*p6
    assert 1646877554784000000*(A*D-B*C)==-a*a*(a-2)**2*p4*p6
    assert A.gcd(A*D-B*C).degree()==0
    assert B.gcd(C).gcd(D).degree()==0
    assert H.gcd(p4).degree()==0
    print("verified width determinant, two whole-algebra coefficient tests")

def verify_F4():
    K,aa=coefficient_field(F4,4)
    R,z=ring("z",K)
    a=R(aa)
    b,d,h,X,V,B,P,Q,H,C1,C2,J,I,Ta,Tb,Uab=model(R,a)
    assert J==0 and C1==C2 and H and Ta*Tb-Uab
    g=C1.exquo(H)
    assert all(g-r for r in (R.zero,R.one,a,h,d))
    dZ=[a**5*z**(i+1)-30*at(P,z)*a**(i+1) for i in range(5)]
    r0=[R.one]*5
    r1=[d**i-(b*i*d**(i-1) if i else 0) for i in range(5)]
    K0=dots(dZ,r0).exquo(a*z*(a-z))
    K1=dots(dZ,r1).exquo(a*z*(a-z))
    assert K0.gcd(K1).degree()==0
    G0=K1-Tb*K0
    G1=Ta*K1-Uab*K0
    P3=(X-a)*(X-h)*(X-d)
    for fixed in ("left","right"):
        # The fixed physical y=g can be either exclusive label.
        if fixed=="left":
            td=(a-g)*G0+g*G1
            tn=a*(a-g)*G0
            od=(tn-d*td)*K0+(td-tn)*K1
            on=d*(tn-d*td)*K0+(td-tn)*K1
        else:
            td=(g-d)*K0+(1-g)*K1
            tn=d*(g-d)*K0+(1-g)*K1
            od=(a*td-tn)*G0+tn*G1
            on=a*(a*td-tn)*G0
        hull=P3*(X-g)*(td*X-tn)*(od*X-on)
        m=X*(1-X)*(X-z)*hull
        f0,f1=integral(m),integral(m,1)
        assert (f0.degree(),f1.degree())==(10,10)
        assert f0.gcd(f1).degree()==0
        print(f"F4 fixed {fixed}: raw shifted degrees 10,10, gcd 1")

def verify_F6():
    K,aa0=coefficient_field(F6,6)
    R,z,y=ring("z,y",K)
    a=R(aa0)
    b,d,h,X,V,B,P,Q,H,C1,C2,J,I,Ta,Tb,Uab=model(R,a)
    I0,I1,I2=I
    A=H**2-J*I0
    Bc=J*I1-H*C1
    C=J*I1-H*C2
    D=C1*C2-J*I2
    assert A*D==Bc*C and A and J and H and Ta*Tb==Uab
    x0=-C.exquo(A)
    y0=-Bc.exquo(A)
    scale=C2-x0*H
    assert scale
    EL=lambda q:[q**(i+1) for i in range(5)]
    ER=lambda q:[(1-q)*q**i for i in range(5)]
    dl0=[R.one]+[R.zero]*4
    dl1=[(i+1)*a**i for i in range(5)]
    # Exact scaled central rows obtained from the four paid products.
    L=[a**5*l+30*(J.exquo(scale)*(z-x0)*at(V,z)-at(P,z))*r
       for l,r in zip(EL(z),EL(a))]
    RR=[b**5*(C1-y*H)*l+30*(J*(z-y)*at(B,z)-(C1-y*H)*at(Q,z))*r
        for l,r in zip(ER(z),ER(d))]
    null_R=[d**i-(b*i*d**(i-1) if i else 0)-Tb for i in range(5)]
    null_L=[v-Ta*w for v,w in zip(dl1,dl0)]
    assert not dots(L,null_R)  # This tempting extra test is redundant.
    F=dots(null_L,RR).exquo((1-z)**2*(z-d)**2)
    assert F.degrees()==(1,1)
    T,Y=ring("Y",K)
    co=lambda f,i:T.from_dict({(j,):c for (k,j),c in f.items() if k==i})
    zzD,zzN=co(F,1),-co(F,0)
    cc=lambda f:T.ground_new(f[(0,0)])
    aa,bb,dd,hh,xx,yy,Taa,Tbb=map(cc,[a,b,d,h,x0,y0,Ta,Tb])
    # The entire exceptional affine coefficient fiber is y=y0.
    assert zzD.gcd(zzN)==Y-yy
    zlD,zlN=zzD.exquo(Y-yy),zzN.exquo(Y-yy)
    assert zlD.degree()==0 and zlN.degree()<=0
    T2,Z=ring("X",T)

    def hull(side,which,yy1):
        u,v=(xx,yy1) if not which else (yy1,xx)
        if side=="R":
            td=v-dd+Tbb*(1-v)
            tn=dd*(v-dd)+Tbb*(1-v)
        else:
            td=aa-u+Taa*u
            tn=aa*(aa-u)
        return u,v,td,tn,(Z-aa)*(Z-hh)*(Z-dd)*(Z-xx)*(Z-yy1)*(td*Z-tn)

    # If left-null and y!=y0, the actual reflected offdiagonal fixes z.
    for which,deg in ((0,1),(1,2)):
        *_,h6=hull("L",which,Y)
        w=Z*(1-Z)*(zlD*Z-zlN)*h6
        p,q=integral(w),integral(w,1)
        assert (p.degree(),q.degree())==(deg,deg)
        assert p.gcd(q).degree()==0
        print(f"F6 left-null regular, orientation {which}: shifted gcd 1")

    # At y=y0, the true two shifted equations are linear in z.
    for side in ("R","L"):
        for which in range(2):
            *_,h6=hull(side,which,yy)
            w=Z*(1-Z)*(Z-Y)*h6
            p,q=integral(w),integral(w,1)
            assert (p.degree(),q.degree())==(1,1)
            assert p.gcd(q).degree()==0
            print(f"F6 both forced roots, {side}/{which}: shifted gcd 1")

    # The right-null case uses the two shifted rows and the reflected
    # dormant offdiagonal against the actual, generally non-null left row.
    lift=lambda f:R.from_dict({(0,k[0]):c for k,c in f.items()})
    for which,degs in ((0,(4,8)),(1,(2,5))):
        u,v,td,tn,h6=hull("R",which,Y)
        m0,m1,m2=[integral(Z*(1-Z)*h6,j) for j in range(3)]
        assert m0.gcd(m1).gcd(m2).degree()==0
        p=m0*m2-m1**2
        l0=(aa*td-tn)*(aa-u)
        l1=-tn*u
        left=[lift(l0)*v+lift(l1)*w for v,w in zip(dl0,dl1)]
        F=dots(left,RR).exquo((1-z)*(z-d))
        q=sum(T.from_dict({(j,):c})*m1**i*m0**(F.degree(z)-i)
              for (i,j),c in F.items())
        assert (p.degree(),q.degree())==degs
        assert p.gcd(q).degree()==0
        print(f"F6 right-null, orientation {which}: singular and regular gcds 1")

if __name__=="__main__":
    verify_width_identities()
    verify_F4()
    verify_F6()
