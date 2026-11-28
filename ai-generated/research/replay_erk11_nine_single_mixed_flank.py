"""Exact finite-place replay for the switched-third-plateau q9 chart."""
import flint
O8=(353,-6592,47432,-180576,407346,-564984,474432,-221760,44352)
T0=[1,-32,216,-480,330]
U0=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],
    [216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],
    [330,-9240,55440,-110880,69300]]

def interp(F,xx,yy):
    X=F.gen(); P=F.zero()
    for j,xxj in enumerate(xx):
        w=F.one()
        for k,xxk in enumerate(xx):
            if j!=k:
                w*= (X-xxk)/(xxj-xxk)
        P+=yy[j]*w
    return P

def invrem(F,a,f):
    # Extended Euclidean inverse, used only after checking unit.
    old,r=f,a%f
    oldu,u=F.zero(),F.one()
    while r:
        q,n=divmod(old,r)
        old,r=r,n
        oldu,u=u,oldu-q*u
    assert old.degree()==0
    return (oldu/old[0])%f

def replay():
    p,deg=19,32
    C=flint.fmpz_mod_poly_ctx(p)
    of=C(list(O8))
    assert of.degree()==8 and of.is_irreducible()
    K=flint.fq_default_ctx(p,deg,'i',fq_type='FQ_NMOD')
    F=flint.fq_default_poly_ctx(K); X=F.gen(); Z=X
    # O8 irreducible over F_19: all eight roots are Frobenius conjugate.
    af=F(list(O8)); ar=af.roots()
    assert len(ar)==8 and all(e==1 for _,e in ar)
    a=ar[0][0]
    assert af(a)==0
    d=2*a-1; b=1-d; h=a/2
    assert all(t!=0 for t in (a,b,a-d,d,a-1,d-1))
    R4=F([1,-14,56,-84,42]); R5=F([-1,20,-120,300,-330,132])
    assert R4(a)!=0 and R5(a)!=0
    R=R5(a)*R4-R4(a)*R5
    assert R.degree()==5
    td=(X-a)*(X-d)
    assert not R%td and R.gcd(R.derivative()).degree()==0
    K0=R//td
    assert K0.degree()==3 and K0(h)!=0
    beta=a*a/(8*K0(h)); Q=beta*K0
    L=X*X*(a-X)/a; Rright=(1-X)**2*(X-d)/b
    Cleft=(Q-L)//(X-h)
    assert not (Q-L)%(X-h) and Cleft.degree()==2
    Cleft=Cleft/Cleft[2]
    assert Cleft.gcd(Cleft.derivative()).degree()==0
    w=X*(1-X)
    M_R=F([sum(R[i]/((i-j+1)*(i-j+2)) for i in range(j+1,6)) for j in range(5)])
    assert M_R(a)!=0 and M_R(d)!=0
    ellA=M_R(a)/(R.derivative()(a)*w(a));ellD=M_R(d)/(R.derivative()(d)*w(d))
    integ=lambda H:sum(H[j]/(j+1) for j in range(H.degree()+1))
    V=X*X*(X-a)**2; W=(1-X)**2*(X-d)**2
    PA=F([K.zero()]+[V[j]/(j+1) for j in range(5)])
    QB0=F([K.zero()]+[W[j]/(j+1) for j in range(5)])
    QB=QB0(K.one())-QB0
    H=integ(PA*W);J=integ(PA*QB)
    C1=integ(X*PA*W);C2=integ(X*V*QB)
    I0,I1,I2=(integ(X**j*V*W) for j in range(3))
    A0=H*H-J*I0;B0=J*I1-H*C1;C0=J*I1-H*C2;D0=C1*C2-J*I2
    assert J!=0 and A0*D0-B0*C0!=0
    UU=F([F(row)(b) for row in U0])(a);TV=F(T0)
    uroots=Cleft.roots()
    assert len(uroots)==2 and all(m==1 for _,m in uroots)
    checked=0
    for ui,(u,_) in enumerate(uroots):
        assert all(t!=0 for t in (u,u-a,u-d,u-h))
        l0=(a-d)*(a-u); l1=-d*u
        AL=l0+TV(a)*l1; BL=TV(b)*l0+UU*l1
        assert AL!=BL
        v0=(BL-AL*d*d)/(AL-BL);v1=(AL*d-BL)/(AL-BL)
        M=v0+v1*Z
        def rem(S):
            return S[0]-S[2]*M-S[3]*Z*M, S[1]+S[2]*Z+S[3]*(Z*Z-M)
        r0,r1=rem(Rright);q0,q1=rem(Q)
        Zgate=r0*q1-r1*q0
        # The exact virtual {1,d} pair is disallowed by the active-label census.
        ghost=1+d
        assert Zgate.degree()==2 and M(ghost)==d and Zgate(ghost)==0
        live=Zgate//(X-ghost)
        assert live.degree()==1 and live(ghost)!=0
        ZZ=-live[0]/live[1]
        AR=X*X-ZZ*X+M(ZZ); check=(X-h)*(X-u)*AR
        assert q1(ZZ)!=0 and r1(ZZ)!=0
        kap=r1(ZZ)/q1(ZZ)
        HG=(check*M_R)%K0
        assert HG.gcd(K0).degree()==0
        LL=(-w*invrem(F,HG,K0))%K0
        monK=K0/K0[3]
        AP=-a*a/2; AE=Rright(a)/kap
        DP=-b*b/(2*kap);DE=L(d)
        AP_,AE_,DP_,DE_=Q(a)-AP,Q(a)-AE,Q(d)-DP,Q(d)-DE
        assert all(t!=0 for t in (AP,DP,AE,DE,AE-AP,DE-DP,AP_,AE_,DP_,DE_))
        VL=V+a*(X-a)*Q; VR=W-b*(X-d)*kap*Q
        MM=lambda zz:monK+zz*LL
        # For each omitted root y, pair gate = B(x,z) B(z,x).
        def normv(zz):
            m=MM(zz); s=-m[2]-X; tt=m[1]-X*s
            v=A0*tt+D0
            pp=v*v+(B0+C0)*v*s+B0*C0*s*s+(B0-C0)**2*tt
            # Norm of the pair gate = determinant of multiplication.
            pp0=pp%m; pp1=(X*pp0)%m;pp2=(X*pp1)%m
            return sum((pp0[j]*(pp1[(j+1)%3]*pp2[(j+2)%3]-pp2[(j+1)%3]*pp1[(j+2)%3]) for j in range(3)))
        ng=interp(F,[K(i) for i in range(5)],[normv(K(i)) for i in range(5)])
        assert all(ng(K(i))==normv(K(i)) for i in range(5,8))
        assert ng.degree()==4 and ng[0]!=0
        nr=ng.roots()
        assert len(nr)==4 and all(e==1 for _,e in nr)
        for lam,_ in nr:
            assert lam!=0 and ng(lam)==0
            m=MM(lam); kk=beta*lam
            wt=A0*X+C0;vv=B0*X+D0
            TB=(-vv)**3+m[2]*(-vv)**2*wt+m[1]*(-vv)*wt*wt+m[0]*wt**3
            ff=m.gcd(TB)
            assert ff.degree()==1
            x=-ff[0]/ff[1]
            assert wt(x)!=0
            z=-vv(x)/wt(x); y=-m[2]-x-z
            assert m(x)==m(y)==m(z)==0
            assert A0*x*z+B0*x+C0*z+D0==0
            D=td*check*m
            gs=(D.derivative()(x),D.derivative()(y),D.derivative()(z), Q(x),Q(y),Q(z),
                VR(y),VR(z),VL(x),VL(y),x-y,y-z,x-z,
                x-a,y-a,z-a,x-d,y-d,z-d)
            assert all(g!=0 for g in gs)
            bx,by,bz=[kk/(D.derivative()(t)*Q(t)) for t in [x,y,z]]
            px=K.zero(); rz=K.zero()
            py=(C1-z*H)/((y-z)*by*VR(y))
            pz=(C1-y*H)/((z-y)*bz*VR(z))
            rx=(C2-y*H)/((x-y)*bx*VL(x))
            ry=(C2-x*H)/((y-x)*by*VL(y))
            Ua=1/Q(a)+ellA*AP*AE/(kk*(AP_*AE_))*D.derivative()(a)
            Ud=1/Q(d)+ellD*DP*DE/(kk*(DP_*DE_))*D.derivative()(d)
            pa=PA(a)*(AE-AP)/AP*(AE*Ua-1)
            rd=QB(d)*(DE-DP)/DP*(DE*Ud-1)
            idx=[a,d,x,y,z]
            ps=[(pa-PA(a))/AE,-PA(d)/DE,
                 (px-PA(x))/Q(x),(py-PA(y))/Q(y),(pz-PA(z))/Q(z)]
            rs=[-QB(a)/AE,(rd-QB(d))/DE,
                 (rx-QB(x))/Q(x),(ry-QB(y))/Q(y),(rz-QB(z))/Q(z)]
            bws=[1/prod(s-t for t in idx if t!=s) for s in idx]
            Uj=[sum(bw*t**j*r for bw,t,r in zip(bws,idx,rs)) for j in range(2)]
            Vj=[sum(bw*t**j*q for bw,t,q in zip(bws,idx,ps)) for j in range(2)]
            assert Uj[0]*Vj[1]-Uj[1]*Vj[0]!=0
            checked+=1
        print('left fiber',ui+1,'right degree 1, outer norm degree 4, four live incompatible read tuples',flush=True)
    assert checked==8
    print('All eight residue fibers excluded (and their Frobenius conjugates).',flush=True)

def prod(xs):
    y=1
    for x in xs:y*=x
    return y

if __name__=='__main__':
    replay()
