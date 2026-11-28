"""Small finite place for the single mixed q9 two-triple branch."""
import flint

O8=(353,-6592,47432,-180576,407346,-564984,474432,-221760,44352)
T0=[1,-32,216,-480,330]
U0=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],
    [216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],
    [330,-9240,55440,-110880,69300]]

def det3(M):
    return (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])
          - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
          + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))

def data(p):
    C=flint.fmpz_mod_poly_ctx(p)
    f=C(list(O8))
    assert f.degree()==8
    factors=f.factor()[1]
    assert len(factors)==1 and factors[0][0].degree()==8 and factors[0][1]==1
    K=flint.fq_default_ctx(modulus=factors[0][0],fq_type='FQ_NMOD')
    F=flint.fq_default_poly_ctx(K);X=F.gen();Z=X
    a=K.gen();d=2*a-1;b=1-d;h=a/2
    assert a!=0 and b!=0 and a!=d
    R4=F([1,-14,56,-84,42])
    R5=F([-1,20,-120,300,-330,132])
    assert R4(a)!=0 and R5(a)!=0
    R=R5(a)*R4-R4(a)*R5
    assert R.degree()==5
    dd=(X-a)*(X-d)
    assert not R%dd and R.gcd(R.derivative()).degree()==0
    Q0=R//dd
    assert Q0.degree()==3 and Q0(h)!=0
    Q=a*a/(8*Q0(h))*Q0
    L=X*X*(a-X)/a
    Cleft=(Q-L)//(X-h)
    assert not (Q-L)%(X-h) and Cleft.degree()==2
    Cleft=Cleft/Cleft[2]
    assert Cleft[0]!=0 and Cleft(a)!=0
    l0=Cleft(a);l1=-Cleft[0]
    t0=F(T0)
    u0=F([F(row)(b) for row in U0])(a)
    AL=l0+t0(a)*l1
    BL=t0(b)*l0+u0*l1
    assert AL!=BL
    v0=(BL-AL*d*d)/(AL-BL)
    v1=(AL*d-BL)/(AL-BL)
    M=v0+v1*Z
    def rem(S):
        return S[0]-S[2]*M-S[3]*Z*M, S[1]+S[2]*Z+S[3]*(Z*Z-M)
    Rright=(1-X)**2*(X-d)/b
    r0,r1=rem(Rright);q0,q1=rem(Q)
    Zgate=r0*q1-r1*q0
    print('Z quadratic degree',Zgate.degree(),'factor degrees',[(r.degree(),m) for r,m in Zgate.factor()[1]],flush=True)
    assert Zgate.degree()==2

    w=X*(1-X)
    # Phi_R(x) here is the scalar moment integral of the divided
    # difference of R, not a derivative-front functional.
    M_R=F([sum(R[i]/((i-j+1)*(i-j+2)) for i in range(j+1,6)) for j in range(5)])
    H=((X-h)*Cleft*M_R)%Q0
    H0=(H*(X*X+v0))%Q0
    H1=(H*(v1-X))%Q0
    Hc=lambda n:[((X**n*H0)%Q0)[i]+Z*((X**n*H1)%Q0)[i] for i in range(3)]
    xh=Hc(1);ph=Hc(0);rhs=Hc(2)
    ww=w%Q0
    A=[[-xh[i],ph[i],F([ww[i]])] for i in range(3)]
    DE=det3(A)
    NS=det3([[-rhs[i],A[i][1],A[i][2]] for i in range(3)])
    NP=det3([[A[i][0],-rhs[i],A[i][2]] for i in range(3)])
    print('ghost pivot gcd',Zgate.gcd(DE).degree(),flush=True)
    assert Zgate.gcd(DE).degree()==0

    integ=lambda H:sum(H[j]/(j+1) for j in range(H.degree()+1))
    V=X*X*(X-a)**2;W=(1-X)**2*(X-d)**2
    PA=F([K.zero()]+[V[j]/(j+1) for j in range(5)])
    QB0=F([K.zero()]+[W[j]/(j+1) for j in range(5)])
    QB=QB0(K.one())-QB0
    H=integ(PA*W);J=integ(PA*QB)
    C1=integ(X*PA*W);C2=integ(X*V*QB)
    I0,I1,I2=(integ(X**j*V*W) for j in range(3))
    A0=H*H-J*I0;B0=J*I1-H*C1;C0=J*I1-H*C2;D0=C1*C2-J*I2
    u8=A0*d+C0;v8=B0*d+D0
    m8=DE*v8*v8+NS*u8*v8+NP*u8*u8
    u9=B0-C0;v9=A0*NP+C0*NS+D0*DE
    m9=v9*v9+u9*NS*v9+u9*u9*NP*DE
    print('d at 8 gcd',Zgate.gcd(m8).degree(),'d at 9 gcd',Zgate.gcd(m9).degree(),flush=True)
    assert Zgate.gcd(m8).degree()==Zgate.gcd(m9).degree()==0

if __name__=='__main__':data(19)
