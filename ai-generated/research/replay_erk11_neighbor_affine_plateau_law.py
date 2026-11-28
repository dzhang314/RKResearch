#!/usr/bin/env python3
"""Small exact witness for the affine plateau law (python-flint 0.9.0)."""
from flint import fmpz_mod_poly_ctx as ctx

def witness():
    # Exact shapes already checked from original actual width fits in the
    # independent K-live finite-width replay at (prime,a,b)=(17,7,7).
    C=ctx(17)
    X=C.gen();Y=1-X
    c=lambda u:C([u])[0]
    a,b,d,s,z,u,v,J=map(c,[7,7,11,12,15,11,5,5])
    P=C([5,9]);Q=C([11,16,13,6,10])
    BL=C([11,6,1,1]);BR=C([4,13,2,1])
    Ds=-BL*BR(Y)*(X-s)*(X-z)
    Om=X*(X-1)*(X-a)*(X-d)
    R=Om*Q
    M=C([sum((R[i]/(i-j) for i in range(j+1,R.degree()+1)),c(0)) for j in range(R.degree())])
    hull,rem=divmod(Ds,X-s)
    assert rem.is_zero() and Ds.derivative()(s)==0
    rho=J/(u*v)
    mA=Ds*M-rho*Q(s)*hull
    mB=P*P*X*(X-1)
    SA,r=divmod(mA,Q);SB,ss=divmod(mB,Q)
    assert [list(map(int,w.coeffs())) for w in [r,ss]]==[[3,2,11,7],[1,12,15,8]]
    assert (r+14*ss).is_zero()

    def hom(H,n):
        return sum((H[i]*(-P[0])**i*P[1]**(n-i) for i in range(n+1)),c(0))
    D,L=hom(Ds,8),-hom(Q,4)**2
    assert (D,L)==(14,13)
    coeff1=(-a*a/2,-4*Q(1-b/2)/P(1-b/2))
    for x,f,expect in zip([a,d],coeff1,[(0,0,0,0,1,0,2),(15,4,3,2,5,2,11)]):
        p,q=P(x),Q(x)
        g=(x-s)*M(x)-rho*Q(s)
        uu=f*(D*q*(q-f*p)+L*Ds(x))*g
        vv=-L*(x-s)*x*(x-1)*p*(q-f*p)
        assert (uu,vv,uu*ss[0]-vv*r[0],g,f,p,q)==expect
    # Check exact stage-sample arithmetic here with no direct 1/Ds'(s).
    e=1-b/2
    a_mass=(SA(a)+14*SB(a))/(Om.derivative()(a)*Ds(a))
    d_mass=(SA(d)+14*SB(d))/(Om.derivative()(d)*Ds(d))
    assert (a_mass,d_mass)==(0,10)
    xis=-P[0]/P[1]
    tau,rem=divmod(Q*Q+L*Ds/D,P)
    assert rem.is_zero() and Ds(xis)!=0
    for x,y,B,f in [(a,d,a_mass,coeff1[0]),(d,a,d_mass,coeff1[1])]:
        nu,mu,t=[14*g(x)/((x-y)*Ds(x)) for g in [P,Q,tau]]
        assert ((mu-f*nu)**2-(nu-f*B)*(t-f*mu))==13
    print('D_lambda=14,L_lambda=13; right compact coefficients (15,4)')
    print('ghost constant coefficients (3,1); independent right mark 3 modulo 17')
    print("ordinary masses via polynomial quotient (0,10) although Ds'(s)=0 in residue")
if __name__=='__main__':
    witness()
