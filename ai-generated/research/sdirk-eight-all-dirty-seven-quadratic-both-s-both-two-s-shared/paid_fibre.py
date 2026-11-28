"""Exact specialization of paid scales, Legendre remainders, and fourth tests."""
from flint import nmod_poly as NP
def sp(F,p,u,keep=1):
    ds=F.degrees()
    a=[0]*(ds[keep]+1)
    k=1-keep
    up=[pow(u,i,p) for i in range(ds[k]+1)]
    for xy,c in F.to_dict().items():a[xy[keep]]+=int(c)*up[xy[k]]
    return NP(a,p)
def finite(ev,mode,u,v):
    p=ev
    inv=lambda x:pow(x%p,-1,p)
    Y=NP([0,1],p)
    C=lambda n:NP([n%p],p)
    front=mode[:1] if mode[0]=='S' else mode[:2]
    rear=mode[len(front):]
    def paid(ph,z):
        kk=lambda x:1+2*x-x*x
        if ph=='S':
            assert z*(z-1)*(z-2)*kk(z)%p
            f=kk(z)*inv(2)%p
            # either genuine star order has the same second-defect factor.
            return (2-z)%p,f,f,kk(z)%p
        a=z if ph=='A2' else z*inv(2)%p
        D=-2+a+4*a*a-a**3
        N=(1+4*a-4*a*a)*D+4*a*a*(3*a-2)
        assert a*(a-2)*(3*a-2)*D*N*kk(a)%p
        E=kk(a)*inv(2)%p;G=N*inv(2*D)%p
        return ((2*z)%p,E,G,kk(a)%p) if ph=='A2' else (a,G,E,kk(a)%p)
    s,fp,fs,kap=paid(front,u)
    x,rp,rt,_=paid(rear,v)
    H=(u+v)%p;t=(H-x)%p
    m=(H+2)*inv(2)%p
    assert m and len({0,H,u,s,t})==5
    y=Y-H*inv(2)
    L3=y**3-3*m*m*inv(5)*y
    L4=y**4-6*m*m*inv(7)*y*y+3*m**4*inv(35)
    x0=int(L4(0));Lp=int(L4(u));L3p=int(L3(u))
    assert Lp
    beta=-Lp*inv(fp*rp)%p
    T0=[-beta*inv(2)%p,2*x0%p]
    TH=[2*x0%p,-beta*inv(2)%p]
    Tp=[-beta*fp%p,-beta*rp%p]
    Ts=[-beta*fs%p,int(L4(s))*inv(fs)%p]
    Tt=[int(L4(t))*inv(rt)%p,-beta*rt%p]
    R0=[inv(2),0]
    RH=[0,inv(2)]
    Rs=[fs,0]
    Rt=[0,rt]
    def gate(y,Z,a,V,P,Q):
        L=lambda y,i:(H-y)*P[i]+y*Q[i]
        return [(a*(a-H)*(H*Z[i]-L(y,i))-y*(y-H)*(H*V[i]-L(a,i)))%p for i in (0,1)]
    lines=[gate(s,Ts,u,Tp,T0,TH),gate(t,Tt,u,Tp,T0,TH),gate(t,Rt,s,Rs,R0,RH)]
    lead=next((i for i,(a,b) in enumerate(lines) if b),None)
    if lead is None:return 'no unit scale'
    lam=-lines[lead][0]*inv(lines[lead][1])%p
    if any((a+lam*b)%p for a,b in lines):return 'lines'
    # Rooted low-degree reads recovered from genuine interpolation nodes.
    def interp(pts):
        P=C(0)
        for a,b in pts:
            T=C(b)
            for c,d in pts:
                if a!=c:T=T*(Y-c)*inv(a-c)
            P+=T
        return P
    R=interp([(0,inv(2)),(s,fs),(H,lam*inv(2)%p)])
    if R.degree()!=2:return 'curvature lost'
    P=(Lp*L3-L3p*L4)%R
    Q=((Y-u)*L4)%R
    det=(int(P[0])*int(Q[1])-int(P[1])*int(Q[0]))%p
    if det:return 'R determinant'
    if not lam:return 'scale lost'
    U,A,B=(L4%R).xgcd(R)
    if U!=C(1) or ((L4%R)*A)%R!=C(1):return 'L4/R inverse lost'
    Ft=L3*A%R
    P,rem=divmod(L3-Ft*L4,R)
    if rem or P.degree()!=3:return 'D cubic lost'
    Z,rem=divmod(P,Y-u)
    if rem or Z.degree()!=2:return 'D quadratic lost'
    T=interp([(0,(T0[0]+lam*T0[1])%p),(H,(TH[0]+lam*TH[1])%p),
              (u,(Tp[0]+lam*Tp[1])%p)])
    A=T*inv(lam);B=beta*inv(lam)%p
    # Actual first-three T2 is the interpolation of the real paid defects, in y.
    T2=interp([(0,inv(2)),(u,fp),(s,fs)])
    X=Y+1
    c0=int(T2[0])-int(T2[1])+int(T2[2]);c1=int(T2[1])-2*int(T2[2]);c2=int(T2[2])
    X2=c0+c1*X+c2*X*X
    J=c0*X+c1*inv(2)*X**2+c2*inv(3)*X**3
    La=1+(X-1)*inv(kap)
    De=4*inv(3)+2*(kap+1)*(X-1)*inv(3*kap)
    C4=1-La+c1+c2*De;N=X2-J
    V=C4*C4*L4-A*N*C4-B*N*N
    if Z.gcd(V).degree()==0:return 'fourth'
    return 'live '+str(Z.gcd(V))
