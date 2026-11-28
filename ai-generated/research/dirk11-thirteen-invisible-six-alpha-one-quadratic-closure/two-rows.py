"""Fixed quadratic carrier in the adjugate old fit. All coefficients ascend."""
# Input ring env: P/P0 and their primitives, two matched old interpolation
# fits el,to and M,W0, old profile z=zp/zq, and the true V.  No forward
# chronology outside the known alpha=1 beta>=1 enters these rows.
L0,L1=prim(P0)[1:],prim([zero,*P0])[1:]
def exact_monic_div(f,m):
    x=list(f)
    n=len(m)-1
    assert m[-1]==1
    q=[zero]*(len(x)-n)
    for i in range(len(x)-1,n-1,-1):
        q[i-n]=c=x[i]
        for j in range(n):x[i-n+j]-=c*m[j]
    assert all(g==0 for g in x[:n])
    return q
def diff_a(f,g):
    return pplus(f,pscale(g,-one))
Q0=fit(L1)
dv4=exact_monic_div(diff_a(mul(L0,M),mul(W0,J4p)),R3)
dv5=exact_monic_div(diff_a(mul(L1,M),mul(Q0,J4p)),R3)
UV=ev(M,V); jv=ev(J4p,V); hv=V*jv; CV=ev(dv4,V)
pv=ev(P,V); ip=ev(IP,V)
A=(zp-V*zq)*((ev(el,V)*hv-ip*UV)*UV+CV*(pv*UV-den*hv))-zq*(ev(I2P,V)*UV-ev(to,V)*hv)*UV
def five():
    """Bona fide degree-five weighted moment at the first middle ghost."""
    mulZ=lambda f:mul([-zp,zq],f)
    CQ=ev(P0,V)*UV
    K=(zq*V-zp)*(den*hv-pv*UV)
    Lm=pplus(pscale(pplus(mulZ(el),pscale(to,-zq)),CQ),pscale(W0,K))
    assert len(Lm)==4 and Lm[3]==0
    xd=zq*Lm[2];xp=-zq*Lm[1]-zp*Lm[2]
    def he(f,x,d,cap):
        assert len(f)<=cap+1
        return sum(f[i]*x**i*d**(cap-i) for i in range(len(f)))
    def dd(f):
        f=list(f)+[zero]*(4-len(f))
        return [zq*zq*f[1]+zq*zp*f[2]+zp*zp*f[3],
                zq*zq*f[2]+zq*zp*f[3],zq*zq*f[3]]
    B5=pplus(pscale(pplus(Q0,pscale(W0,-V)),jv),pscale(R3,ev(dv5,V)-V*CV))
    Mz=he(M,zp,zq,3)
    Q5=pplus(pscale(B5,Mz),pscale(M,-he(B5,zp,zq,3)))
    assert he(Q5,zp,zq,3)==0
    return he(dd(Q5),xp,xd,2)
