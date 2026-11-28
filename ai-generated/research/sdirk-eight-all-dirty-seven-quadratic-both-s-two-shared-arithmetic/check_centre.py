"""Both-S two-shared A/A, third D at center. Exact trace + literal row-four gates."""
from sympy import QQ
from sympy.polys.fields import field
from sympy.polys.rings import ring
F,u=field('u',QQ)
B,x=ring('X',F.to_domain())
W,w=ring('w',F.to_domain())
def check():
    h=3*u/2;d=u/2;m=h+1
    D=-2+u+4*u*u-u**3;k=1+2*u-u*u
    N=(1+4*u-4*u*u)*D+4*u*u*(3*u-2)
    f1=k/2;f2=N/(2*D)
    L=x*x-B(6*m*m/7)*x+B(3*m**4/35)
    l0=L[(0,)];ld=L.evaluate(x,d*d);lh=L.evaluate(x,h*h)
    slope=(d*d-3*m*m/5)/ld
    eta=1/slope+6*m*m/7-d*d
    scale=1/(2*(h*h-eta))
    R=B(scale)*(x-B(eta))
    bb=-ld/(f1*f2)
    ah=2*lh-bb/2;ad=-bb*(f1+f2)
    A=B(ah)+B((ad-ah)/(d*d-h*h))*(x-B(h*h))
    J=(L-R*(A+B(bb)*R)).exquo(x-B(h*h))
    assert J.degree()==1
    sigma=-J[(0,)]/J[(1,)]
    gs=[u,m,u-2,D,k,N,3*u-2,f1-f2,ld,slope,h*h-eta,J[(1,)],
        sigma,sigma-h*h,sigma-d*d,R.evaluate(x,sigma)]
    assert all(gs)
    # Paid b/g sum by the quotient modulo L4^2. Squared variable captures
    # the odd remainder w*T(w^2) without a field or root-splitting assumption.
    V=-(B(slope))*x*(x-B(d*d))*(x-B(eta))
    mod=L*L
    n1,_,g1=R.gcdex(mod)
    print('R inverse',flush=True)
    n2,_,g2=V.gcdex(mod)
    print('Q0 odd inverse',flush=True)
    assert g1==B.one and g2==B.one
    T=((L*n1+A)*n2)%mod
    barg=4*m**6/175*T.get((3,),F.zero)
    suminv=4+2/R.evaluate(x,sigma)+A[(0,)]/l0+2*ad/ld
    trace=2*suminv-2*m*barg
    assert (trace.numer.degree(),trace.denom.degree())==(12,11)
    print('trace degrees',trace.numer.degree(),trace.denom.degree(),flush=True)
    # Actual first three original residuals at normalized clocks 1,1+u,1+2u.
    alpha=(3*u-2)/D
    a1=1-alpha*u
    c=alpha-F.one/2
    a=F.one/2-a1+c;b=a1-2*c
    z=w+W(1+h)
    T2=W(a)+W(b)*z+W(c)*z*z
    JT=W(a)*z+W(b/2)*z*z+W(c/3)*z**3
    LL=1+(z-1)/W(k)
    Del=W(F(4)/3)+W(2*(k+1)/(3*k))*(z-1)
    C4=1-LL+W(b)+W(c)*Del;N4=T2-JT
    Rw=W(scale)*(w*w-W(eta))
    Srow=(C4*Rw-N4)%(w*w-W(sigma))
    S4=Srow.get((0,),F.zero)**2-sigma*Srow.get((1,),F.zero)**2
    C0=C4.get((0,),F.zero);N0=N4.get((0,),F.zero)
    D4=l0*C0*C0-A[(0,)]*N0*C0-bb*N0*N0
    assert (S4.numer.degree(),D4.numer.degree())==(45,23)
    print('fourth equations degrees',S4.numer.degree(),D4.numer.degree(),flush=True)
    def clean(f,guards):
      for g in guards:
        while (z:=f.gcd(g.numer)).degree()>0:f=f.exquo(z)
      return f
    masks=gs+[F(l0),F(3*m*m/35)]
    for f in [trace,S4,D4]:
        Q=clean(f.denom,masks)
        assert Q.degree()==0
    for label,f in [('S',S4),('D',D4)]:
        G=trace.numer.gcd(f.numer)
        assert G.degree()==0
        print('trace vs fourth',label,'raw unit gcd',flush=True)
    return trace,S4,D4,masks
if __name__=='__main__':check()
