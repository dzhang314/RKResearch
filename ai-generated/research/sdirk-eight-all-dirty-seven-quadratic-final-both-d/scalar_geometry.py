import sympy as S

def k(u):return 1+2*u-u*u
def D(u):return -2+u+4*u*u-u**3
def N(u):return (1+4*u-4*u*u)*D(u)+4*u*u*(3*u-2)
def exact_trace(K,R,t,P,W,L,Q0,m):
    """Return normalized c/r + T(A2), with repeated-root branch retained."""
    one,zero=K.one,K.zero
    def inv(f,v):
        a,b,g=f.gcdex(v)
        assert g==R.one
        return a%v
    W1=W.get((1,),zero)
    def tw(f):
        r=f%W
        return 2*r.get((0,),zero)-W1*r.get((1,),zero)
    P1,P2=(P.get((i,),zero) for i in (1,2))
    def tp(f):
        r=f%P
        return 3*r.get((0,),zero)-P2*r.get((1,),zero)+(P2*P2-2*P1)*r.get((2,),zero)
    dL=L.diff(t)
    if W.gcd(W.diff(t)).degree()==0:
        uc=-tw(dL*inv(L*W.diff(t),W))
    else:
        h=-W1/2;l=L.evaluate(t,h)
        assert W==(t-h)**2 and l
        uc=(dL.evaluate(t,h)/l)**2-dL.diff(t).evaluate(t,h)/l
    N=(inv(Q0,L**2)*(4*m**6/175))%(L**2)
    wid=lambda f:((f*N)%(L**2)).get((7,),zero)
    ce=2*uc-2*m*wid(L*inv(W,L**2))
    Li,Lp=inv(L,W),inv(L,P)
    return ce, lambda f: 2*(tw(f*Li)+tp(f*Lp))-2*m*wid(f)
