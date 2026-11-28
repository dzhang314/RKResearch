"""Affine reverse numerator sharing a root, genuine quintic, no ordinary hole."""
from reverse_live_quartic import profile_gamma,gap,literal_fifth,L4
from aq_modular import mon,Bfield,Tower,nmod_poly,Nested
from aq_modular import ev,qr,sc,add,nodal

def model(front,rear,p,t):
    DG,data=profile_gamma(front,L4)
    F=Bfield(nmod_poly([0,1],p),p,t)
    M=nmod_poly([int(F(q).x[0]) for q in DG],p)
    assert M.degree()==4 and M.leading_coefficient()==1
    fac=M.factor()[1]
    M1=nmod_poly([1],p)
    for M0,e in fac:M1*=M0**e
    assert M1==M
    for M0,e in fac:
        K=Bfield(M0,p,t);g=K(nmod_poly([0,1],p));x=1-g
        A,B,m,ha,hb,H4=data
        A,B,m,ha,hb=map(K,(A,B,m,ha,hb));H4=list(map(K,H4))
        Lp=[K(v)*g**j for j,v in enumerate(L4)]
        take=ev(Lp,A).inv()*ha
        LP=sc(Lp,take)
        P4=add(LP,sc(H4,-1))
        S,Err=qr(P4,nodal([A,B]));assert not Err and len(S)==3
        S=mon(S);K0=Tower(S);s=K0.gen();g0=K0(g);x0=K0(x)
        N=gap(K,g,x,rear,L4)
        nd=4 if rear is None else (2 if rear else 5)
        assert len(N)==nd+1
        V=Nested(list(map(K0,mon(N))));u=V.gen()
        cv=lambda k:V(K0(k))
        gamma,X=cv(g),cv(x);s=V(s);A,B,m,ha,hb=map(cv,(A,B,m,ha,hb))
        Lpoly=list(map(cv,LP));h4=ev(Lpoly,s)
        a,b,q=gamma*A,gamma*B,gamma*s
        c=X-gamma*u
        k=1+2*u-u*u
        d=X+gamma*k*(u-2)/2 if rear is None else X-gamma*(2-u if rear else 2*u)
        gstack=(M0.degree(),e,nd)
        yield V,(gamma,X,c,d,u,k,a,b,q),Lpoly,(A,B,s,m,ha,hb,h4),gstack

def fifth(V,LP,data):
    A,B,s,m,ha,hb,h4=data
    raw=literal_fifth(V,A,B,m,ha,hb,s,h4,LP)
    Q,err=qr(raw,nodal([A,B,s]))
    assert not err and len(Q)<=3
    return Q

def literal_positions(front,rear,p,t):
    assert rear is not None
    factors=[]
    for V,dat,LP,fr,dims in model(front,rear,p,t):
        g,x,c,d,u,k,a,b,q=dat
        H=lambda z:ev(list(map(V,L4)),z)
        for z in (a,b,q):
            # Actual silent literal 2, 3, or 4.
            ((x-z)*H(c)-k*(c-z)*H(x)).inv()
        # Actual ordinarily silent stage 5, with its own clock.
        den=(H(c)-k*H(x)).inv()
        Y=(x+g*u*k*H(x)*den)/g
        ev(fifth(V,LP,fr),Y).inv()
        factors.append(dims)
    print('shared quintic no-hole literal silence positions 2–5',front,rear,factors,flush=True)
    return len(factors)
