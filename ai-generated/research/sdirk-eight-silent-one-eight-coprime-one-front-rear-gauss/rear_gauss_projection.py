"""Exact coprime one-front projection when penultimate or eighth is Gauss."""
from coprime_generic_front import *
from time import perf_counter

def norm_s(A,B):
    aa=co(A,1);bb=co(B,1)
    n,m=len(aa)-1,len(bb)-1
    assert n>=1 and m>=1
    c=aa[-1]
    fs=[can(v*c**(n-1-i)) for i,v in enumerate(aa[:-1])]
    def step(v):
        a=v[-1]
        return [can((v[j-1] if j else Z)-a*b) for j,b in enumerate(fs)]
    v=[Z]*n;w=O
    for j in range(m,-1,-1):
        v=step(v)
        v[0]=can(v[0]+w*bb[j])
        w=can(w*c)
    V=[]
    for i in range(n):
        V.append(v)
        v=step(v)
    x=can(det([[V[j][i] for j in range(n)] for i in range(n)]))
    P,C=gco(x),gco(c)
    assert P
    a=C[-1].inv();M=sc(C,a)
    for _ in range((n-1)*m):
        P,R=qr(P,M);assert not R
        P=sc(P,a)
    return P

@lru_cache(None)
def rear_gauss(front,slot,rear,hit):
    assert hit in (8,9)
    Et,Ea,D,q0,q1,Q,ds=setup_front(front,slot)
    q=lambda X:can(g*q0+q1*X)
    A,B,m,ha,hb,a,quiet,H0,H4=ds
    xx=1-g
    if hit==9:
        nu,Den=xx-r,g
        cc=r
        dd=xx-2*g+nu if rear else xx-2*nu
    else:
        nu,Den=(2*g-(xx-r),g) if rear else (xx-r,2*g)
        cc=xx-nu if rear else (xx+r)/2
        dd=r
    kh=can(Den**2+2*nu*Den-nu**2)
    Hh=can(-2*Den**3+nu*Den**2+4*nu**2*Den-nu**3)
    Jh=can(2*Den**3+3*nu*Den**2-12*nu**2*Den+4*nu**3)
    if hit==9:
        if rear:
            T=can(nu*Den**2*L(dd)*q(xx)-kh*(2*nu-2*Den)*L(xx)*q(dd))
        else:
            T=can(Den**2*Hh*L(dd)*q(xx)-kh*Jh*L(xx)*q(dd))
    elif rear:
        T=can((2*Den-nu)*Den**2*L(cc)*q(xx)+kh*(2*nu-2*Den)*L(xx)*q(cc))
    else:
        T=can(2*Den**2*L(cc)*q(xx)-kh*L(xx)*q(cc))
    Gg=[g,xx-r,nu,kh,xx-cc,xx-dd,cc-dd,L(xx),L(dd if hit==9 else cc),L(g*expr(a))]
    for z in T.degrees():
        assert z>=0
    T,tt=strip_known(T,[can(v) for v in Gg]+[s-expr(a)])
    start=perf_counter()
    J0=norm_s(T,D)
    assert len(J0)-1==(120 if rear else 134 if hit==9 else 113)
    print('coprime rear Gauss raw exact projection',front,slot,rear,hit,len(J0)-1,round(perf_counter()-start,2),
          'tail',T.degrees(),'strip tail',tt,flush=True)
    J=mon(guarded(J0,[gco(v) for v in Gg if v]))
    Ds=co(D,1)
    assert len(J)-1==(120 if not rear and hit==9 else 99)
    assert len(gcdp(J,gco(Ds[-1])))==1
    print('coprime rear Gauss retained gamma',front,slot,rear,hit,len(J)-1,
          'literal s leading lower',len(gcdp(J,gco(Ds[-1])))-1,flush=True)
    return J,D,T,Et,Ea,(q0,q1,xx,cc,dd,Q,ds)
