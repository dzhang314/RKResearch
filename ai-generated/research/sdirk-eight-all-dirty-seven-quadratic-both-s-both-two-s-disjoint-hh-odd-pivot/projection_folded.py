from paid_taps import *
from flint import fmpz_mpoly_ctx
Z0,Z1=CZ.constant(0),CZ.constant(1)
H0,A0,B0=CZ.gens()
CZs=fmpz_mpoly_ctx.get(('H','s','z'),'lex')
Hs,ss,zz=CZs.gens()
def swap(P):
    return CZ.from_dict({(i,k,j):c for (i,j,k),c in P.to_dict().items()})
def shape(P,odd=False):
    assert P
    if odd:
        assert swap(P)==-P
        P,q=divmod(P,A0-B0);assert not q
    assert P==swap(P)
    T=[CZs.constant(2),ss]
    for j in range(max(P.degrees()[1:])-1):T.append(ss*T[-1]-zz*T[-2])
    out=CZs.constant(0)
    for (i,j,k),c in P.to_dict().items():
        if j==k:out+=c*Hs**i*zz**j
        elif j>k:out+=c*Hs**i*zz**k*T[j-k]
    back=CZ.from_dict({ix:int(v) for ix,v in out.to_dict().items()}).compose(H0,A0+B0,A0*B0)
    assert back==P
    return out.primitive()[1]

def build():
    r,masks=frame()
    gam,Y=r
    T=(a-H)*(H-b)/4
    Sig=(a-b)/2
    l3=3*mh*mh/5;l4=6*mh*mh/7;c4=3*mh**4/35
    d0=T*T-Sig*Sig*T+l4*T+c4;d1=Sig*(Sig*Sig-2*T-l4)
    c0=-Sig*T;c1=Sig*Sig-T-l3
    Dax=d0*(d0+Sig*d1)+T*d1*d1
    Aan=c0*(d0+Sig*d1)+T*d1*c1
    Ban=d0*c1-d1*c0
    p=a/2-h;q=h-b/2
    L3c=lambda y:y**3-l3*y
    L4c=lambda y:y**4-l4*y*y+c4
    assert not (Dax-L4c(p)*L4c(q))
    for x in [p,q]:assert not (Dax*L3c(x)-(Aan+Ban*x)*L4c(x))
    m3=-Ban
    m2=-Aan+Sig*m3
    m1=Dax+l4*Ban+Sig*m2-T*m3
    m0=l4*Aan+Sig*m1-T*m2
    assert not (T*m0+c4*Aan)
    assert not (T*m1-Sig*m0+l3*Dax+c4*Ban)
    da,db=D(a/2),D(b/2)
    ja,jb=(N(a/2)-da)/a,(N(b/2)-db)/b
    assert all(x.d.is_constant() for x in (ja,jb))
    n=(a+b-2*H)*da-H*ja*(H-b)
    m=(a+b-2*H)*db-H*jb*(H-a)
    U,V=n*db,m*da
    r2=(ja*db+jb*da+H*ja*jb)/2
    r1=(jb*(H-a)*da-ja*(H-b)*db)/2
    r0=(U+V)/4-h*h*r2
    R=lambda y:r0+r1*y+r2*y*y
    assert not (R(-h)-V/2) and not (R(h)-U/2)
    assert not (R(a-h)-V*N(a/2)/(2*da))
    assert not (R(h-b)-U*N(b/2)/(2*db))
    # True nonzero group; invariance of the set, not each item, is enough.
    nonzero=sum(masks.values(),[])+[ip(x.n) for x in (r2,m3)]
    guards=nonzero+[swap(v) for v in nonzero]
    E0=m0*r2**2-(m2*r2-m3*r1)*r0
    E1=m1*r2**2-m3*r2*r0-(m2*r2-m3*r1)*r1
    E0,E1=ip(E0.n),ip(E1.n)
    assert not (E0% (A0-B0))
    P0=strip(E0/(A0-B0),guards)
    P1=strip(E1,guards)
    Y1=strip(Y+swap(Y),guards)
    Y2=strip((Y-swap(Y))/(A0-B0),guards)
    P=[gam,P0,P1,Y1,Y2]
    print('unfolded',[(x.degrees(),len(x.to_dict())) for x in P],flush=True)
    F=list(map(shape,P))
    print('folded',[(x.degrees(),len(x.to_dict())) for x in F],flush=True)
    return F,P,guards,(Dax,Aan,Ban,m0,m1,m2,m3,U,V,r0,r1,r2)

if __name__=='__main__':
    R,P,G,_=build()
    for i,f in enumerate(R):
        print(i,'factors',[(e.degrees(),k) for e,k in f.factor()[1]],flush=True)
