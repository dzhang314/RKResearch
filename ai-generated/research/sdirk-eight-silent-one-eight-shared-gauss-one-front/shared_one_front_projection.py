"""Exact characteristic-zero literal projection, one live front, shared Gauss clock."""
from functools import lru_cache
from itertools import product
from flint import fmpq_mpoly_ctx, fmpq_poly as FlP, fmpq as FlQ
from quadratic_poly import E as EE
from seven_k0_anchors import F2,cv,Lco,ends,h4,pol,ExField,gcdp,divp,mon,guarded,subst,det,ev,add,sc,mul,qr,nodal
from unequal_finite import sum_poly,power,deriv
from both_front_silent8 import context

CX=fmpq_mpoly_ctx.get(['y','s','g','r','t'])
y,s,g,r,t=CX.gens()
Z=CX.constant(0);O=CX.constant(1)
LM=list(map(FlQ,Lco))
Lg=LM[-1]
GAUSS_R=sum(c*r**i/Lg for i,c in enumerate(LM))
TT=t*t-FlQ(1,2)
MM=EE(FlP([c/Lg for c in LM]))
F=ExField(MM)
r0=F(EE(FlP([0,1])))

def can(V):
    if isinstance(V,(int,FlQ)):
        return CX.constant(V)
    V=divmod(V,TT)[1]
    return divmod(V,GAUSS_R)[1]

def exdiv(f,d):
    a,b=divmod(f,d)
    return can(a),can(b)

def expr(U):
    U=F2(U).v
    return U.a[0]+U.b[0]*t

def term(vals,at):
    return sum(expr(u)*at**j for j,u in enumerate(vals))

def co(P,iv):
    C={}
    for I,h in P.to_dict().items():
        k=I[iv];J=list(I);J[iv]=0
        C.setdefault(k,{})[tuple(J)]=h
    return [CX.from_dict(C.get(i,{})) for i in range(max(C,default=-1)+1)]

def plug(P,iv,U):
    return can(sum(A*U**i for i,A in enumerate(co(P,iv))))

def gco(Poly):
    V={}
    for (i,j,k,n,l),a in can(Poly).to_dict().items():
        assert i==j==0 and n<=3 and l<=1
        A=V.setdefault(k,[[FlQ(0)]*4,[FlQ(0)]*4])
        A[l][n]+=a
    return [F(EE(FlP(V[k][0]),FlP(V[k][1]))) if k in V else F(0)
            for k in range(max(V,default=-1)+1)]

def U(X):
    return can(sum(c*X**i*r**(j-i-1) for j,c in enumerate(LM) for i in range(j)))

def sh(H,Y):
    return can(sum(a*Y**i*g**(len(co(H,0))-1-i) for i,a in enumerate(co(H,0))))

@lru_cache(None)
def literal(front,slot):
    A,B,m=map(lambda w:cv(F2,w),ends(front,1))
    H_a,H_b=(A-1)/2,(B-1-m)/2
    active,quiet,H=(A,B,H_a) if slot==0 else (B,A,H_b)
    al,bl,af=map(expr,(A,B,active))
    X4=[cv(F2,v) for v in pol(h4(front),lambda z:z)]
    S0,_,S1,QT,QA=context(F2,A,B,m,H_a,H_b,None,X4)
    gQ=U(g*af)
    P=can(expr(H)*U(g*y))
    hs=term(X4,s)
    st0=s-1-2*hs;st1=s*s/2-s-2*hs
    tap_a=(bl*st0-st1)*expr((B-A).inv());tap_b=st0-tap_a
    rowT=can(s**3-s**4/4+2*hs+tap_a*al**3+tap_b*bl**3)
    rowA=can(hs+tap_a*expr(H_a)+tap_b*expr(H_b))
    # The literal h4/Ah gcd involves no Gauss parameter.
    def cfield(poly):
        arr=[]
        for f in co(poly,1):
            pairs={}
            for (i,j,k,n,l),a in f.to_dict().items():
                assert i==j==k==n==0
                pairs[l]=a
            from check_star_family import E as QqE
            arr.append(F2(QqE(FlP([pairs.get(0,0)]),FlP([pairs.get(1,0)]))))
        return arr
    assert len(gcdp(X4,cfield(rowA)))==1
    qt,qa=ev(QT,active),ev(QA,active)
    Xt,rem=exdiv(can(rowT-expr(qt)*hs),s-af);assert not rem
    Xa,rem=exdiv(can(rowA-expr(qa)*hs),s-af);assert not rem
    M0=y-1;M1=y*y/2-y;M2=y**3/3-y*y
    J0=M2-(al+bl)*M1+al*bl*M0
    T0=can(y**3-y**4/4+(al+bl)*M2-al*bl*M1+s*J0)
    A0=can(expr(S0[0])*M0+expr(S0[1])*M1+term(S1,s)*J0)
    j=-F2(4)/3+2*(A+B)-2*A*B
    DT=term([2-F2(4)/3*(A+B)+2*A*B,j],s)
    DA=expr(1-2*S0[0]-2*S0[1])+term(S1,s)*expr(j)
    T1=can(hs*(DT-expr(qt))-Xt*(y-af))
    A1=can(hs*(DA-expr(qa))-Xa*(y-af))
    Et=can(hs*T0*gQ+T1*P); Ea=can(hs*A0*gQ+A1*P)
    Et,rem=exdiv(Et,y-af);assert not rem
    Ea,rem=exdiv(Ea,y-af);assert not rem
    Phi,rem=exdiv(can(hs*gQ-plug(P,0,s)),s-af);assert not rem
    outT,Rt=exdiv(Et,y-s);outA,Ra=exdiv(Ea,y-s)
    assert not can(Rt-plug(T0,0,s)*Phi) and not can(Ra-plug(A0,0,s)*Phi)
    assert (Phi.degrees()[1],outT.degrees()[0],outA.degrees()[0])==(2,2,2)
    # Actual fifth h=0: two literal defects must vanish; no pole value is substituted.
    V=can(A0-expr(S1[1])*T0)
    assert not V.degrees()[1]
    Gh=sh(V,r)
    Th=sh(T0,r)
    assert Gh and Th
    print('shared-one-front literal degrees',front,slot,Phi.degrees(),outT.degrees(),outA.degrees(),flush=True)
    return Phi,outT,outA,Gh,Th,gQ,(A,B,m,H_a,H_b,active,quiet,H,X4,T0,A0,rowT,rowA)

def gstar():
    # Normalize the exact star tail, retaining the true u != 0,1,2 guards.
    u=s;x=1-g
    c=x-g*u;d=x-g*(2-u)
    k=1+2*u-u*u
    N=can((2-u)*U(c)-u*U(d)+k*(2*u-2)*U(x))
    D,rem=exdiv(N,u*(u-1)*(u-2))
    assert not rem and not D.degrees()[1]
    return gco(D)

def geight():
    # Arithmetic Gauss eighth has w8=0, so the exact H k8=-k J
    # identity forces J=0 without dividing H.
    X=1-g-r; D=2*g
    return gco(can(4*X**3-12*X*X*D+3*X*D**2+2*D**3))

@lru_cache(None)
def projection(front,slot):
    Phi,Et,Ea,Gh,Th,gQ,ds=literal(front,slot)
    Gph=gco(co(Phi,1)[-1]); GG=gco(gQ)
    strict=[F(0),F(1)]
    hroot=gco(Gh)
    root5=gco(can(Phi.resultant(Th,1)))
    RR=mon(guarded(gcdp(hroot,root5),[strict,GG]))
    print('fifth Gauss hole immediate gcd',front,slot,len(hroot)-1,len(root5)-1,len(RR)-1,flush=True)
    E0=can(Et.resultant(Ea,0))
    A,B,*_=ds
    for a in (A,B):
        while True:
            V,rr=exdiv(E0,s-expr(a))
            if rr:break
            E0=V
    D=co(E0,1);C=co(Phi,1);cc=[gco(v) for v in C]
    N=len(D)-1
    assert len(C)==3 and N>=1
    # Homogeneous quadratic norm: Z=C2*s, with Z^2+C1 Z+C0 C2=0.
    a,b=Z,Z
    pow0=O
    for j in range(N,-1,-1):
        a,b=can(-b*C[0]*C[2]+D[j]*pow0),can(a-b*C[1])
        pow0=can(pow0*C[2])
    NC=can(a*a-C[1]*a*b+C[0]*C[2]*b*b)
    G=gco(NC)
    # Exact polynomial division, not a numerical inversion at an actual diagonal.
    for j in range(N):
        G,rr=divp(G,cc[2])
        assert not rr
    assert len(G)==73
    print('shared-one-front exact early projections',front,slot,'fifth y/s',E0.degrees(),
          'raw gamma',len(G)-1,'leading Phi s',len(Gph)-1,flush=True)
    G=mon(guarded(G,[strict,GG]))
    assert len(G)==67
    print('shared-one-front diagonal retained',front,slot,len(G)-1,
          'star nonhole gcd',len(gcdp(G,gstar()))-1,'Gauss eighth gcd',len(gcdp(G,geight()))-1,
          'row-four lower gamma',len(gcdp(G,Gph))-1,flush=True)
    return G,RR,E0,Phi,Et,Ea,Gh,Th,gQ,ds
