from eight_arithmetic_polys import *
from extra_active import exact_uc
from quadratic_poly import E as EE

zz,oo=EE(0),EE(1)
def eu(P0):
    return EE(P0.a,P0.b)

def ea(P0):
    A=exact_uc(P0)
    return [EE(P([v.a[0] for v in [eu(w.v) for w in R]]),
               P([v.b[0] for v in [eu(w.v) for w in R]])) for R in A]

def fastgcd(a,b):
    if not a or not b:return a.gcd(b)
    if min(a.degree(),b.degree())==0:return oo
    if not a.b and not b.b:
        return EE(a.a.gcd(b.a))
    # A degree-preserving split with gcd one certifies the exact coprimality.
    for p,t in ((1097,345),(1103,161),(1129,203),(1151,24)):
        K=Bfield(nmod_poly([0,1],p),p,t)
        try:c,d=K.cast(a),K.cast(b)
        except ValueError:continue
        if c.degree()==a.degree() and d.degree()==b.degree() and c.gcd(d).degree()==0:
            return oo
    return a.gcd(b)

def ediv(a,b):
    if b==oo:return a
    ba,bb=b.a,b.b
    d=ba*ba-bb*bb/2
    q,ra=divmod(a.a*ba-a.b*bb/2,d);assert not ra
    z,rb=divmod(a.b*ba-a.a*bb,d);assert not rb
    return EE(q,z)

def stripE(A,guards):
    for q in guards:
        k=0
        while q.degree()>0:
            if A.degree()>=q.degree():
                try:
                    X=ediv(A,q)
                except AssertionError:
                    pass
                else:
                    A=X;k+=q.degree()
                    continue
            h=fastgcd(A,q)
            if h.degree()==0:break
            A=ediv(A,h);k+=h.degree()
        if k:print('exact removed',q.degree(),k,flush=True)
    return A.monic()

def eres(F,G,stats=False):
    n,d=len(F)-1,len(G)-1
    if n<0 or d<0:return zz
    P0=[]
    for i in range(d):
        P0.append([zz]*i+F+[zz]*(d-1-i))
    for i in range(n):
        P0.append([zz]*i+G+[zz]*(n-1-i))
    assert P0
    m=n+d;sign=1;q=oo
    for j in range(m-1):
        row=next((k for k in range(j,m) if P0[k][j]),None)
        if row is None:return zz
        if row!=j:P0[j],P0[row]=P0[row],P0[j];sign=-sign
        p=P0[j][j]
        for i in range(j+1,m):
            for k in range(j+1,m):
                s=p*P0[i][k]-P0[i][j]*P0[j][k]
                P0[i][k]=ediv(s,q)
            P0[i][j]=zz
        q=p
        if stats:print('bareiss pivot',j,q.degree(),flush=True)
    return sign*P0[-1][-1]

@lru_cache(None)
def projections(front):
    s=perf_counter()
    F,M,Y,E5,guards,geom,info=acdata(front)
    ff,mm=ea(F),ea(M)
    print('exact resultant with Bareiss',front,flush=True)
    R=eres(ff,mm)
    assert R
    assert R.degree()==600
    print('exact arithmetic degree',front,R.degree(),'seconds',perf_counter()-s,flush=True)
    cg=[ea(can(q))[0] for q in guards if not q.degrees()[1]]
    aa,bb,q,bq,pp,Lx,Lc,Ld=info
    # front Gauss values should already appear in guards, and compare all possible.
    S=stripE(R,cg)
    if not S.b:S=ediv(S,fastgcd(S,S.der())).monic()
    print('exact square-free guarded',front,S.degree(),flush=True)
    k=1+2*u-u*u
    Qx,Qc=[can(g*q+bq*v) for v in pp[-3:-1]]
    Kd=ea(can(2*Lc*Qx-k*Lx*Qc))
    D=eres(Kd,ea(Ld))
    assert D
    bad=stripE(D,cg)
    print('arithmetic exact separated Gauss eighth factor',front,bad.degree(),flush=True)
    good=stripE(S,[bad])
    assert (good.degree(),bad.degree())==(249,36)
    print('arithmetic noTailGauss regular vs contact',front,good.degree(),bad.degree(),flush=True)
    return good,bad,(ff,mm,Y,E5,guards,geom,info)
