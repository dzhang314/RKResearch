"""Exact exceptional front projection for the reverse nine-site L3/L4/L5 family."""
from flint import fmpq_mpoly_ctx, fmpq_poly, fmpq
from seven_k0_anchors import ends,h4,pol,F2,cv,gcdp,E

Q=fmpq_mpoly_ctx.get(['s','g','t'])
s,g,t=Q.gens()
tt=t*t-fmpq(1,2)
L3=(-1,12,-30,20)
L4=(1,-20,90,-140,70)
L5=(-1,30,-210,560,-630,252)

def can(X):return divmod(X,tt)[1] if hasattr(X,"to_dict") else Q.constant(X)
def cx(X):
    y=F2(X).v
    return y.a[0]+t*y.b[0]
def lp(v,a):return can(sum(c*a**j for j,c in enumerate(v)))
def erem(x,d):
    y,z=divmod(x,d)
    assert not can(z)
    return can(y)

def ext(P):
    cf={}
    for (si,gi,ti),v in P.to_dict().items():
        assert si==0 and ti<=1
        cf[(gi,ti)]=v
    n=max((k[0] for k in cf),default=-1)
    return [F2(E(fmpq_poly([cf.get((i,0),0)]),fmpq_poly([cf.get((i,1),0)]))) for i in range(n+1)]

def remove(X,guard):
    C=Q.from_dict({k:v*(-1)**k[-1] for k,v in guard.to_dict().items()})
    N=can(guard*C)
    counter=0
    while True:
        H,R=divmod(can(X*C),N)
        if R:return X,counter
        X=can(H);counter+=1

def front_projection(front):
    A,B,m=map(lambda q:cv(F2,q),ends(front,1))
    ha,hb=(A-1)/2,(B-1-m)/2
    assert A and B and ha and hb and A!=B
    A,B,ha,hb=map(cx,(A,B,ha,hb))
    H4=can(sum(cx(cv(F2,w))*s**j for j,w in enumerate(pol(h4(front),lambda x:x))))
    LA,LB,LS=map(lambda y:lp(L4,g*y),(A,B,s))
    GA,GB,GS=map(lambda y:lp(L3,g*y),(A,B,s))
    assert len(gcdp(ext(LA),ext(LB)))==1
    U=can((B-A)*LA*LB)
    p0=can(LS*(ha*LB*(B-s)+hb*LA*(s-A)))
    p1=can(U*GS-LS*(GA*LB*(B-s)+GB*LA*(s-A)))
    P=can(U*H4-p0)
    geom=can((s-A)*(s-B))
    P,V=erem(P,geom),erem(p1,geom)
    J=can(P.resultant(V,0))
    assert J
    degrees=J.degrees()
    counts=[]
    for gd in (g,LA,LB):
        J,k=remove(J,gd)
        counts.append(k)
    assert J and (P.degrees()[0],V.degrees()[0],degrees[1],J.degrees()[1])==(3,3,57,21)
    assert counts==[12,3,3]
    print('generic plus exceptional constant nine-site front',front,
          's/g',P.degrees(),V.degrees(),'projected',degrees,J.degrees(),
          'only exact gamma/EarlyGauss factors',counts,flush=True)
    return P,V,J
