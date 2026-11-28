#!/usr/bin/env python3
"""Independent denominator-padded fixed-grid resultant replay (standard library)."""
from collections import Counter
from itertools import permutations
import sys

P=1013
D6=(-42,840,-5040,12600,-13860,5544)
ROOTS=(347,468,507,546,667)
LIVE=(*ROOTS,1)

def inv(x):return pow(x%P,-1,P)
def frac(x,y):return x*inv(y)%P

def coeff_add(a,b):return (a+b)%P
def uadd(f,g):
    return [(f[i] if i<len(f) else 0)+(g[i] if i<len(g) else 0) for i in range(max(len(f),len(g)))]

def trim(f):
    g=[i%P for i in f]
    while g and not g[-1]:g.pop()
    return g

def uval(f,x):
    s=0
    for c in reversed(f):s=(x*s+c)%P
    return s

def umul(f,g):
    if not f or not g:return []
    h=[0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g):h[i+j]=(h[i+j]+a*b)%P
    return h

def hull(nodes):
    f=[1]
    for x in nodes:f=umul(f,[-x,1])
    return f

def integ(f,x):
    return uval([0]+[frac(v,i+1) for i,v in enumerate(f)],x)

J=integ
val=uval

def card(nodes,x):
    f=hull(y for y in nodes if y!=x)
    d=inv(uval(f,x))
    return [v*d%P for v in f]

def gcd(f,g):
    f,g=trim(f),trim(g)
    while g:
        i=inv(g[-1])
        while len(f)>=len(g):
            j=len(f)-len(g)
            a=f[-1]*i%P
            for k,v in enumerate(g): f[k+j]=(f[k+j]-a*v)%P
            f=trim(f)
        f,g=g,f
    return [v*inv(f[-1])%P for v in f] if f else []

class Poly(dict):
    # exponent triple (t,z,w), all coefficients modulo P.
    def __init__(self,u=0):
        if isinstance(u,dict):
            super().__init__({e:c%P for e,c in u.items() if c%P})
        else:
            super().__init__({(0,0,0):u%P} if u%P else {})
    def __add__(self,g):
        g=g if isinstance(g,Poly) else Poly(g)
        h=dict(self)
        for e,v in g.items(): h[e]=h.get(e,0)+v
        return Poly(h)
    __radd__=__add__
    def __neg__(self):return Poly({e:-v for e,v in self.items()})
    def __sub__(self,g):
        return self+-g if isinstance(g,Poly) else self+(-g)
    def __rsub__(self,g):return -self+g
    def __mul__(self,g):
        if not isinstance(g,Poly):return Poly({e:v*g for e,v in self.items()})
        h={}
        for (i,j,k),a in self.items():
            for (l,m,n),b in g.items():
                e=(i+l,j+m,k+n)
                h[e]=h.get(e,0)+a*b
        return Poly(h)
    __rmul__=__mul__
    def part(self,axis,degree):
        return Poly({tuple(0 if i==axis else x for i,x in enumerate(e)):v
                     for e,v in self.items() if e[axis]==degree})
    def deg(self,axis):
        return max((e[axis] for e in self),default=-1)
    def total(self):return max((sum(e) for e in self),default=-1)
    def plug_z(self,a,b):
        S=[Poly(1)]
        B=Poly(a)+t*b
        for _ in range(self.deg(1)):S.append(S[-1]*B)
        return sum(Poly({(i,0,k):v})*S[j] for (i,j,k),v in self.items())
    def at_t(self,x,n):
        a=[0]*(n+1)
        for (i,j,k),v in self.items():
            assert k==0 and j<=n
            a[j]=(a[j]+pow(x,i,P)*v)%P
        return a
    def pure_t(self):
        assert self.deg(1)<=0 and self.deg(2)<=0
        return trim([self.get((i,0,0),0) for i in range(1+self.deg(0))])

t=Poly({(1,0,0):1})
z=Poly({(0,1,0):1})
w=Poly({(0,0,1):1})

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def powers(pts,k):return [x**k%P for x in pts]
def row(pts,x,scale,err):
    out=[]
    for j in pts:
        f=card(pts,j)
        out.append(scale*J(f,x)+sum(f[k]*d for k,d in err.items()))
    return out

def interp(pts,values,x):return sum(g*val(card(pts,j),x) for j,g in zip(pts,values))

def stages(nodes):
    x1,x2,x3,x4=nodes
    g1=frac(x1**3,6)
    e1=frac(3*x1,2); r1=frac(x1,2)
    f1=frac(9*x1*x1,5); u1=frac(x1*x1,2)
    P2=(0,x1,x2)
    W2=row(P2,x2,1,{2:t})
    G2=(0,g1,t)
    e2=dot(W2,powers(P2,3))-frac(x2**4,4)
    r2=dot(W2,G2)
    f2=dot(W2,powers(P2,4))-frac(x2**5,5)
    u2=dot(W2,[g*j for g,j in zip(G2,P2)])
    e3=interp((x1,x2),(t*e1,e2),x3)
    r3=interp((x1,x2),(t*r1,r2),x3)
    P3=(*P2,x3)
    W3=row(P3,x3,t,{2:t*z,3:e3*z})
    G3=(*G2,z)
    Q=dot(W3,G3)-r3*z
    f3=dot(W3,powers(P3,4))-t*frac(x3**5,5)
    u3=dot(W3,[g*j for g,j in zip(G3,P3)])
    e4=interp((x1,x2),(t*e1,e2),x4)
    r4=interp((x1,x2),(t*r1,r2),x4)
    f4=interp((x1,x2,x3),(t*z*f1,z*f2,f3),x4)
    u4=interp((x1,x2,x3),(t*z*u1,z*u2,u3),x4)
    P4=(*P3,x4)
    W4=row(P4,x4,t*z,{2:t*z*w,3:z*e4*w,4:f4*w})
    G4=(*G3,w)
    F=dot(W4,G4)-z*r4*w
    L=dot(W4,[(j-x4)*g for j,g in zip(P4,G4)])-(u4-x4*z*r4)*w
    return P4,G4,Q,L,F

def event(pts,G,a,role):
    if role==0:
        allpts=(*pts,a)
        cards=[card(allpts,x) for x in pts]
        A=[J(f,a) for f in cards]
        B=[f[-1] for f in cards]
        Gy=[j*g for j,g in zip(pts,G)]
        return dot(A,G)*dot(B,Gy)-dot(B,G)*dot(A,Gy)
    s=pts[role]
    return dot([J(card(pts,x),s)*(x-s) for x in pts],G)

def det(M):
    M=[row[:] for row in M]
    d=1
    for ix,row in enumerate(M):
        pivot=next((j for j in range(ix,len(M)) if M[j][ix]),None)
        if pivot is None:return 0
        if pivot!=ix:
            M[pivot],M[ix]=M[ix],M[pivot]
            d=-d
        v=M[ix][ix]
        d=d*v%P
        c=inv(v)
        for row in M[ix+1:]:
            a=row[ix]*c%P
            if a:
                for k in range(ix+1,len(M)):
                    row[k]=(row[k]-a*M[ix][k])%P
    return d%P

def interpolate(values):
    # Newton basis at the consecutive residues 0,...,N; N<p.
    p=[0]
    basis=[1]
    row=values[:]
    fact=1
    for i in range(len(values)):
        p=uadd(p,[v*frac(row[0],fact)%P for v in basis])
        row=[(z-y)%P for y,z in zip(row,row[1:])]
        fact=fact*(i+1)%P
        basis=umul(basis,[-i,1])
    return trim(p)

def resultant_z(Q,E,n,cap):
    """Degree-padded Sylvester determinant, evaluated and interpolated in t."""
    assert Q.deg(1)<=2 and E.deg(1)<=n
    v=[]
    for t0 in range(cap+1):
        q=Q.at_t(t0,2); e=E.at_t(t0,n)
        v.append(det([[0]*i+q+[0]*(n-1-i) for i in range(n)]
                    +[[0]*i+e+[0]*(1-i) for i in range(2)]))
    return interpolate(v)

def wquad_against(F,C):
    c0,c1=C.part(2,0),C.part(2,1)
    return F.part(2,0)*c1*c1-F.part(2,1)*c0*c1+F.part(2,2)*c0*c0

def check_one(pts,G,Q,L,F,a,role):
    C=event(pts,G,a,role)
    assert L.deg(2)<=1 and F.deg(2)<=2 and C.deg(2)<=1
    assert Q.total()<=3 and Q.get((0,0,0),0)==0
    if role==4:
        assert C.deg(1)==1 and C.deg(2)<=0 and C.total()<=1
        ls=inv(C.get((0,1,0),0))
        z0=-ls*C.get((0,0,0),0)%P
        z1=-ls*C.get((1,0,0),0)%P
        A=Q.plug_z(z0,z1).pure_t()
        B=wquad_against(F,L).plug_z(z0,z1).pure_t()
        assert len(A)==4 and len(gcd(A,B))==1
        return False
    M=L.part(2,0)*C.part(2,1)-L.part(2,1)*C.part(2,0)
    E=wquad_against(F,C)
    if role==0:
        nz,mtot,ntot,etot,bound,k=3,5,4,6,11,2
    elif role==1:
        nz,mtot,ntot,etot,bound,k=3,4,3,4,10,2
    elif role==2:
        nz,mtot,ntot,etot,bound,k=3,4,3,4,9,1
    else:
        nz,mtot,ntot,etot,bound,k=2,4,2,4,9,1
    assert M.total()<=mtot and E.total()<=etot
    na=2*mtot+nz    # n*3+2*deg_tot(M)-2*n
    nb=2*etot+ntot
    A=resultant_z(Q,M,nz,na)
    B=resultant_z(Q,E,ntot,nb)
    assert len(A)==bound+1
    assert not any(A[:k]) and not any(B[:k])
    Gd=gcd(A[k:],B[k:])
    if len(Gd)==1:return False
    assert role==0  # two singleton residue roles need the mixed determinant.
    Z=resultant_z(Q,M+E,ntot,nb)
    assert not any(Z[:k]) and len(gcd(Gd,Z[k:]))==1
    return True

def main():
    assert all(P%k for k in range(2,32)) and D6[-1]%P
    assert tuple(x for x in range(P) if uval(D6,x)==0)==ROOTS
    ct=Counter()
    for k,lab in enumerate(permutations(LIVE)):
        x1,x2,x3,x4,a,b=lab
        if a==1:continue
        pts,G,Q,L,F=stages((x1,x2,x3,x4))
        for role in range(5):
            if role and pts[role]==1:
                ct["literal_origin_skipped"]+=1
                continue
            mixed=check_one(pts,G,Q,L,F,a,role)
            ct["singleton" if not role else "spent"+str(role)]+=1
            if mixed:ct["mixed"]+=1
    assert ct=={"singleton":600,"spent1":480,"spent2":480,"spent3":480,"spent4":480,
                "literal_origin_skipped":480,"mixed":2},ct
    print("mod 1013: all padded first-event charts excluded after exact boundary factors")
    for k,n in ct.items():print(f"{k}: {n}")

if __name__=="__main__": main()
