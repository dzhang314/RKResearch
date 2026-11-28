#!/usr/bin/env python3
"""Literal real-algebraic construction rules; no numerical solves."""
from fractions import Fraction as Q
from functools import reduce
from math import comb,prod

def pmul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b):c[i+j]+=u*v
    return c
def hull(xs):return reduce(pmul,([-x,1] for x in xs),[1])
def ev(poly,x):
    n=0
    for c in reversed(poly):n=n*x+c
    return n
def integ(poly,t=1):
    return sum(Q(1,i+1)*v*t**(i+1) for i,v in enumerate(poly))
def der(s,x):return prod(x-z for z in s if z!=x)
def leg(j,x):
    return sum(k*(-1)**(j-k)*comb(j,k)*comb(j+k,k)*x**(k-1) for k in range(1,j+1))
def solve(M,r):
    a=[list(row)+[v] for row,v in zip(M,r)]
    for i in range(len(a)):
        j=next(j for j in range(i,len(a)) if a[j][i])
        a[j],a[i]=a[i],a[j]
        r0=a[i][i];a[i]=[v/r0 for v in a[i]]
        for j in range(len(a)):
            if i!=j:
                r0=a[j][i]
                a[j]=[v-r0*w for v,w in zip(a[j],a[i])]
    return [u[-1] for u in a]

def support(a,x,y,t,f):
    fixed=[0,1]+[1-u for u in [a,a*x,a*y,a*t,f]]
    fixed_poly=hull(fixed)
    n0,n1,n2=[integ([0]*j+fixed_poly) for j in range(3)]
    ab=n0*n2;bb=n1*n1
    g0,g1,g2=9*bb-4*ab,3*bb-ab,3*bb-2*ab
    s=6*n1*n2/g0
    p=3*n1*n1*n2*n2/(g0*g1)
    u=n1*n2/g2
    return fixed,s,p,u

GHOST_P=[Q(1,4),Q(1,3),Q(8,11),Q(1)]
GHOST_ELL=[Q(256,945),Q(81,520),Q(161051,393120),Q(89,1080)]
GHOST_A=[[Q(1,8),0,0,0],[Q(16,27),Q(-5,18),0,0],
         [Q(-128,1331),Q(756,1331),Q(3,22),0],
         [Q(880,623),Q(-27,26),Q(43923,64792),0]]

def ghost_checks():
    p=GHOST_P;w=GHOST_ELL;A=GHOST_A
    assert all(sum(w[i]*p[i]**k for i in range(4))==Q(1,k+1) for k in range(1,6))
    assert all(sum(p[j]*A[i][j] for j in range(4))==p[i]**2/2 for i in range(4))
    h=[sum(p[j]**2*A[i][j] for j in range(4))-p[i]**3/3 for i in range(4)]
    u=[w[i]*h[i]*der(p,p[i]) for i in range(4)]
    assert u[0] and all(v==u[0] for v in u)
    for j in range(4):
        assert sum(w[i]*A[i][j] for i in range(4))==(1-p[j])*w[j]
        assert sum(w[i]*p[i]*A[i][j] for i in range(4))==(1-p[j]**2)*w[j]/2

def ordinary_modes(a,x,y):
    Db=5*x*x-5*x+1;D=2*x*y-x-3*y*y+2*y
    rb=x**3*(15*x**3-49*x*x+55*x-20)/Db
    kb=-30*x**3*(x-1)**3/Db
    ep=-(7*x*x-7*x+2)/1260
    P0=hull([0,1,x,y])
    I0,I1=integ(P0),integ([0]+P0)
    K1=integ([0,0]+P0)-ep
    ry=-10800*(K1*integ(P0,y)-I1*integ([0]+P0,y))/(Db*D)
    rr=solve([[s*leg(j,a*s) for j in [5,6,7]] for s in [1,x,y]],[1,rb,ry])
    nv=kb/(a*x*leg(6,a*x))
    return rr,nv,ep

def construct(a,x,y,t,f,d,cast):
    """Use x,y,t normalized and f physical. Return ordinary 15-row A,b,c."""
    z,o=cast(0),cast(1)
    fixed,s,p,u=support(a,x,y,t,f);v=s-d
    assert d*v==p and d!=v and d*u*v
    labels=fixed+[d,v,u]
    assert all(l!=m for i,l in enumerate(labels) for m in labels[i+1:])
    B=[integ(hull([r for r in labels if r!=s0]))/der(labels,s0) for s0 in labels]
    def bweight(s0):return B[next(i for i,x0 in enumerate(labels) if x0==s0)]
    D=labels[1:]
    r=v/d;tu=u/d;sig=Q(1,6)
    assert (r!=0 and r!=1 and r!=2 and 2*r!=1
            and r*r-4*r+1 and 5*r*r-14*r+5 and r+1)
    assert tu==-r*(r+1)/(r*r-4*r+1)
    lam=3*(r-1)*(r-2);k=(r-Q(1,2))/lam
    p1=r**3/(6*(r-1));pr=r/2-p1/r
    hv=sig*p1;rho=bweight(v)*d**4*der(D,v)*hv
    assert rho and -k*sig*bweight(d)*d**4*der(D,d)==rho
    # All physical clock positions, including the pair and literal terminal.
    X=[o,x,y,t,f/a]
    C=[z]+[a*e for e in GHOST_P]+[a*u0 for u0 in X]+[1-u,1-d,1-v,1-d,o]
    b=[bweight(o)]+[z]*4+[bweight(1-a*u0) for u0 in X]+[
                           bweight(u),bweight(d)/2,bweight(v),bweight(d)/2,bweight(z)]
    assert all(b[j] for j in [0]+list(range(5,15)))
    assert sum(b)==1
    # First-five ordinary live-only block, by positive-degree exact cardinals.
    (alpha,mu,gamma),nu,ep=ordinary_modes(a,x,y)
    assert gamma and nu
    def modes(T):
        R=T*(alpha*leg(5,a*T)+mu*leg(6,a*T)+gamma*leg(7,a*T))
        K=a*nu*T*leg(6,a*T)
        return R,K
    def live(P,s0,R,K):
        return integ(P,s0)-R*integ(P)-K*(integ([0]+P)-(ep*P[5] if len(P)==6 else 0))
    rows=[]
    for i,T0 in enumerate(X):
        R,K=modes(T0)
        row=[]
        for j,s0 in enumerate(X[:i+1]):
            P=hull([0]+[X[k0] for k0 in range(i+1) if k0!=j])
            row.append(a*live(P,T0,R,K)/ev(P,s0))
        rows.append(row)
    # t_i,j = A[j,i]*b[j]/(b[i]*d), normalized reverse and deweighted.
    T={13:{13:o/2},12:{13:p1,12:pr}}
    delta=-2*sig
    a2=Q(1,2)+sig/(r-1)+k
    T[11]={13:Q(1,2)-delta/(r-1)-a2,12:delta/(r*(r-1)),11:a2}
    for i in range(10,4,-1):
        si=(1-C[i])/d; Hi=rho/(b[i]*d**4*der(D,d*si))
        known={j:rows[j-5][i-5]*b[j]/(b[i]*d) for j in range(i,10)}
        unknown=[o,r,tu]
        group=[]
        for z0 in unknown:
            P=hull([0]+[q0 for q0 in unknown if q0!=z0])
            a0=integ(P,si)+lam*Hi
            a0-=sum(c0*ev(P,(1-C[j])/d) for j,c0 in known.items())
            group.append(a0/ev(P,z0))
        Td2=(Hi-sig*group[0])/delta
        T[i]=dict(known)
        T[i].update({13:group[0]-Td2,12:group[1],11:Td2,10:group[2]})
    out=[[z for _ in range(15)] for _ in range(15)]
    for i,row in T.items():
        row[14]=(1-C[i])/d-sum(row.values())
        for j,u0 in row.items():
            assert i<=j
            out[j][i]=d*u0*b[i]/b[j]
    assert all(out[i+5][j+5]==rows[i][j] for i in range(5) for j in range(i+1))
    for i in range(4):
        for j in range(i+1):out[i+1][j+1]=a*GHOST_A[i][j]
    for i in range(5,14):
        ci=C[i]
        for j in range(4):
            out[i][j+1]=ci*GHOST_ELL[j]*((mu+nu*C[j+1])*leg(6,ci)+alpha*leg(5,ci)+gamma*leg(7,ci))
    for j in range(1,5):
        out[14][j]=-sum(b[i]*out[i][j] for i in range(14))/b[14]
    for i in range(15):out[i][0]=C[i]-sum(out[i][1:])
    assert all(not out[i][j] for i in range(15) for j in range(i+1,15))
    assert any(out[i][i] for i in range(15)) and not out[0][0] and not out[14][14]
    return out,b,C
