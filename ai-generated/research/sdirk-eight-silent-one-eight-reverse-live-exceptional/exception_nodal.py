"""Five/six-peg homogeneous Bezout projection at a finite exceptional front."""
from exception_base import *
from itertools import combinations, permutations
from time import perf_counter

def prod(vv,K):
    z=[K(1)]
    for a0 in vv:z=mul(z,a0)
    return z

def scale(u,a):
    return [sc(v,a) for v in u]

def pdet(rows,K):
    n=len(rows);z=[]
    for q0 in permutations(range(n)):
        S=prod([rows[i][q0[i]] for i in range(n)],K)
        sign=(-1)**sum(q0[i]>q0[j] for i in range(n) for j in range(i+1,n))
        z=add(z,sc(S,sign))
    return z

def outer_nodal(pegs,K):
    e=[[K(1)]]
    for c in pegs:
        z=[[] for _ in range(len(e)+1)]
        for i,v in enumerate(e):
            z[i+1]=add(z[i+1],v)
            z[i]=add(z[i],sc(mul(v,c),-1))
        e=z
    return e

def W(p,K):
    return [sum_poly([sc(p[j],K(1)/(j-i)) for j in range(i+1,len(p))]) for i in range(len(p)-1)]

def coeff(p,q,i):
    return sum_poly([mul(a,q[i-j]) for j,a in enumerate(p) if 0<=i-j<len(q)])

def ordinary_cols(H,pegs,K):
    D=outer_nodal(pegs,K)
    r=8-len(pegs);assert r in (2,3)
    V=W(H,K)
    E=[]
    for j in range(r+1):
        F=[[]]*j+D;U=W(F,K)
        E.append([add(coeff(H,U,k),sc(coeff(F,V,k),-1)) for k in (1,2,3,4)])
    return E

def ordinary_gates(cols,K):
    d=len(cols)
    return [pdet([[cols[j][i] for j in range(d)] for i in J],K) for J in combinations(range(4),d)]

def projected(K,g,A,B,m,ha,hb,s,hp,H0,H1,rear,slot):
    x=1-g
    A,B=g*A,g*B;S=g*s
    z=[]
    if slot in (2,3,4):z=[{2:A,3:B,4:S}[slot]]
    F0,F1=map(lambda H:gap(K,g,x,rear,H),(H0,H1))
    u=[K(0),K(1)];k=[K(1),K(2),K(-1)]
    c=[x,-g]
    d=[x-2*g,g] if rear else [x,-2*g]
    pegs=[[A],[B],[S],[x],c]+([] if rear is None else [d])
    if slot in (2,3,4):pegs.pop(slot-2)
    n=len(pegs);assert n in (5,6)
    l=max(len(H0),len(H1));H0=H0+[K(0)]*(l-len(H0));H1=H1+[K(0)]*(l-len(H1))
    H=[add(sc(F1,a),sc(F0,-b)) for a,b in zip(H0,H1)]
    cols=ordinary_cols(H,pegs,K)
    N=ordinary_gates(cols,K);aft=list(map(len,N))
    if z:
        # The known silent clock is also the actual affine root.
        G=add(sc(subst_ex(H,c,K),x-z[0]),sc(mul(mul(k,add(c,sc(z,-1))),subst_ex(H,[x],K)),-1))
        G,err=qr(G,u);assert not err
        N.append(G)
    return F0,F1,N,pegs,aft

def subst_ex(H,a,K):
    return sum_poly([mul(v,prod([a]*j,K)) for j,v in enumerate(H)])
