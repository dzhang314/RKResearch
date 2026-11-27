"""Deterministically reconstruct the factorial-only 13/14-stage DIRK tableaux.

The recorded tap solutions are untrusted and verified by every actual
cut equation. No Smith installation is needed to rebuild or audit.
"""
from fractions import Fraction as Q
from functools import reduce
import operator,json
from pathlib import Path
from argparse import ArgumentParser
H=[0,1,-14,56,-84,42]

def mul(V,W):
    out=[0]*(len(V)+len(W)-1)
    for i,a in enumerate(V):
        for j,b in enumerate(W):
            out[i+j]+=a*b
    return out
def product(seq):
    return reduce(operator.mul,seq,1)
def hull(nodes):
    return reduce(mul,([-v,1] for v in nodes),[1])
def scale(f,a):
    return [a*v for v in f]
def val(f,v):
    return reduce(lambda hi,lo:v*hi+lo,reversed(f),0)
def integ(f,v):
    z=0
    for i,a in enumerate(f,1):
        z+=a*v**i/i
    return z
def interp(nodes):
    return [scale(hull([v for j,v in enumerate(nodes) if j!=i]),
                  1/product(u-v for j,v in enumerate(nodes) if j!=i))
             for i,u in enumerate(nodes)]
def quad(nodes,v):
    return [integ(f,v) for f in interp(nodes)]
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def matrix_vec(M,v):return [dot(r,v) for r in M]
def solve(M,b, one):
    # All casts stay in the chosen ring. Divisions apply only to a nonzero pivot.
    n=len(b); assert len(M)==n and all(len(r)==n for r in M)
    T=[list(r)+[z] for r,z in zip(M,b)]
    for j in range(n):
        i=next((i for i in range(j,n) if T[i][j]),None)
        if i is None: raise ValueError("singular solve")
        T[i],T[j]=T[j],T[i]; t=one/T[j][j]
        T[j]=[z*t for z in T[j]]
        for i in range(n):
            if i!=j and T[i][j]:
                k=T[i][j];T[i]=[a-k*c for a,c in zip(T[i],T[j])]
    return [r[-1] for r in T]
def add(a,b):return [u+v for u,v in zip(a,b)]
def diff(a,b):return [u-v for u,v in zip(a,b)]

def strip(v):
    v=abs(v)
    if not v:return 0
    for p in (2,3,5,7):
        while v%p==0: v//=p
    return v

def paid(v):return strip(Q(v).denominator)==1

def unit(v):v=Q(v);return strip(v.numerator)==strip(v.denominator)==1

grid=[Q(j,6) for j in range(-3,7)]
weights=dict(zip(grid,quad(grid,Q(1))))
assert all(paid(w) for w in weights.values())
assert all(sum(w*x**k for x,w in weights.items())==Q(1,k+1) for k in range(10))
proper=[x for x in grid if x not in (0,1)]
co=[1/(x*product(x-z for z in proper if z!=x)) for x in proper]
cofactor=dict(zip(proper,co))

def reverse13(x,k,answer):
    n=len(x); assert n==9
    y=[1-t for t in x]; w=[weights[t] for t in x]
    assert x[0]==1 and all(unit(m) for m in w[:3])
    U2=w[1]*y[1]**3/6
    U=[Q(0)]+[cofactor[z]*U2/cofactor[x[1]] * (1+k*(z-x[1])) for z in x[1:]]
    assert all(paid(u) for u in U)
    assert all(sum(ui*xi**j for ui,xi in zip(U,x))==0 for j in range(1,7))
    wy=[[v*t**j for v,t in zip(w,y)] for j in range(5)]
    K=[[Q(0)]*n for _ in range(n)]
    K[1][1]=y[1]/2; K[1][0]=w[1]*y[1]/(2*w[0])
    V0=[row[:3] for row in wy[:3]]
    inv=[solve(V0,[int(i==j) for j in range(3)],Q(1)) for i in range(3)]
    actinv=lambda Z:[sum(v[j]*z for v,z in zip(inv,Z)) for j in range(3)]
    for i in range(2,n):
        K[i][:3]=actinv([wy[1][i],wy[2][i]/2,wy[3][i]/3+U[i]])
    nulls=[]
    for j in range(3,n-3):
        v=actinv([-row[j] for row in wy[:3]])+[Q(0)]*(n-3)
        v[j]=Q(1)
        nulls.append(v)
    assert all(paid(z) for row in K+nulls for z in row)
    assert [matrix_vec(K,wy[j]) for j in range(3)]==[
      wy[1],scale(wy[2],Q(1,2)), add(scale(wy[3],Q(1,3)),U)]
    u,q,r=x[-1],x[-2],x[-3]
    F=hull([Q(0),u,q,r])
    E=[[val(f,z) for z in x] for f in (F,[0]+F,H)]
    h0=diff(matrix_vec(K,wy[3]),scale(wy[4],Q(1,4)))
    k0=matrix_vec(K,U)
    rhs=[-dot(f,h) for h in (h0,k0) for f in E]
    taps=[(i,j) for i in range(3,n) for j in range(3,min(i+1,n-3))]
    T=[[f[i]*dot(nulls[j-3],probe) for i,j in taps] for probe in (wy[3],U) for f in E]
    assert len(answer)==len(taps) and matrix_vec(T,answer)==rhs
    assert all(paid(c) for c in answer)
    for (i,j),c in zip(taps,answer):
        K[i]=add(K[i],scale(nulls[j-3],c))
    assert all(paid(z) for row in K for z in row)
    assert [matrix_vec(K,wy[j]) for j in range(3)]==[
      wy[1],scale(wy[2],Q(1,2)), add(scale(wy[3],Q(1,3)),U)]
    assert all(dot(f,h)==0 for h in (diff(matrix_vec(K,wy[3]),scale(wy[4],Q(1,4))),matrix_vec(K,U)) for f in E)
    eta=[val(H,z) for z in x]
    eta[0]-=integ(H,Q(1))/w[0]
    assert all(paid(z) for z in eta)
    W=[list(w)]
    for n in range(5):
        assert all(dot(eta,V)==0 for V in W)
        W=[z for v in W for z in (matrix_vec(K,v),[yi*vi for yi,vi in zip(y,v)])]
    return K,w,U,eta

def assemble13(x,u,p,K,w,eta):
    r,q,v=x[-3],x[-2],x[-1]
    assert u==v
    c=[Q(0),u/4,u/2,u,p,q,r];z=len(c)
    G=[[Q(0)]*z for _ in range(z)]
    for i,idx in [(1,[0,1]),(2,[0,1,2]),(3,[0,2,3]),(4,[0,2,3,4])]:
        for j,wj in zip(idx,quad([c[j] for j in idx],c[i])):
            G[i][j]=wj
    Pi=[[]]*z
    idx=[0,3,4,5,6]
    for j,P in zip(idx,interp([c[i] for i in idx])):
        Pi[j]=P
    sig=scale(diff(G[3],[integ(f,u) for f in Pi]),1/val(H,u))
    assert all(paid(t) for t in sig)
    for i,xi in [(5,q),(6,r)]:
        G[i]=add([integ(f,xi) for f in Pi],scale(sig,val(H,xi)))
    assert G[5][6]==0
    h=len(x);T=[[K[h-1-j][h-1-i] for j in range(h)] for i in range(h)]
    A=[row+[Q(0)]*h for row in G]
    xf=x[::-1]
    for i,xi in enumerate(xf):
        row=[integ(f,xi)-sum(t*val(f,xj) for t,xj in zip(T[i],xf)) for f in Pi]
        A.append(add(row,scale(sig,eta[h-1-i]))+T[i])
    B=[weights[Q(0)]]+[Q(0)]*6+w[::-1]
    records=((3,7),(5,8),(6,9))
    assert all(A[orig]==A[new] for orig,new in records)
    keep=[i for i in range(16) if i not in (7,8,9)]
    for orig,new in records:
        for row in A: row[orig]+=row[new]
        B[orig]+=B[new]
    assert all(not A[i][j] for k,i in enumerate(keep) for j in keep[k+1:])
    return ([[A[i][j] for j in keep[:k+1]] for k,i in enumerate(keep)],
          [B[i] for i in keep],c+xf[3:])


def reverse14(x,k,answer):
    n=len(x); assert n==9
    y=[1-t for t in x]; w=[weights[t] for t in x]
    assert x[0]==1 and all(unit(m) for m in w[:3])
    U2=w[1]*y[1]**3/6
    U=[Q(0)]+[cofactor[z]*U2/cofactor[x[1]] * (1+k*(z-x[1])) for z in x[1:]]
    assert all(paid(u) for u in U)
    assert all(sum(ui*xi**j for ui,xi in zip(U,x))==0 for j in range(1,7))
    wy=[[v*t**j for v,t in zip(w,y)] for j in range(5)]
    K=[[Q(0)]*n for _ in range(n)]
    K[1][1]=y[1]/2; K[1][0]=w[1]*y[1]/(2*w[0])
    V0=[row[:3] for row in wy[:3]]
    inv=[solve(V0,[int(i==j) for j in range(3)],Q(1)) for i in range(3)]
    actinv=lambda Z:[sum(v[j]*z for v,z in zip(inv,Z)) for j in range(3)]
    for i in range(2,n):
        K[i][:3]=actinv([wy[1][i],wy[2][i]/2,wy[3][i]/3+U[i]])
    nulls=[]
    for j in range(3,n-2):
        v=actinv([-row[j] for row in wy[:3]])+[Q(0)]*(n-3)
        v[j]=Q(1)
        nulls.append(v)
    assert all(paid(z) for row in K+nulls for z in row)
    assert [matrix_vec(K,wy[j]) for j in range(3)]==[
      wy[1],scale(wy[2],Q(1,2)), add(scale(wy[3],Q(1,3)),U)]
    q,r=x[-1],x[-2]
    F=hull([Q(0),q,r])
    E=[[z**j*val(F,z) for z in x] for j in range(3)]
    h0=diff(matrix_vec(K,wy[3]),scale(wy[4],Q(1,4)))
    k0=matrix_vec(K,U)
    rhs=[-dot(f,h) for h in (h0,k0) for f in E]
    taps=[(i,j) for i in range(3,n-2) for j in range(3,i+1)]
    T=[[f[i]*dot(nulls[j-3],probe) for i,j in taps] for probe in (wy[3],U) for f in E]
    assert len(answer)==len(taps) and matrix_vec(T,answer)==rhs
    assert all(paid(c) for c in answer)
    for (i,j),c in zip(taps,answer):
        K[i]=add(K[i],scale(nulls[j-3],c))
    assert all(paid(z) for row in K for z in row)
    assert [matrix_vec(K,wy[j]) for j in range(3)]==[
      wy[1],scale(wy[2],Q(1,2)), add(scale(wy[3],Q(1,3)),U)]
    assert all(dot(f,h)==0 for h in (diff(matrix_vec(K,wy[3]),scale(wy[4],Q(1,4))),matrix_vec(K,U)) for f in E)
    return K,w,U

def assemble14(x,u,p,K,w):
    r,q=x[-2],x[-1]
    c=[Q(0),u/4,u/2,u,p,q,r];z=len(c)
    G=[[Q(0)]*z for _ in range(z)]
    for i,idx in [(1,[0,1]),(2,[0,1,2]),(3,[0,2,3]),(4,[0,2,3,4]),(5,[0,3,4,5]),(6,[0,3,4,5,6])]:
        for j,wj in zip(idx,quad([c[j] for j in idx],c[i])):
            G[i][j]=wj
    Pi=[[]]*z
    idx=[0,3,4,5,6]
    for j,P in zip(idx,interp([c[i] for i in idx])):
        Pi[j]=P
    h=len(x);T=[[K[h-1-j][h-1-i] for j in range(h)] for i in range(h)]
    A=[row+[Q(0)]*h for row in G]
    xf=x[::-1]
    for i,xi in enumerate(xf):
        row=[integ(f,xi)-sum(t*val(f,xj) for t,xj in zip(T[i],xf)) for f in Pi]
        A.append(row+T[i])
    B=[weights[Q(0)]]+[Q(0)]*6+w[::-1]
    assert A[5]==A[7] and A[6]==A[8]  # two actual, complete ties
    keep=[i for i in range(16) if i not in (7,8)]
    for orig,new in ((5,7),(6,8)):
        for row in A: row[orig]+=row[new]
        B[orig]+=B[new]
    assert all(not A[i][j] for k,i in enumerate(keep) for j in keep[k+1:])
    return ([[A[i][j] for j in keep[:k+1]] for k,i in enumerate(keep)],
          [B[i] for i in keep],c+xf[2:])

def emit(width):
    inputs=json.loads(Path(__file__).with_name("paid-taps.json").read_text())
    d=inputs[str(width)]
    x=list(map(Q,d["reverse"]));u,p,k=map(Q,(d["u"],d["p"],d["k"]))
    params=list(map(Q,d["top_taps"]))
    if width==13:
        K,w,U,eta=reverse13(x,k,params)
        A,b,c=assemble13(x,u,p,K,w,eta)
    else:
        K,w,U=reverse14(x,k,params)
        A,b,c=assemble14(x,u,p,K,w)
    assert [sum(row) for row in A]==c and len(A)==width
    e=dot(b,[z**10 for z in c])-Q(1,11)
    assert e==Q(179,3079296)
    return dict(schema="rational-lower-triangular-runge-kutta-tableau-v1",stages=width,order=10,
       A=[[str(v) for v in row]for row in A],b=list(map(str,b)),c=list(map(str,c)),eleventh_bush_defect=str(e))

if __name__=="__main__":
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("width",type=int,choices=[13,14])
    cli.add_argument("--emit",type=Path,required=True)
    a=cli.parse_args()
    a.emit.write_text(json.dumps(emit(a.width),indent=2)+"\n")
    print("paid top equations and all literal row merges for",a.width)
