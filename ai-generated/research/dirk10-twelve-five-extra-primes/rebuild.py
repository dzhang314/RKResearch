"""Standard-library deterministic regeneration of the five-extra-prime DIRK12."""
from fractions import Fraction as Q
from functools import reduce
from math import lcm
from pathlib import Path
from argparse import ArgumentParser
import operator,json
ALLOWED={2,3,5,7,47,83,97,199,647}
H=[0,1,-14,56,-84,42]
TAPS=['-1/4', '1215/64', '17/192', '81/32', '-1/48', '-173/192', '0', '-725/96', '29/192']
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
    for p in sorted(ALLOWED):
        while v%p==0: v//=p
    return v

def paid(v):return strip(Q(v).denominator)==1

def unit(v):v=Q(v);return strip(v.numerator)==strip(v.denominator)==1

def reverse(x,answer):
    n=len(x); assert n==8
    y=[1-t for t in x]; w=[weights[t] for t in x]
    assert x[0]==1 and all(unit(m) for m in w[:3])
    U2=w[1]*y[1]**3/6
    U=[Q(0)]+[cofactor[z]*U2/cofactor[x[1]] for z in x[1:]]
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

def opening(u,p,q,r):
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
    for i,xi in [(5,q),(6,r)]:
        G[i]=add([integ(f,xi) for f in Pi],scale(sig,val(H,xi)))
    assert G[5][6]==0
    return G,c,Pi,sig

def assemble(x,u,p,K,w,eta):
    r,q,v=x[-3],x[-2],x[-1]
    assert u==v
    G,c,Pi,sig=opening(u,p,q,r)
    h=len(x);T=[[K[h-1-j][h-1-i] for j in range(h)] for i in range(h)]
    A=[row+[Q(0)]*h for row in G]
    xf=x[::-1]
    for i,xi in enumerate(xf):
        row=[integ(f,xi)-sum(t*val(f,xj) for t,xj in zip(T[i],xf)) for f in Pi]
        A.append(add(row,scale(sig,eta[h-1-i]))+T[i])
    B=[weights[Q(0)]]+[Q(0)]*6+w[::-1]
    records=((3,7),(5,8),(6,9))
    assert all(A[orig]==A[new] for orig,new in records)
    keep=[i for i in range(15) if i not in (7,8,9)]
    for orig,new in records:
        for row in A: row[orig]+=row[new]
        B[orig]+=B[new]
    assert all(not A[i][j] for k,i in enumerate(keep) for j in keep[k+1:])
    return ([[A[i][j] for j in keep[:k+1]] for k,i in enumerate(keep)],
          [B[i] for i in keep],c+xf[3:])

X=list(map(Q,"1 7/10 3/10 3/2 5/6 1/6 -1/2 1/2".split()))
weights=dict(zip([Q(0)]+X,quad([Q(0)]+X,Q(1))))
cofactor={z:1/(z*product(z-v for v in X[1:] if v!=z)) for z in X[1:]}

def denominator(A,b):
    return lcm(*(z.denominator for row in A for z in row), *(z.denominator for z in b))

def tableau():
    K,w,U,eta=reverse(X,list(map(Q,TAPS)))
    A,b,c=assemble(X,Q(1,2),Q(112,423),K,w,eta)
    assert list(map(sum,A))==c and len(c)==12
    assert denominator(A,b)==14762353142762908220160000000
    e=dot(b,[x**10 for x in c])-Q(1,11)
    assert e == Q(-1207,57024000)
    return dict(schema="rational-lower-triangular-runge-kutta-tableau-v1",stages=12,order=10,
       A=[[str(v)for v in row]for row in A],b=list(map(str,b)),c=list(map(str,c)),eleventh_bush_defect=str(e))

if __name__=="__main__":
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--emit",type=Path,required=True)
    a=cli.parse_args()
    a.emit.write_text(json.dumps(tableau(),indent=2)+"\n")
    print("9 paid top taps, 31 actual reflected words, and three padded row equalities verified")
