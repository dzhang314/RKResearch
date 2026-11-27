#!/usr/bin/env python3
"""Exact reductions for the Stepanov 15 -> 14 one-opening-row question."""
from itertools import combinations,product
from math import prod,isqrt
from pathlib import Path
from hashlib import md5
import sys
P=227
def inv(x):return pow(int(x)%P,-1,P)
def dot(x,y):return sum(a*b for a,b in zip(x,y))%P
def vscale(a,v):return [a*x%P for x in v]
def pv(x,r):return sum(y*pow(x,i,P)for i,y in enumerate(r))%P
def rowmul(a,B):return [dot(a,[r[j]for r in B])for j in range(len(B))]
def read(p,x,y,z):
    global P
    P=p
    assert (x*x-3)%p==0 and (y*y-7)%p==0 and (z*z-147-42*y)%p==0
    lines=Path(sys.argv[1]).read_bytes()
    assert md5(lines).hexdigest()=="be9e5e3ba1ff8ed21124ad285d7d2fd5"
    rr=[list(map(int,r.split()))for r in lines.splitlines()]
    assert len(rr)==135
    def decode(u):
        a,b,c,d,e,f,g,h,q=u
        return inv(63*q)*(63*a+63*b*x+63*c*y+63*d*x*y+3*e*z+
                          (-2*f+7*h)*x*z+3*g*y*z+(f-2*h)*x*y*z)%P
    D=list(map(decode,rr)); c,b=D[:15],D[15:30]
    A=[D[30+i*(i-1)//2:30+i*(i+1)//2]+[0]*(15-i)for i in range(15)]
    assert all(sum(r)%P==u for r,u in zip(A,c))
    return c,b,A
def det(M):
    K=[v[:] for v in M]
    d=1
    for j in range(len(K)):
        k=next((k for k in range(j,len(K))if K[k][j]%P),None)
        if k is None:return 0
        if k!=j:
            K[k],K[j]=K[j],K[k]
            d=-d
        a=K[j][j]%P; d=d*a%P
        a=inv(a)
        K[j]=vscale(a,K[j])
        for i in range(j+1,len(K)):
            r=K[i][j]
            K[i]=[(a-r*b)%P for a,b in zip(K[i],K[j])]
    return d%P
def rank(M):
    R=[v[:]for v in M];ii=0;jj=[]
    for k in range(len(R[0])):
        r=next((l for l in range(ii,len(R))if R[l][k]%P),None)
        if r is None:continue
        R[r],R[ii]=R[ii],R[r]
        R[ii]=vscale(inv(R[ii][k]),R[ii])
        ri=R[ii]
        for l in range(len(R)):
            if l==ii:continue
            u=R[l][k]
            R[l]=[(a-b*u)%P for a,b in zip(R[l],ri)]
        ii+=1;jj.append(k)
        if ii==len(R): break
    return ii,R,jj
def t(M):return list(map(list,zip(*M)))
def solve(A,b):
    n=len(A); d,M,p=rank([a+[v]for a,v in zip(A,b)])
    assert d==n and p==list(range(n))
    return [a[-1]for a in M]
def high(B,c,b):
    B=[v[6:]for v in B[6:]];c=c[6:];b=b[6:]
    R=[[z*pow(x,k,P)%P for z,x in zip(b,c)]for k in range(5)]
    Ds=[[(u-z*(1-pow(x,k+1,P))*inv(k+1))%P for u,z,x in zip(rowmul(r,B),b,c)]
        for k,r in enumerate(R)]
    assert not any(Ds[0])
    z=Ds[1]
    zc=[x*y%P for x,y in zip(z,c)]
    zcc=[x*y%P for x,y in zip(zc,c)]
    zcca=rowmul(zcc,B)
    zs=[x*y%P for x,y in zip(zcc,c)]
    assert len(set(c[:-1]))==4 and c[-1]==1
    T=[(0,6),(1,7),(2,3),(4,5)]
    assert all(c[i]==c[j] for i,j in T)
    ratio=[(sum(Ds[4][i]for i in I)%P,sum(zcca[i]for i in I)%P)for I in T]
    u,v=next((u,v)for u,v in ratio if v)
    eta=u*inv(v)%P
    # Recover the gamma coefficients and independently check all full fixed relations.
    for L,Q,k in [(Ds[2],[z,zc],2),(rowmul(z,B),[z,zc],2),
         (Ds[3],[z,zc,zcc],3),(rowmul(zc,B),[z,zc,zcc],3),
         (Ds[4],[z,zc,zcc,zs,zcca],5)]:
        I=next(I for I in combinations(range(9),k)if det([t(Q)[j]for j in I]))
        co=solve([t(Q)[j]for j in I],[L[j]for j in I])
        assert all(dot(cp,co)==p for cp,p in zip(t(Q),L))
        if k==5:assert co[-1]==eta
    H=R[:4]+[z,zc,[(a-eta*w)%P for a,w in zip(R[4],zcc)]]
    return B,c,b,H,eta

def main(p=227,x=177,y=190,z=149):
    c,b,A=read(p,x,y,z)
    B,c,b,R,eta=high(A,c,b)
    print('p, coordinates, eta:',P,x,y,z,eta)
    print('high nodes',c,'weights',b)
    S=[]
    for j in range(8):
        K=[u[j+1:]for u in R]
        r,_,col=rank(K)
        S.append(r)
        print('column',j,'n',len(K[0]),'r',r,'pivots',col)
    if S!=[7,7,6,5,4,3,2,1]:return
    K=[u[2:]for u in R]
    cr=det(K)
    assert cr
    U=solve(K,[-u[1]%P for u in R])
    variation=[0,1,*U]
    print('leading affine-variation matrix determinant',cr,'v',variation)
    def gate(tau):
        return [[(pow(x,k+1,P)*inv(k+1)-sum(B[i][j]*pow(y,k,P)for j,y in enumerate(c))
                  -tau*variation[i]*pow(c[0],k,P))%P for k in range(1,4)]
              for i,x in enumerate(c)]
    M0,M1=gate(0),gate(1)
    states=[]
    for I in combinations(range(9),3):
        f=lambda M:det([M[i]for i in I])
        vals=f(M0),(f(M1)-f(M0))%P
        if any(vals):states.append((I,vals))
    for (I,vals),(J,w)in combinations(states,2):
        obs=det([list(vals),list(w)])
        if obs:
            print('independent affine minors',I,J,vals,w,obs)
            return
    print('no independent pair',states[:7])
if __name__=='__main__':main(*list(map(int,sys.argv[2:])))
