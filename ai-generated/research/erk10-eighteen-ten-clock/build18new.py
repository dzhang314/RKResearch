#!/usr/bin/env python3
from scalar import *
from replay_rooted import audit,trees,size,tf
from argparse import ArgumentParser
from pathlib import Path
import json
from hashlib import sha256

def prefix(pth):
    src=pth.read_bytes()
    assert sha256(src).hexdigest()=="49e854cdda01628174223f46ba8bc9da03e1b8706b774380f7a4db9820a4f370"
    data=json.loads(src)
    A,Pi=([[F(t)for t in row]for row in data[k]]for k in ("A","Pi"))
    @lru_cache(None)
    def phi(t):
        V=[act(c) for c in t]
        return tuple(prod(v[i]for v in V)for i in range(9))
    @lru_cache(None)
    def act(t):return tuple(dot(row,phi(t))for row in A)
    D=hull((F(0),F(1),F(1,2)))
    R=D+[F(0)]*3;S=mul(D,[F(0),-F(1),F(1)])
    for n in range(1,9):
        for t in trees(n-1):
            rho=[-dot(row,phi(t))for row in Pi]+[F(0)]*(8-len(Pi))
            rho[n-1]+=F(n,tf(t))
            assert rho[0]==0
            if n<=5:assert not any(rho)
            if n in (6,7):assert not sum(rho)
            if n==6:
                a=rho[5]
                b=rho[3]-a*S[3]
                assert rho==[b*x+a*y for x,y in zip(R,S)]+[F(0)]*2
    return A,Pi

def raw():
    xs=tuple(F(j,6)for j in range(-3,7))
    w0=tuple(j0(lagrange(xs,i))for i in range(10))
    W=dict(zip(xs,w0))
    assert W[F(1)]==F(7,150)
    assert all(sum(x**d*a for x,a in W.items())==F(1,d+1)for d in range(10))
    c=tuple(map(F,('1','-1/2','-1/3','-1/6','1/3','1/2','5/6','1/6','2/3')))
    y=[1-x for x in c];w=[W[x]for x in c]
    co={x:1/(x*prod(x-z for z in c[1:] if x!=z))for x in c[1:]}
    scale=-W[c[1]]*y[1]**2/2/co[c[1]]
    u=[F(0),*[scale*co[x]for x in c[1:]]]
    v=[F(0),*[z/t for z,t in zip(u[1:],y[1:])]]
    yu=[z*t for z,t in zip(u,y)]
    assert all(dot(u,[a**d for a in c])==0 for d in range(1,8))
    moments=[[q*z**d for q,z in zip(w,y)]for d in range(5)]
    R=[*moments[:3],u,moments[3],yu,v]
    L=[[F(0)]*9 for _ in range(9)]
    for i in range(1,4):
        j=min(i,2)
        L[i][:j]=solve([rr[:j]for rr in R[:j]],
            [moments[1][i],moments[2][i]/2+u[i]][:j])
    S=list(zip(u,yu,v))
    M=S[1:4]
    pg=solve(M,[dot(L[i],moments[2])-moments[3][i]/3 for i in range(1,4)])
    ph=solve(M,[dot(L[i],u)for i in range(1,4)])
    G=[dot(pg,row)for row in S];H=[dot(ph,row)for row in S]
    print('compressed G,H',pg,ph)
    D4=det([r[:4]for r in R[:4]]);D7=det([r[:7]for r in R])
    assert unit(D4) and unit(D7)
    tests0=[a*(a-1)*(a-F(1,2))for a in c]
    tests1=[v0*a*(a-1)for v0,a in zip(tests0,c)]
    T=[tests0,tests1]
    D2=det([r[7:]for r in T]);assert unit(D2)
    print('paid determinants',det(M),D4,D7,D2)
    k=[F(0)]*9;ell=[F(0)]*9;jot=[F(0)]*9
    for i in range(9):
        required=[moments[1][i],moments[2][i]/2+u[i],moments[3][i]/3+G[i],H[i]]
        if 4<=i<7:L[i][:4]=solve([r[:4]for r in R[:4]],required)
        if i<7:
            k[i]=dot(L[i],moments[3])-moments[4][i]/4
            ell[i]=dot(L[i],yu);jot[i]=dot(L[i],v)
        if i>=7:
            if i==7:
                for q in (k,ell,jot):
                    q[7:]=solve([r[7:]for r in T],[-dot(r[:7],q[:7])for r in T])
                    assert all(dot(q,r)==0 for r in T)
            required +=[moments[4][i]/4+k[i],ell[i],jot[i]]
            L[i][:7]=solve([r[:7]for r in R],required)
        assert [dot(L[i],r)for r in R[:len(required)]]==required
        assert all(paid(z)for z in L[i]) and not any(L[i][i:])
    return c,w,W[F(0)],L,u,v,(k,ell,jot)

def build(A0,Pi,c,w,w0,K):
    N=9;high=c[::-1]
    B=[[K[N-1-j][N-1-i]if i>j else F(0)for j in range(N)]for i in range(N)]
    K0=[]
    for i,x in enumerate(high):
        pr=[x**(j+1)/(j+1)-dot(B[i],[a**j for a in high])for j in range(5)]
        K0.append([dot(pr,[Pi[k][j]for k in range(5)])for j in range(9)])
    A=[row+[F(0)]*(18-len(row))for row in A0]+[a+b for a,b in zip(K0,B)]
    b=[w0]+[F(0)]*8+w[::-1]
    assert len(A)==len(b)==18 and len({tuple(r)for r in A})==18
    assert all(not any(r[i:])for i,r in enumerate(A))
    assert all(paid(q)for q in (*b,*(z for r in A for z in r)))
    return A,b

def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument('--prefix',type=Path,default=Path(__file__).with_name('seed6-prefix.json'))
    p.add_argument('--emit',type=Path)
    args=p.parse_args()
    A0,P=prefix(args.prefix)
    c,w,w0,L,u,v,res=raw()
    A,b=build(A0,P,c,w,w0,L)
    D,defs=audit(A,b)
    out={'A':[list(map(str,r[:i]))for i,r in enumerate(A)],'b':list(map(str,b)),
         'D':str(D),'defects':[[t,str(g)]for t,g in defs],
         'reverse_clocks':list(map(str,c)), 'reverse_w':list(map(str,w)),
         'reverse_U':list(map(str,u)), 'reverse_Z':list(map(str,v)),
         'reverse_K':[list(map(str,r[:i]))for i,r in enumerate(L)],
         'reverse_terms':[list(map(str,q))for q in res]}
    if args.emit:args.emit.write_text(json.dumps(out,indent=2)+"\n")
if __name__=='__main__':main()
