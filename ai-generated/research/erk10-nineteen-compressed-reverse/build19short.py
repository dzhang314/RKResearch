#!/usr/bin/env python3
from choose import *
from pathlib import Path
from sys import argv
from math import lcm
import json

def prefix():
    # Existing nine-stage universal ERK7 seed, from erk-seven-factorial/check.py.
    A=[list(map(F,r.split())) for r in (
       '', '1/6', '0 1/3', '1/8 0 3/8', '1/8 0 3/16 -1/16',
       '64 0 474 -88 -448', '151/972 0 13/27 -28/243 -320/1701 -1/6804',
       '23637/168070 0 114/343 -7492/84035 -52576/588245 -93/1176490 -729/84035',
       '1169/900 0 13/5 5204/675 -147136/1575 -13/18900 -2376/25 4802/27')]
    b=list(map(F,'7/40 0 0 328/135 -512/35 -1/7560 -729/40 16807/540 1/8'.split()))
    x=[sum(r)for r in A]
    A.append(b)
    feats=[[F(1)]+[F(0)]*9,[F(0)]*9+[F(1)]]
    feats+=[[u*c**j for u,c in zip(b,x)]+[F(0)]for j in range(3)]
    mats=[[F(0)**i for i in range(5)],[F(1)]*5]
    mats+=[[F(1,i+j+1)for i in range(5)]for j in range(3)]
    D=det(mats);assert unit(D)
    Pi=list(zip(*(solve(mats,r)for r in zip(*feats))))
    assert [sum(Pi[j][k]/(j+1)for j in range(5))for k in range(10)]==feats[2]
    return A,Pi

def construct(c,w,u,A0,Pi):
    y=[1-a for a in c]
    m=[[v*z**j for v,z in zip(w,y)]for j in range(5)]
    s=[u_i*z for u_i,z in zip(u,y)]
    v=[F(0),*w[1:-1],F(0)]
    e=[w[0],*[F(0)]*(len(w)-1)]
    R=[*m[:3],u,m[3],s,e]
    L=[[F(0)]*10 for _ in c]
    for i in range(1,4):
        d=min(i,2)
        L[i][:d]=solve([r[:d]for r in R[:d]],[m[1][i],m[2][i]/2+u[i]][:d])
    M=[[r[i]for r in (u,s,v)]for i in range(1,4)]
    pg=solve(M,[dot(L[i],m[2])-m[3][i]/3 for i in range(1,4)])
    ph=solve(M,[dot(L[i],u)for i in range(1,4)])
    G=[dot(pg,[a,b,c])for a,b,c in zip(u,s,v)]
    H=[dot(ph,[a,b,c])for a,b,c in zip(u,s,v)]
    print('compressed G and H',pg,ph)
    assert all(paid(a)for a in (*pg,*ph))
    gk=[F(0)]*10
    gl=[F(0)]*10
    gr=[F(0)]*10
    for i in range(10):
        T=[m[1][i],m[2][i]/2+u[i],m[3][i]/3+G[i],H[i]]
        if 4<=i<=6:
            L[i][:4]=solve([r[:4]for r in R[:4]],T)
        if i<7:
            gk[i]=dot(L[i],m[3])-m[4][i]/4
            gl[i]=dot(L[i],s)
            gr[i]=dot(L[i],e)
        if i in (7,8):
            if i==7:
                E=list(zip(*map(tests,c)))
                M=[list(r[7:9])for r in E]
                assert unit(det(M))
                for vec in (gk,gl,gr):
                    vec[7:9]=solve(M,[-dot(vec[:7],r[:7])for r in E])
                    assert all(dot(vec,r)==0 for r in E)
            T += [m[4][i]/4+gk[i],gl[i],gr[i]]
            L[i][:7]=solve([r[:7]for r in R],T)
            assert dot(L[i],m[3])-m[4][i]/4==gk[i] and dot(L[i],s)==gl[i] and dot(L[i],e)==gr[i]
        assert [dot(L[i],r)for r in R[:len(T)]]==T, (i,list(map(str,T)))
        assert all(paid(a)for a in L[i]) and not any(L[i][i:])
    assert not any(L[-1]) and not any(a[-1] for a in L)
    assert all(sum(a*(x**(k+1))*(1-x) for x,a in zip(c,u))==0 for k in range(6))
    assert all(sum(a*x**k for a,x in zip(w,c))+(C[0] if k==0 else 0)==F(1,k+1) for k in range(10))
    N=10;high=c[::-1]
    B=[[L[N-1-j][N-1-i]if i>j else F(0)for j in range(N)]for i in range(N)]
    K=[]
    for i,x in enumerate(high):
        vals=[x**(k+1)/(k+1)-dot(B[i],[a**k for a in high])for k in range(5)]
        K.append([dot(vals,[Pi[k][j]for k in range(5)])for j in range(10)])
    assert K[0]==A0[-1]+[F(0)] and not any(B[0]) and not any(B[i][0]for i in range(N))
    A=[row+[F(0)]*(19-len(row)) for row in A0]+[a+b[1:]for a,b in zip(K[1:],B[1:])]
    b=[C[F(0)]]+[F(0)]*8+w[::-1]
    assert len(A)==len(b)==19
    assert all(not any(r[i:])for i,r in enumerate(A))
    assert len(set(tuple(r)for r in A))==19
    assert all(paid(z)for z in (*b,*(x for r in A for x in r)))
    return A,b,L,(gk,gl,gr)

@lru_cache(None)
def trees(n,lo=(0,())):
    if not n:return ((),)
    return tuple((t,)+s for k in range(max(1,lo[0]),n+1)
                 for t in trees(k-1) if (k,t)>=lo for s in trees(n-k,(k,t)))
@lru_cache(None)
def size(t):return 1+sum(size(s)for s in t)
@lru_cache(None)
def tf(t):return size(t)*prod(tf(s)for s in t)

def audit(A,b,verbose=True):
    N=len(A)
    DD=lcm(*(x.denominator for x in (*b,*(x for r in A for x in r))))
    assert unpaid(DD)==1
    A=[tuple(int(x*DD)for x in r[:i])for i,r in enumerate(A)]
    b=tuple(int(x*DD)for x in b)
    @lru_cache(None)
    def phi(t):
        acts=[act(v)for v in t]
        return tuple(prod(q[i]for q in acts)for i in range(N))
    @lru_cache(None)
    def act(t):
        v=phi(t)
        return tuple(sum(x*y for x,y in zip(row,v))for row in A)
    def defect(t):
        return F(tf(t)*sum(x*y for x,y in zip(b,phi(t))),DD**size(t))-1
    for n, M in enumerate((1,1,2,4,9,20,48,115,286,719),1):
        ts=trees(n-1)
        assert len(ts)==M
        bad=[(t,defect(t))for t in ts if defect(t)]
        if verbose:print("conditions",n,M,"bad",len(bad),bad[:1],flush=True)
        assert not bad,(n,bad[:3])
    gaps=[];g=0
    for t in trees(10):
        d=defect(t);G=gcd(g,d.numerator)
        if d and G!=g:
            gaps.append((t,d));g=G
            if unpaid(g)==1:break
    assert unpaid(g)==1
    if verbose:print('common denominator',DD,'next defects',gaps,'gcd',g,flush=True)
    return DD,gaps

def main():
    d,q,*z=next(good())
    early,last,share,split,D,E=z
    print('paid determinants',D,E)
    c,w,u=obs(d,q,early,last,share,split)
    print('reverse clocks',list(map(str,c)));print('split mass and U',q,share,split)
    A0,P=prefix()
    A,b,L,more=construct(c,w,u,A0,P)
    D,defects=audit(A,b)
    data={'A':[list(map(str,r[:i]))for i,r in enumerate(A)],'b':list(map(str,b)),
           'D':str(D),'defects':[[t,str(g)]for t,g in defects],
           'reverse_clocks':list(map(str,c)),'reverse_weights':list(map(str,w)),
           'reverse_U':list(map(str,u)),'reverse_K':[list(map(str,r[:i]))for i,r in enumerate(L)],
           'reverse_terms':list(list(map(str,v))for v in more)}
    if len(argv)>1:Path(argv[1]).write_text(json.dumps(data,indent=2)+"\n")
if __name__=='__main__':main()
