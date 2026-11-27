#!/usr/bin/env python3
from compress import *
from math import lcm
import json
from pathlib import Path
from sys import argv

def prefix(p=F(1,6),q=F(1,2),r=F(5,6),e=F(1,12),f=F(0)):
    s=2*p/3
    x=(F(0),e,s,p,q,r)
    A=[[F(0)]*6 for _ in x]
    A[1][0]=e
    A[2][:2]=[s-s*s/(2*e),s*s/(2*e)]
    A[3][:3]=[p/4,F(0),3*p/4]
    for i,a in ((4,F(0)),(5,f)):
        t=x[i]; m1=t*t/2-a*q;m2=t**3/3-a*q*q
        g=(p*m1-m2)/(s*(p-s));h=(m2-s*m1)/(p*(p-s))
        A[i][:5]=[t-g-h-a,F(0),g,h,a]
    out=(p,q,r)
    Q=[dot(A[i],[a**3 for a in x])-x[i]**4/4 for i in (3,4,5)]
    V=[A[i][2] for i in (3,4,5)]
    ell=[Q[(i+1)%3]*V[(i+2)%3]-Q[(i+2)%3]*V[(i+1)%3]for i in range(3)]
    lam=[dot(ell,[a**k for a in out]) for k in range(1,5)]
    Pi=[[F(0)]*6 for _ in range(4)]
    for i,j in enumerate((0,3,4,5)):
        for k,z in enumerate(lagrange((F(0),p,q,r),i)):Pi[k][j]=z
    assert all(paid(v) for v in [*ell,*lam,*(a for row in A for a in row),*(a for row in Pi for a in row)])
    return A,x,Pi,ell,lam

def raw_core():
    target=tuple(F(z)for z in ('1','3/2','1/3','4/3','5/6','7/6'))
    wg=tuple(F(z)for z in ('19/400','15/56','-9/1400','212/525','-51/700','243/700','-1/840','3/175','-9/2800','1/4200'))
    X=tuple(F(j,6)for j in range(10));W=dict(zip(X,wg))
    assert all(paid(z) for z in W.values())
    assert all(sum(v*x**k for x,v in W.items())==F(1,k+1)for k in range(9))
    S=[x for x in W if x]
    bar={x:1/(x*prod(x-y for y in S if x!=y)) for x in S}
    theta=F(3)
    h=init(*(1-x for x in target[1:4]),theta)
    UI,alf,bet,gam,delt=h
    U=weighted((F(0),*UI[:2]),target[:3],W,bar)
    assert U[target[3]] == W[target[3]]*UI[2]
    assert all(sum(U[x]*x**k for x in S)==0 for k in range(1,7))
    G={x:(alf+bet*(1-x))*U[x] for x in S}
    H={x:(gam+delt*(1-x))*U[x] for x in S}
    d4=det(profile(target[:4],W,U,3))
    d6=det(profile(target,W,U,4)+[[(1-x)*U[x]for x in target]])
    assert unit(d4) and unit(d6)
    return Core(W,target,U,G,H,theta,alf,bet,gam,delt,d4,d6)

def build(C,P, tail_order=(F(1,6),F(1,2),F(2,3))):
    A,old,Pi,ell,lam=P
    assert set(tail_order)==set(C.W)-set(C.X)-{0}
    X=(*C.X,*tail_order); Y=[1-x for x in X]
    W=[C.W[x]for x in X];U=[C.U[x]for x in X]
    G=[C.G[x]for x in X];H=[C.H[x]for x in X]
    baseP=[[w*y**j for w,y in zip(W,Y)] for j in range(4)]
    R=[*baseP[:3],U,baseP[3],[y*u for y,u in zip(Y,U)]]
    B0=[[F(0)]*9 for _ in X]
    source=[[X[i]**k for i in range(9)] for k in range(1,5)]
    M=[row[6:]+[-q] for row,q in zip(source,lam)]
    DP=det(M);assert unit(DP),DP
    k=[F(0)]*9;l=[F(0)]*9
    for i in range(9):
        tgt=[W[i]*Y[i],W[i]*Y[i]**2/2+U[i],W[i]*Y[i]**3/3+G[i],H[i]]
        if i<6:
            j=min(i,4)
            if j:B0[i][:j]=solve([row[:j]for row in R[:j]],tgt[:j])
            k[i]=dot(B0[i],R[4])-W[i]*Y[i]**4/4
            l[i]=dot(B0[i],R[5])
        else:
            if i==6:
                for row in (k,l):
                    vals=solve(M,[-dot(row[:6],s[:6])for s in source])
                    row[6:]=vals[:3]
                    assert [dot(row,s)for s in source]==[vals[3]*v for v in lam]
            tgt += [W[i]*Y[i]**4/4+k[i],l[i]]
            B0[i][:6]=solve([row[:6]for row in R],tgt)
            assert dot(B0[i],R[4])-W[i]*Y[i]**4/4==k[i]
            assert dot(B0[i],R[5])==l[i]
        assert all(paid(z) for z in B0[i]),(i,B0[i])
        assert [dot(B0[i],p)for p in R[:4]]==tgt[:4],(i,B0[i],tgt)
        assert not any(B0[i][i:])
    N=9;high=X[::-1]
    B=[[B0[N-1-j][N-1-i]if i>j else F(0)for j in range(N)]for i in range(N)]
    AA=[r+[F(0)]*N for r in A]
    for i,x in enumerate(high):
        vals=[x**(j+1)/(j+1)-dot(B[i],[a**j for a in high])for j in range(4)]
        cxs=[dot(vals,[Pi[k][j]for k in range(4)])for j in range(6)]
        AA.append(cxs+B[i])
    b=[C.W[F(0)]]+[F(0)]*5+W[::-1]
    assert all(paid(z) for z in (*b,*(v for row in AA for v in row)))
    assert all(not any(r[i:]) for i,r in enumerate(AA))
    assert len({tuple(r)for r in AA})==15
    assert [sum(r)for r in AA]==list(old+high)
    print("unit donor determinants:", C.d4,C.d6,"unit terminal pressure determinant:",DP)
    print("prefix cross product ell:",ell,"coefficient row:",lam)
    print("physical stage clocks:"," ".join(map(str,old+high)))
    return AA,b,B0,k,l

@lru_cache(None)
def trees(n, lo=(0,())):
    if not n:return ((),)
    return tuple((t,)+s for k in range(max(1,lo[0]),n+1)
                 for t in trees(k-1) if (k,t)>=lo for s in trees(n-k,(k,t)))
@lru_cache(None)
def size(t):return 1+sum(size(s)for s in t)
@lru_cache(None)
def tf(t):return size(t)*prod(tf(s)for s in t)
def audit(A,b):
    @lru_cache(None)
    def phi(t):
        acts=[act(u)for u in t]
        return tuple(prod(v[i]for v in acts)for i in range(15))
    @lru_cache(None)
    def act(t):return tuple(dot(row,phi(t))for row in A)
    def defect(t):return tf(t)*dot(b,phi(t))-1
    for n, M in enumerate((1,1,2,4,9,20,48,115,286),1):
        ts=trees(n-1)
        assert len(ts)==M
        bad=[(t,defect(t))for t in ts if defect(t)]
        print("conditions",n,M,"bad",len(bad),bad[:1],flush=True)
        assert not bad
    D=lcm(*(z.denominator for z in (*b,*(a for row in A for a in row))))
    assert unpaid(D)==1
    defects=[];g=0
    for t in trees(9):
        d=defect(t);G=gcd(g,d.numerator)
        if d and G!=g:
            defects.append((t,d));g=G
            if unpaid(g)==1:break
    assert unpaid(g)==1
    print("common denominator",D,"tenth numerator gcd",g)
    print("tenth defects",defects)
    return D,defects

def main():
    C=raw_core();P=prefix()
    A,b,B0,k,l=build(C,P)
    D,defects=audit(A,b)
    ds=lambda row:list(map(str,row))
    data={"A":[ds(r[:i])for i,r in enumerate(A)],"b":ds(b),"coefficient_common_denominator":str(D),
          "exactness":[[t,str(z)]for t,z in defects],"chronology":[str(x)for x in (*C.X,F(1,6),F(1,2),F(2,3))],
          "weighted_reverse":[ds(r[:i])for i,r in enumerate(B0)],"weighted_k":ds(k),"weighted_l":ds(l)}
    if len(argv)>1:Path(argv[1]).write_text(json.dumps(data,indent=2)+"\n")
if __name__=='__main__':
    main()
