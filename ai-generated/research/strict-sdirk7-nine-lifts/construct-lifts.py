from functools import cache
from math import prod
from pathlib import Path
import json
P=19
N=9
SLOTS=[(i,j) for i in range(N) for j in range(i)]
D=1+len(SLOTS)+N
SLOT_MAP={ij:k+1 for k,ij in enumerate(SLOTS)}
@cache
def size(t): return 1+sum(map(size,t))
@cache
def density(t): return size(t)*prod(map(density,t))
def trees(n):
    counts=[]
    ts=[]
    for d in range(1,n+1):
        def forests(start,left):
            if not left:
                yield ()
                return
            for i in range(start,len(ts)):
                w=size(ts[i])
                if w>left:break
                for f in forests(i,left-w):yield (ts[i],)+f
        ss=list(forests(0,d-1))
        ts.extend(ss)
        counts.append(len(ss))
    assert counts==[1,1,2,4,9,20,48,115][:n]
    return ts
TS=trees(7)
BUSH=((),)*7
def values(A,b,m,ts=TS):
    @cache
    def stage(t):
        phases=[[sum(aij*xj for aij,xj in zip(row,stage(u)))%m for row in A] for u in t]
        return [prod(w[i] for w in phases)%m for i in range(N)]
    return [(density(t)*sum(bi*ti for bi,ti in zip(b,stage(t))))%m for t in ts]
def jacobian(A,b,p=P):
    @cache
    def data(t):
        # Return stage vector and full gradient of every stage (dual-number arithmetic).
        Cs=[data(c) for c in t]
        out=[]
        for i in range(N):
            v=1
            w=[0]*D
            for S in Cs:
                f=sum(A[i][j]*S[j][0] for j in range(i+1))%p
                g=[sum(A[i][j]*S[j][1][k] for j in range(i+1))%p for k in range(D)]
                for j in range(i+1):
                    g[(SLOT_MAP[i,j] if i>j else 0)]+=S[j][0]
                v,w=v*f%p,[(wk*f+v*gk)%p for wk,gk in zip(w,g)]
            out.append((v,w))
        return out
    ret=[]
    for t in TS:
        H=data(t)
        v=density(t)
        G=[v*sum(bi*h[1][k] for bi,h in zip(b,H))%p for k in range(D)]
        for i in range(N):G[1+len(SLOTS)+i]=(G[1+len(SLOTS)+i]+v*H[i][0])%p
        ret.append(G)
    return ret
def update(A,b,x,times,mod):
    AA=[row[:] for row in A]
    for i in range(N):AA[i][i]=(A[i][i]+times*x[0])%mod
    for (i,j),k in SLOT_MAP.items():AA[i][j]=(A[i][j]+times*x[k])%mod
    bb=[(bi+times*xi)%mod for bi,xi in zip(b,x[-N:])]
    return AA,bb
def system(J,y,p=P):
    aug=[list(row)+[rhs]+[int(j==i) for j in range(len(J))] for i,(row,rhs) in enumerate(zip(J,y))]
    piv=[]
    for j in range(D):
        k=len(piv)
        u=next((i for i in range(k,len(J)) if aug[i][j]),None)
        if u is None:continue
        aug[k],aug[u]=aug[u],aug[k]
        r=aug[k]
        w=pow(r[j],-1,p)
        r=[x*w%p for x in r]
        aug[k]=r; piv.append(j)
        for i,row in enumerate(aug):
            if i==k or not row[j]:continue
            w=row[j]
            aug[i]=[(x-w*z)%p for x,z in zip(row,r)]
    for row in aug[len(piv):]:
        if row[D]:
            q=row[D+1:]
            assert all(sum(w*r[j] for w,r in zip(q,J))%p==0 for j in range(D))
            assert sum(w*t for w,t in zip(q,y))%p==row[D]!=0
            return None,len(piv),q
    x=[0]*D
    for i,j in enumerate(piv):x[j]=aug[i][D]
    assert [sum(a*z for a,z in zip(r,x))%p for r in J]==list(y)
    return x,len(piv),None
def digit(A,b,k,J=None):
    m=P**k
    M=m*P
    v=values(A,b,M)
    assert all(vi%m==1 for vi in v)
    y=[(1-vi)//m%P for vi in v]
    J=J if J is not None else jacobian(A,b)
    x,rank,q=system(J,y)
    if x is None:return None,rank,q,y
    AA,bb=update(A,b,x,m,M)
    assert values(AA,bb,M)==[1]*len(TS)
    assert values(AA,bb,M,[BUSH])[0]%P!=1
    return (AA,bb),rank,None,y
if __name__=='__main__':
    ledger=json.loads(Path(__file__).with_name('nine-stage-19-power-lifts.json').read_text())
    data=ledger['residue']
    J=jacobian(data['A'],data['b'])
    for j in range(D):
        x=[int(i==j) for i in range(D)]
        Ap,bp=update(data['A'],data['b'],x,P,P*P)
        dj=[(a-b)//P%P for a,b in zip(values(Ap,bp,P*P),values(data['A'],data['b'],P*P))]
        assert dj==[row[j] for row in J]
    A,b=data['A'],data['b']
    for k in range(1,ledger['highest-k']):
        result,rank,q,y=digit(A,b,k,J)
        assert result is not None and rank==43
        A,b=result
        m=P**(k+1)
        if k in (1,ledger['highest-k']-1):
            rec=ledger['square' if k==1 else 'top']
            assert rec=={'modulus':m,'A':A,'b':b,'next-bush-value':values(A,b,m,[BUSH])[0]}
        print(f'Lift verified modulo 19^{k+1} (residual Jacobian rank {rank}).')
