"""Exact polynomial-time Gram check for scaled rooted-tree tableau data (standard library)."""
from pathlib import Path
import json, sys, time

def load(path):
    t=json.loads(Path(path).read_text())
    M=t['a_integer']; w=t['b_integer']; d=t['a_denominator']; e=t['b_denominator']
    s=len(M); p=t['order']
    if not (s==len(w)==t['stages'] and s and d and e and all(len(r)==s for r in M)):
        raise ValueError("inconsistent tableau dimensions or scales")
    if not (all(type(v) is int for v in [d,e,p]+w+[x for r in M for x in r]) and p>0):
        raise ValueError("expected literal integer numerators/scales and a positive order")
    return M,w,d,e,p

def gram(M,w,d,e,p):
    """Cov[g] is the sum of outer products at tree size g+1; T[g] is L Cov[g] Lᵀ."""
    s=len(M);m=s+1
    L=[r+[0] for r in M]+[[0]*s+[d]]
    nz=[[(j,a) for j,a in enumerate(r) if a] for r in L]
    C=[[[1]*m for _ in range(m)]]
    H=[];T=[]
    for g in range(p):
        if g:
            N=[[0]*m for _ in range(m)]
            for r in range(g):
                l=g-r
                for i in range(m):
                    bi=l if i<s else 1
                    for j in range(i+1):
                        bj=l if j<s else 1
                        N[i][j] += C[r][i][j]*T[l-1][i][j]*(bi*bj)
            for i in range(m):
                for j in range(i):N[j][i]=N[i][j]
            C.append(N)
        v=[(g+1)*a for a in w]+[-e]
        energy=sum(a*C[g][i][j]*b for i,a in enumerate(v) if a for j,b in enumerate(v) if b)
        if energy:
            raise ValueError(f"nonzero exact sum of squared defects at order {g+1}: {energy}")
        if g+1<p:
            Y=[[sum(a*C[g][k][j] for k,a in nz[i]) for j in range(m)] for i in range(m)]
            Z=[[0]*m for _ in range(m)]
            for i in range(m):
                for j in range(i+1):
                    Z[i][j]=Z[j][i]=sum(Y[i][k]*a for k,a in nz[j])
            H.append(Y);T.append(Z)
    return C,H,T
if __name__=='__main__':
    for file in sys.argv[1:]:
        t=time.monotonic(); M,w,d,e,p=load(file)
        C,_,_=gram(M,w,d,e,p)
        print(f"{file}: zero Gram energy for orders 1-{p}; {time.monotonic()-t:.2f}s, max entry bit lengths",
            [max(abs(v).bit_length() for r in c for v in r) for c in C],flush=True)
