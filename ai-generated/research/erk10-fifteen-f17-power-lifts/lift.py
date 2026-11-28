"""Audit unrestricted first-order lifts of a strict ERK tableau mod 17."""
from functools import cache
import json,sys
from math import prod
from pathlib import Path
import numpy as np

p=17
d=json.loads(Path(sys.argv[1]).read_text())
assert d['field']==p
B=np.array(d['b'],dtype=np.int64)
s=len(B)
A=np.zeros((s,s),dtype=np.int64)
cols=[(i,j) for i in range(s) for j in range(i)]
for i,row in enumerate(d['A']):
    assert len(row)==i
    A[i,:i]=row
N=len(cols)
var=N+s
i,j=np.array(cols).T

@cache
def grade(t):
    return 1+sum(grade(v) for v in t)

@cache
def trees(n):
    return forests(n-1,())

@cache
def forests(n,t):
    if n==0: return ((),)
    return tuple((u,)+v for g in range(grade(t),n+1) for u in trees(g)
          if grade(u)>grade(t) or u>=t for v in forests(n-g,u))

@cache
def density(t):
    return grade(t)*prod(map(density,t))

@cache
def stage(t):
    c=np.ones(s,dtype=np.int64)
    J=np.zeros((s,N),dtype=np.int64)
    for u in t:
        old,dd=stage(u)
        read=A@old % (p*p)
        dread=A@dd % p
        dread[i,np.arange(N)]=(dread[i,np.arange(N)]+old[j])%p
        J=(J*read[:,None]+c[:,None]*dread)%p
        c=c*read%(p*p)
    return c,J

ts=[t for size in range(1,11) for t in trees(size)]
assert len(ts)==1205 and len(set(ts))==1205
M=np.empty((len(ts),var),dtype=np.int64)
rhs=np.empty(len(ts),dtype=np.int64)
for k,t in enumerate(ts):
    c,J=stage(t)
    g=density(t)
    z=(g*int(B@c)-1)%(p*p)
    assert z%p==0
    rhs[k]=(-z//p)%p
    M[k,:N]=g*(B@J)%p
    M[k,N:]=g*c%p

R=np.column_stack([M,rhs])
C=np.eye(len(ts),dtype=np.int64)
row=0
pivots=[]
for col in range(var):
    cand=np.flatnonzero(R[row:,col])
    if not len(cand): continue
    k=row+int(cand[0])
    R[[row,k]],C[[row,k]]=R[[k,row]],C[[k,row]]
    h=pow(int(R[row,col]),-1,p)
    R[row]=(h*R[row])%p; C[row]=(h*C[row])%p
    rr=np.flatnonzero(R[:,col]); rr=rr[rr!=row]
    mu=R[rr,col].copy()
    R[rr]=(R[rr]-mu[:,None]*R[row])%p
    C[rr]=(C[rr]-mu[:,None]*C[row])%p
    pivots.append(col)
    row+=1
assert np.all(R[row:,:var]==0)

# Retain one independently checked row reduction for every higher precision.
AA=A.astype(object); BB=B.astype(object)
mod=p
out=[]
print(f'{s} stages; {len(ts)} rooted equations; {var} variables; Jacobian rank {row}',flush=True)
for k in range(2,21):
    target=p*mod
    @cache
    def current_stage(t):
        c=np.ones(s,dtype=object)
        for u in t: c=c*(AA@current_stage(u)%target)%target
        return c
    residual=[(density(t)*int(BB@current_stage(t))-1)%target for t in ts]
    assert all(v%mod==0 for v in residual)
    r=np.array([(-v//mod)%p for v in residual],dtype=np.int64)
    r1=C@r%p
    fs=np.flatnonzero(r1[row:])
    if len(fs):
        z=C[row+int(fs[0])]
        assert np.all(z@M%p==0) and z@r%p != 0
        print(f'No next lift of this selected mod {mod} representative, at 17^{k}.',flush=True)
        break
    X=np.zeros(var,dtype=np.int64); X[pivots]=r1[:row]
    assert np.all((M@X-r)%p==0)
    AA[i,j]+=mod*X[:N].astype(object); BB+=mod*X[N:].astype(object)
    current_stage.cache_clear()
    assert all((density(t)*int(BB@current_stage(t))-1)%target==0 for t in ts)
    w=(11*int(BB@current_stage(((),)*10))-1)%target
    assert w%p==8
    cert={'field':target,'A':[x[:h].tolist() for h,x in enumerate(AA)],'b':BB.tolist(),
          'next_failure_value':w,'prime':p,'exponent':k}
    out.append(cert)
    print(f'Characteristic {target} = 17^{k}; 1,205 checks green; bush defect {w}',flush=True)
    Path(sys.argv[2]).write_text(json.dumps(out,indent=2)+'\n')
    mod=target
