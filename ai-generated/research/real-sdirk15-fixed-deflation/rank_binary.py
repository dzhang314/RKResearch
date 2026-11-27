"""Actual exact lower rank of tracked stage columns for the archived real order-15 tableau."""
import json,sys
from pathlib import Path
sys.path.insert(0,sys.argv[1])
from check_two_ports import I,S,B,up,dot
t=json.loads(Path("actual34.json").read_text())
P=int(t["precision"])
assert P>=B
d=1<<(P-B)
def scaled(r):
    l,h=map(int,r)
    return I(l//d,up(h,d))
Z=I.val(0);O=I.val(1)
A=[[scaled(a)for a in row]for row in t['A']]
n=len(A);assert n==34
rows=[]
pivs=[]
def feed(rank,j):
    v=rank[1][:]
    for k,u in zip(pivs,rows):
        q=v[k]
        for i in range(n):
            if i!=k:v[i]=v[i]-q*u[i]
        v[k]=Z
    ix=max(range(n),key=lambda i:v[i].inf())
    if not v[ix].sign():return False
    v=[a/v[ix]for a in v];v[ix]=O
    pivs.append(ix);rows.append(v)
    return True
basis=[]
for m in range(1,16):
    old=basis[:]
    terms=[(m,[O]*n,'.')] if m==1 else [
        (m,[a*b for a,b in zip(ta,ub)],f'({pa},{pb})')
        for (na,ta,ua,pa) in old for (nb,tb,ub,pb) in old if na+nb==m]
    for d,fac,rept in terms:
        if feed((d,fac),len(basis)):
            basis.append((d,fac,[d*dot(r,fac[:len(r)])for r in A],rept))
            if len(basis)==n:break
    print(f'binary tree size ≤{m}: certified column rank ≥{len(basis)}',flush=True)
    if len(basis)==n:break
b=[scaled(a)for a in t['b']]
dist={j:0 for j,x in enumerate(b) if x.sign()}
for d in range(1,n):
    for j in range(n):
        if j not in dist and any(dist[k]==d-1 and A[k][j].sign() for k in dist if j<k):
            dist[j]=d
    if len(dist)==n:break
print('physical path shortest upper bounds by row (weights count zero edges):',dist,flush=True)
assert len(basis)==n and len(dist)==n
print('selected actual binary trees:',[q[-1]for q in basis],flush=True)
