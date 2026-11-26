"""Paid moment-splice extensions at p=11 and p=12; literal rational replay."""
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, lcm, prod
import json
from pathlib import Path
import sys
here=Path(__file__).resolve().parent
p=int(sys.argv[1])
assert p in (11,12)
m=p-4
U=2*3*5*7*11
zero,one=F(0),F(1)
def rem(n):
    n=abs(n)
    while n and (g:=gcd(n,U))>1:n//=g
    return n
def unit(x):
    x=F(x)
    return rem(x.numerator)==rem(x.denominator)==1
def paid(x):return rem(F(x).denominator)==1
def matdet(M):
    A=[list(map(F,r)) for r in M]
    a=F(1)
    for j in range(len(A)):
        k=next((k for k in range(j,len(A))if A[k][j]),None)
        if k is None:return F(0)
        if k!=j:A[j],A[k]=A[k],A[j];a=-a
        v=A[j][j];a*=v
        for k in range(j+1,len(A)):
            if not A[k][j]:continue
            v1=A[k][j]/v
            for l in range(j+1,len(A)):A[k][l]-=v1*A[j][l]
    return a
def adj(M):
    d=matdet(M)
    assert unit(d),d
    return [[(-1)**(i+j)*matdet([[v for l,v in enumerate(rr) if l!=i] for k,rr in enumerate(M) if k!=j])/d
              for j in range(len(M))] for i in range(len(M))]
def dot(a,b):return sum((x*y for x,y in zip(a,b)),zero)
def mv(M,v):return [dot(r,v) for r in M]
def mm(M,N):return [[dot(r,c) for c in zip(*N)] for r in M]
def pad(v,n):return list(v)+[zero]*(n-len(v))
def basis(i,n):return [F(j==i) for j in range(n)]
def ints(d,*a):return [F(x,d) for x in a]

if p==11:
    seed=[[],ints(9,1),ints(24,1,3),ints(16,1,0,3),ints(500,29,0,33,-12),ints(972,33,0,0,4,125),
          ints(36,-21,0,0,76,125,-162),ints(243,-30,0,0,-32,125,0,99),
          ints(324,1175,0,0,-3456,-6250,8424,242,-27),
          ints(324,293,0,0,-852,-1375,1836,-118,162,324),
          ints(1620,1303,0,0,-4260,-6875,9990,1030,0,0,162),
          ints(8,0,0,0,0,0,3,2,0,0,3,0),
          ints(108,-8595,0,0,30720,48750,-67716,-702,-729,-1944,-2916,3240,0)]
    b=ints(840,41,0,0,0,0,216,272,27,27,36,180,40,1)
else:
    data=json.loads((here/'paid9-seed.json').read_text())
    seed=[list(map(F,r)) for r in data['A']]
    b=list(map(F,data['b']))
cs=[sum(r,zero) for r in seed]
A=seed+[b.copy()]
end=len(seed)
evals=[(zero,0),(one,end)]
def chart(e,k):
    s=len(A)
    g=len(e)+k
    M=[[c**j for j in range(g)] for c,i in e]+[[F(1,j+i+1) for j in range(g)] for i in range(k)]
    L=[basis(i,s)for c,i in e]+[pad([wi*c**i for wi,c in zip(b,cs)],s) for i in range(k)]
    print('forward chart',g,matdet(M))
    return mm(adj(M),L)
def add_stage(P,x):
    r=[dot([x**(j+1)/(j+1) for j in range(len(P))],v) for v in zip(*P)]
    A.append(pad(r,len(A)))
    return (x,len(A)-1)
if p==11:
    P=chart(evals,3)  # exact through derivative order 5
    extra=[add_stage(P,F(1,3))]
    P=chart(evals+extra,3) # exact through derivative order 6
    high=[add_stage(P,y) for y in (F(1,12),F(1,3),F(2,3))]
else:
    P=chart(evals,4) # exact through derivative order 6
    extra=[add_stage(P,y) for y in (F(1,3),F(2,3))]
    P=chart(evals+extra,3) # exact through derivative order 7
    high=[add_stage(P,y) for y in (F(1,12),F(1,4),F(1,3),F(1,2))]
P=chart(evals+high,2)
n=len(A)
assert n== (18 if p==11 else 23)
assert [dot([F(1,j+1) for j in range(m)],v) for v in zip(*P)]==pad(b,n)
reversal=list(map(F,(1,'1/12','1/6','5/6','1/4','1/3','1/2','2/3','3/4','11/12','1/3','1/2','2/3',1)))
xs=reversal
ys=[1-x for x in xs]
w=list(map(F,(1,'576/4235','-9/1925','-9/1925','448/2475',1,1,1,'448/2475','576/4235',
              F(783,15400)-1,F(262,1155)-1,F(783,15400)-1,F(35663,1524600)-1)))
w0=F(35663,1524600)
N=len(xs)
assert all(dot(w,[x**k for x in xs])+(w0 if k==0 else 0)==F(1,k+1) for k in range(p))
S=list(range(1,10))
bar={i:one/prod(xs[i]-xs[j] for j in S if i!=j)for i in S}
u=[zero]*N
u[1]=-ys[1]**2/2
for i in S:
    u[i]=u[1]*w[1]*xs[1]*ys[1]/bar[1]*bar[i]/(w[i]*xs[i]*ys[i])
assert all(dot(w,[xs[i]*ys[i]*u[i]*xs[i]**k for i in range(N)])==0 for k in range(m))
v=[y*y/2+e for y,e in zip(ys,u)]
L=[[zero]*N for _ in range(N)]
L[1][0]=ys[1]
for i in (2,3):
    L[i][1]=v[i]/ys[1]
    L[i][0]=ys[i]-L[i][1]
donors=list(range(4))
M=[[one]*4,[ys[j] for j in donors],[ys[j]**2 for j in donors],[u[j] for j in donors]]
print('reverse donor det',matdet(M))
MI=adj(M)
pivots=list(range(4,10))
if p==11:
    def ff(k,x):return x*(1-x)*x**k
    tests=list(range(6))
else:
    def ff(k,x):return x*(1-x)*(x**k-F(6,(k+2)*(k+3)))
    tests=list(range(1,7))
MF=[[w[i]*ff(k,xs[i]) for i in pivots] for k in tests]
print('reverse weighted det',matdet(MF))
MFI=adj(MF)
need_e=[-sum(w[i]*ff(k,xs[i])*(dot(L[i],[y*y for y in ys])-ys[i]**3/3)for i in range(4))for k in tests]
need_u=[-sum(w[i]*ff(k,xs[i])*dot(L[i],u)for i in range(4))for k in tests]
ce=mv(MFI,need_e);cu=mv(MFI,need_u)
for i in range(4,N-1):
    e,lu=(ce[i-4],cu[i-4]) if i in pivots else (zero,zero)
    r=mv(MI,[ys[i],v[i],ys[i]**3/3+e,lu])
    for j,a in zip(donors,r):L[i][j]=a
assert all(sum(r,zero)==y and dot(r,ys)==z for r,y,z in zip(L,ys,v))
assert all(sum(w[i]*ff(k,xs[i])*(dot(L[i],[y*y for y in ys])-ys[i]**3/3)for i in range(N))==0 for k in tests)
assert all(sum(w[i]*ff(k,xs[i])*dot(L[i],u)for i in range(N))==0 for k in tests)

T=[[w[N-1-j]*L[N-1-j][N-1-i]/w[N-1-i] if L[N-1-j][N-1-i] else zero for j in range(N)]for i in range(N)]
xf=xs[::-1];wf=w[::-1]
K=mm([[xf[i]**(j+1)/(j+1)-dot(T[i],[x**j for x in xf])for j in range(m)]for i in range(N)],P)
assert not any(T[0]) and not any(r[0] for r in T) and K[0]==pad(b,n)
A1=[pad(r,n+N-1) for r in A]+[K[i]+T[i][1:] for i in range(1,N)]
B=[w0]+[zero]*(end-1)+[wf[0]]+[zero]*(n-end-1)+wf[1:]
assert len(A1)==len(B)
index={};rep=[];old_to_new=[];weights=[];merges=[];sigs=[]
for i,row in enumerate(A1):
    assert not any(row[i:])
    d={}
    for j,a in enumerate(row[:i]):
        if a:
            k=old_to_new[j]
            d[k]=d.get(k,zero)+a
    key=tuple(sorted((k,a)for k,a in d.items()if a))
    if key not in index:
        index[key]=len(rep);rep.append(i);sigs.append(key);weights.append(zero)
    else:merges.append((i+1,rep[index[key]]+1,B[i]))
    old_to_new.append(index[key])
    weights[index[key]]+=B[i]
s=len(rep)
A=[[dict(sig).get(j,zero) for j in range(s)]for sig in sigs]
b=weights
print('physical rows',s,'merges',merges)
assert len(set(map(tuple,A)))==s and all(not any(r[i:])for i,r in enumerate(A))
assert all(paid(x) for x in (*b,*(x for r in A for x in r)))

@lru_cache(None)
def forest(n,i=(0,())):
    if n==0:return ((),)
    return tuple((b,)+r for j in range(max(1,i[0]),n+1) for b in tree(j)
                 if (j,b)>=i for r in forest(n-j,(j,b)))
@lru_cache(None)
def tree(n):return forest(n-1)
@lru_cache(None)
def sz(t):return 1+sum(map(sz,t))
@lru_cache(None)
def tf(t):return sz(t)*prod(map(tf,t))
sparse=[[(j,a)for j,a in enumerate(r)if a]for r in A]
@lru_cache(None)
def phi(t):
    V=[ext(u)for u in t]
    return [prod(q[i]for q in V)for i in range(s)]
@lru_cache(None)
def ext(t):return [sum((a*phi(t)[j]for j,a in row),zero)for row in sparse]
def df(t):return tf(t)*dot(b,phi(t))-1
for k,cnt in enumerate((1,1,2,4,9,20,48,115,286,719,1842,4766)[:p],1):
    ts=tree(k)
    assert len(ts)==cnt
    assert all(df(t)==0 for t in ts),k
    print('order',k,'checked',cnt)

bush=lambda n:((),)*(n-1)
u=bush(7) if p==11 else bush(9)
if p==11:
    for j in range(3):u=(u,)
    witness=((),u)
    assert tf(witness)==60480 and df(witness)==F(-10,567)
else:
    witness=((),(),(u,))
    assert tf(witness)==1170 and df(witness)==F(1,3326400)
assert sz(witness)==p+1 and unit(df(witness))
ws=[(witness,str(df(witness)))]
print('next defect witness',ws)
D=lcm(*(z.denominator for r in A for z in r),*(z.denominator for z in b))
D1=D; ds=[]
for q in (2,3,5,7,11):
    e=0
    while D1%q==0:
        D1//=q;e+=1
    ds.append(e)
assert D1==1
print('common denominator',D,'exponents',ds)
out={'A':[[str(z)for z in r[:i]]for i,r in enumerate(A)],'b':[str(z)for z in b],
     'coefficient_common_denominator':str(D),'defect_witness':ws}
dst=here/f'tableau-{p}.json'
if '--write-tableau' in sys.argv:dst.write_text(json.dumps(out,indent=2)+'\n')
else:assert json.loads(dst.read_text())==json.loads(json.dumps(out))
