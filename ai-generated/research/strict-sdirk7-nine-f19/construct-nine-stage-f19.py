from math import prod
from itertools import combinations
from functools import cache
from collections import Counter
import json

p=19; I2=10

def inv(x):return pow(x%p,-1,p)
def dot(x,y):return sum(u*v for u,v in zip(x,y))%p

def poly_mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]=(c[i+j]+x*y)%p
    return c
def poly(xs):
    g=[1]
    for x in xs:g=poly_mul(g,[-x,1])
    return g

def solve(M,values,n=None):
    if n is None:n=len(M[0])
    A=[[x%p for x in a]+[v%p] for a,v in zip(M,values)]
    piv=[]
    l=len(A)
    for j in range(n):
        i=len(piv)
        r=next((r for r in range(i,l) if A[r][j]),None)
        if r is None:continue
        A[i],A[r]=A[r],A[i];a=A[i]
        m=inv(a[j])
        a=[x*m%p for x in a];A[i]=a
        for k in range(l):
            if i==k or not A[k][j]:continue
            q=A[k][j];A[k]=[(x-q*y)%p for x,y in zip(A[k],a)]
        piv.append(j)
        if len(piv)==l:break
    if any(row[-1] for row in A[len(piv):]):return None
    v=[0]*n
    for i,j in enumerate(piv):v[j]=A[i][-1]
    assert [dot(row,v) for row in M]==[v0%p for v0 in values]
    return v

def search():
    stats=Counter()
    for z in range(1,p):
        mass=[pow(z,i,p)*inv(i+1)%p for i in range(7)]
        def mean(f):
            assert len(f)<=7
            return dot(f,mass)
        def pair(f,g): return mean(poly_mul(f,g))
        def T(g):
            return [(-g[0])%p]+[(g[i-1]*inv(i)-(g[i] if i<len(g) else 0))%p for i in range(1,len(g)+1)]
        all_choices=range(p)
        # In reflected time the last two clocks are u,1; the first three form a monic F3.
        k=[-1,2,-I2]; Tk=T(k)
        for u in range(p):
            if u==1:continue
            H=poly([1,u]); Th=T(H)
            poss=[j for j in range(p) if j not in (1,u)]
            for C3 in combinations(poss,3):
                F3=poly(C3)
                if pair(Th,F3) or pair(Tk,F3):continue
                h0=pair(H,F3); k0=pair(k,F3)
                if not h0:continue
                for x3 in C3:
                    y1,y2=[j for j in C3 if j!=x3]
                    F2=poly([y1,y2])
                    if (k0*pair(Th,F2)-h0*pair(Tk,F2))%p:continue
                    Y4=range(p) if k0==0 else [(2*u-1)%p]
                    for x4 in Y4:
                        if x4 in list(C3)+[1,u]:continue
                        F4=poly(list(C3)+[x4])
                        if pair(H,F4) or pair(k,F4):continue
                        if mean(poly(list(C3)+[x4,u,1])):continue
                        for yy in [(y1,y2),(y2,y1)]:
                            c=[(z-y)%p for y in list(yy)+[x3,x4,u,1]]
                            stats['clocks']+=1
                            X=[[pow(x,j,p) for x in c] for j in range(7)]
                            b=solve(X,mass)
                            if b is None or not all(b):continue
                            b1=[y*x%p for y,x in zip(b,c)]
                            b2=[y*x*x%p for y,x in zip(b,c)]
                            r=solve(X[:5] + [[int(j==i) for j in range(6)] for i in (4,5)], [dot(b,X[j+2])*inv(j+1) for j in range(5)] + [b[-2]*(c[-2]+c[-1]*(z-c[-2]-1)),b[-1]*c[-1]])
                            if r is None:continue
                            stats['r']+=1
                            a=c[0]; coef=(-a*a*I2+2*a-1)%p
                            rhs=-(a*a-3*a+1)%p
                            assert coef
                            uhelper=rhs*inv(coef)%p
                            if uhelper in (0,p-1):continue
                            print('TRY',z, uhelper,c,b,r,stats,flush=True)
                            yield z,uhelper,c,b,r

def construct(z,u,c,b,r):
    n=len(c);X=[[pow(t,d,p) for t in c] for d in range(7)]
    b1=[w*x%p for w,x in zip(b,c)]; b2=[w*x*x%p for w,x in zip(b,c)]
    P=[((2-u)*x+u-1)%p for x in c]
    JP=[((2-u)*x*x*I2+(u-1)*x)%p for x in c]
    slots=[(i,j) for i in range(n) for j in range(i)]
    rows=[];target=[]
    for i0 in range(n):
        rows.append([P[j] if i==i0 else 0 for i,j in slots])
        target.append(JP[i0]-P[i0])
    for j0 in range(n):
        rows.append([b[i] if j==j0 else 0 for i,j in slots])
        target.append(b[j0]*(z-c[j0]-1))
        rows.append([b1[i] if j==j0 else 0 for i,j in slots])
        target.append(r[j0]-b1[j0])
    for w in (r,b2):
        for d in (0,2,3):
            rows.append([w[i]*X[d][j] for i,j in slots])
            target.append(dot(w,X[d+1])*inv(d+1)-dot(w,X[d]))
    ns=solve(rows,target)
    if ns is None:return
    T=[[int(i==j) for j in range(n)] for i in range(n)]
    for (i,j),v in zip(slots,ns):T[i][j]=v
    a32=(u+1)*inv(2*u)%p
    A=[[1,0,0],[u,1,0],[-1-a32,a32,1]]
    c2=1+u
    for x,row in zip(c,T):
        e0=x-sum(row); e1=x*x*I2-dot(row,c); e2=x*x*x*inv(3)-dot(row,X[2])
        f1=(e2-e1)*inv(c2*(c2-1))%p; f0=e1-c2*f1
        A.append([f0,f1,e0-f0-f1]+row)
    A=[row+[0]*(n+3-len(row)) for row in A]
    return [[t*inv(z)%p for t in row] for row in A],[0]*3+b

def enumerate_trees(limit):
    layers=[[()]]
    for n in range(2,limit+1):
        cs=[t for ly in layers for t in ly]
        def forests(start,left):
            if not left:
                yield ()
                return
            for i in range(start,len(cs)):
                if size(cs[i])>left:break
                for x in forests(i,left-size(cs[i])):
                    yield (cs[i],)+x
        layers.append(list(forests(0,n-1)))
    return layers
@cache
def size(t): return 1+sum(map(size,t))
@cache
def factorial(t):return size(t)*prod(map(factorial,t))
layers=enumerate_trees(8)
assert list(map(len,layers))==[1,1,2,4,9,20,48,115]

def verify(A,b):
    @cache
    def coeff(t):
        phases=[tuple(dot(a,coeff(c)) for a in A) for c in t]
        return tuple(prod(y[i] for y in phases)%p for i in range(len(A)))
    def pay(t):return factorial(t)*dot(b,coeff(t))%p
    if any(pay(t)!=1 for ly in layers[:7] for t in ly):return None
    return [(t,pay(t)) for t in layers[7] if pay(t)!=1]

if __name__=='__main__':
    from pathlib import Path
    # Replay the small exact reconstruction at the first viable full
    # chronological scan candidate, rather than trusting a computed optimizer.
    data = json.loads(Path(__file__).with_name("nine-stage-f19.json").read_text())
    z,u,c=data["z"],data["u"],data["c"]
    b=data["b"][3:]
    r=[3,15,17,13,12,7]
    A,w=construct(z,u,c,b,r)
    assert A==data["A"] and w==data["b"]
    assert verify(A,w)[0]==(((),)*7,12)
    print("Reconstructed the exact nine-stage F19 witness by the linear six-tail solve.")
