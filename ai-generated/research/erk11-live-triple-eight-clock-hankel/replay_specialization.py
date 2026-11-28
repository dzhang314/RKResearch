"""Exact finite-field specialization certificates for the clock-only contact gate."""
from itertools import combinations, product
from math import gcd
from operator import add, mul
from functools import reduce

class Prime:
    def __init__(self,p):
        assert all(p%d for d in range(2,int(p**0.5)+1))
        self.p=p; self.n=1; self.o=0; self.i=1; self.bs=[1]
    def c(self,n): return n%self.p
    def add(self,a,b): return (a+b)%self.p
    def neg(self,a): return -a%self.p
    def mul(self,a,b): return a*b%self.p
    def inv(self,a):
        assert a
        z=pow(a,-1,self.p)
        return z
    def sub(self,a,b): return (a-b)%self.p
    def div(self,a,b): return self.mul(a,self.inv(b))
    def coords(self,a): return [a]
    def monic(self,c): return [self.div(x,c[-1]) for x in c[:-1]]

class Alg:
    def __init__(self,K,g):
        self.K=K; self.p=K.p; self.g=g; self.deg=len(g); self.n=K.n*self.deg
        self.o=(K.o,)*self.deg
        self.i=(K.i,)+(K.o,)*(self.deg-1)
        self.bs=[(K.o,)*j+(x,)+(K.o,)*(self.deg-j-1) for j in range(self.deg) for x in K.bs]
        self.root=(K.o,K.i)+(K.o,)*(self.deg-2) if self.deg>1 else (-g[0],)
    def lift(self,x): return (x,)+(self.K.o,)*(self.deg-1)
    def c(self,n): return self.lift(self.K.c(n))
    def add(self,a,b): return tuple(self.K.add(x,y) for x,y in zip(a,b))
    def sub(self,a,b): return tuple(self.K.sub(x,y) for x,y in zip(a,b))
    def neg(self,a): return tuple(self.K.neg(x) for x in a)
    def mul(self,a,b):
        K=self.K; d=self.deg
        q=[K.o]*(2*d-1)
        for i in range(d):
            for j in range(d):
                q[i+j]=K.add(q[i+j],K.mul(a[i],b[j]))
        for i in range(2*d-2,d-1,-1):
            for j in range(d):
                q[i-d+j]=K.sub(q[i-d+j],K.mul(q[i],self.g[j]))
        return tuple(q[:d])
    def coords(self,a): return [u for x in a for u in self.K.coords(x)]
    def from_coords(self,r):
        if isinstance(self.K,Prime): return tuple(r)
        return tuple(self.K.from_coords(r[i:i+self.K.n]) for i in range(0,self.n,self.K.n))
    def inv(self,a):
        M=[self.coords(self.mul(a,x)) for x in self.bs]
        return self.from_coords(solve_mod(self.p, list(map(list,zip(*M))),self.coords(self.i)))
    def dev(self,a): return tuple(self.coords(a))
    def determinant(self,a):
        M=[self.coords(self.mul(a,x)) for x in self.bs]
        return det_mod(self.p,M)

def solve_mod(p,M,z):
    n=len(M); H=[list(x)+[v] for x,v in zip(M,z)]
    for i in range(n):
        js=[j for j in range(i,n) if H[j][i]%p]
        if not js: raise ZeroDivisionError('singular solve')
        j=js[0]; H[j],H[i]=H[i],H[j]
        u=pow(H[i][i]%p,-1,p); H[i]=[x*u%p for x in H[i]]
        for j in range(n):
            if j!=i:
                v=H[j][i]; H[j]=[(y-v*x)%p for x,y in zip(H[i],H[j])]
    return [x[-1] for x in H]

def det_mod(p,M):
    n=len(M); H=[list(x) for x in M]; d=1
    for i in range(n):
        js=[j for j in range(i,n) if H[j][i]%p]
        if not js: return 0
        j=js[0]
        if j!=i: H[j],H[i]=H[i],H[j]; d=-d
        v=H[i][i]%p; d=d*v%p; v=pow(v,-1,p)
        for j in range(i+1,n):
            u=H[j][i]*v%p
            H[j]=[(y-u*x)%p for x,y in zip(H[i],H[j])]
    return d%p

def prodk(K,*xs): return reduce(K.mul,xs,K.i)
def sumk(K,*xs): return reduce(K.add,xs,K.o)
def pol(K,as_,x): return reduce(lambda y,c: K.add(K.mul(y,x),K.c(c)),reversed(as_),K.o)
W=[-1] # avoid accidental object mutation
def coefs(K,xs):
    r=[K.i]
    for x in xs:
        r=[K.sub(s,K.mul(x,t)) for s,t in zip([K.o]+r,r+[K.o])]
    return r
def moments(K,xs,n):
    cs=coefs(K,xs); p=K.p
    return [sumk(K,*(K.mul(c,K.c(pow((i+j+2)*(i+j+3),-1,p))) for i,c in enumerate(cs))) for j in range(n)]
def d3(K,m):
    A,B,C,D,E=m
    return sumk(K,prodk(K,A,C,E),prodk(K,B,C,D,K.c(2)),K.neg(prodk(K,A,D,D)),K.neg(prodk(K,B,B,E)),K.neg(prodk(K,C,C,C)))
def four(K,a,sample):
    p=K.p
    # For fixed a, determinant in b has degree at most 6; interpolate data.
    J=[[(x**i)%p for i in range(7)] for x in range(7)]
    E=[K.c(d3(K,moments(K,[a,K.div(a,2),1-b,1-K.div(b,2)],5))) for b in range(7)]
    D=solve_mod(p,J,E)
    if not D[6]: return None
    L=Alg(K,K.monic(D)); la=L.c(a); lb=L.root
    inv2=L.c(pow(2,-1,p)); lhalf=L.mul(la,inv2); ld=L.sub(L.i,lb); le=L.sub(L.i,L.mul(lb,inv2))
    m0,m1,m2,m3,m4=moments(L,[la,lhalf,ld,le],5)
    delta=L.sub(L.mul(m0,m2),L.mul(m1,m1))
    deltadet=L.determinant(delta)
    if not deltadet: return None
    di=L.inv(delta); qa=L.mul(di,L.sub(L.mul(m1,m2),L.mul(m0,m3))); qb=L.mul(di,L.sub(L.mul(m1,m3),L.mul(m2,m2)))
    R=Alg(L,[qb,qa]); h=[R.lift(x) for x in [la,lhalf,ld,le]]; t=R.root; u=R.neg(R.add(R.lift(qa),t))
    return R,[*h,t,u],D[6],deltadet

def three(K,a,j):
    p=K.p
    ah=K.div(a,2)
    b=([K.sub(2,a),K.sub(2,2*a),K.div(K.sub(2,a),2)])[j]
    d=K.sub(1,b); e=K.sub(1,K.div(b,2))
    cs=list(dict.fromkeys([a,ah,d,e]))
    if len(cs)!=3:return None
    m=moments(K,cs,6); D=[[m[i+j] for j in range(3)] for i in range(3)]
    det=det_mod(p,D)
    if not det:return None
    g=solve_mod(p,D,[(-x)%p for x in m[3:]])
    L=Alg(K,g); t=L.root # cubic coefficient order (constant, linear, quadratic)
    u2=L.add(t,L.c(g[2])); u1=L.add(L.c(g[1]),L.mul(t,u2))
    R=Alg(L,[u1,u2]); u=R.root; r=R.lift(t)
    w=R.neg(sumk(R,R.c(g[2]),r,u))
    return R,[*(R.c(x) for x in [a,ah,d,e]),r,u,w],det

T=[1,-32,216,-480,330]
U=[
 [1,-32,216,-480,330],
 [-32,992,-6480,13920,-9240],
 [216,-6480,41040,-85680,55440],
 [-480,13920,-85680,174720,-110880],
 [330,-9240,55440,-110880,69300]]
def psi(K,nodes,left,right):
    a,_,d,_=nodes[:4]; b=K.sub(K.i,d)
    z,x=(nodes[i] for i in left); v,u=(K.sub(K.i,nodes[i]) for i in right)
    l0=K.mul(K.sub(a,x),K.sub(a,z)); l1=K.neg(K.mul(x,z))
    r0=K.mul(K.sub(b,u),K.sub(b,v)); r1=K.neg(K.mul(u,v))
    ur=reduce(lambda z,r:K.add(K.mul(z,a),pol(K,r,b)),reversed(U),K.o)
    return sumk(K,K.mul(l0,r0),prodk(K,l1,r0,pol(K,T,a)),prodk(K,l0,r1,pol(K,T,b)),prodk(K,l1,r1,ur))

def shapes(j):
    if j==3: # no collision. Last two labels are free.
        left=list(combinations([2,3,4,5],2)); right=list(combinations([0,1,4,5],2))
        return [(L,R) for L,R in product(left,right) if not (2 in L and 0 in R)]
    # Known clock indices a,h,d,e occupy fixed positions, with exactly one identified calibration pair.
    active=[4,5,6]
    if j==0: ll=[2,*active]; rr=[0,*active]        # h=e
    if j==1: ll=[2,*active]; rr=[*active]          # a=e, so triple already used at a and d confined
    if j==2: ll=[*active]; rr=[0,*active]          # h=d, so triple already used at d and a confined
    return [(L,R) for L,R in product(combinations(ll,2),combinations(rr,2)) if not (2 in L and 0 in R)]

def scan(j,p):
    K=Prime(p)
    tests=shapes(j)
    for a in range(2,p):
        red=(four(K,a,p) if j==3 else three(K,a,j))
        if red is not None:
            R,clk,*special=red
            results=[R.determinant(psi(R,clk,L,Rt)) for L,Rt in tests]
            good=sum(x!=0 for x in results)
            if good==len(results): return a, special, results
    return None

if __name__=='__main__':
    for j in range(4):
        for p in (101,103,107,109,113,127):
            r=scan(j,p)
            if r: print(j,p,len(shapes(j)),r,flush=True); break
        else: print('FAILED',j,flush=True)
