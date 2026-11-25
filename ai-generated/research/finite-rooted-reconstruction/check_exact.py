#!/usr/bin/env python3
"""Small exact checks of finite RK reconstruction; no third-party dependencies."""
from fractions import Fraction as F
from dataclasses import dataclass
from math import prod

@dataclass(frozen=True,eq=False)
class S:
    a:F
    b:F=F(0)
    d:int=3
    def __post_init__(self):
        object.__setattr__(self,'a',F(self.a));object.__setattr__(self,'b',F(self.b))
    def asS(self,y):
        if isinstance(y,S):
            assert y.d==self.d;return y
        return S(F(y),F(0),self.d)
    def __add__(self,y):
        y=self.asS(y);return S(self.a+y.a,self.b+y.b,self.d)
    __radd__=__add__
    def __neg__(self):return S(-self.a,-self.b,self.d)
    def __sub__(self,y):return self+-self.asS(y)
    def __rsub__(self,y):return self.asS(y)+-self
    def __mul__(self,y):
        y=self.asS(y);return S(self.a*y.a+self.d*self.b*y.b,self.a*y.b+self.b*y.a,self.d)
    __rmul__=__mul__
    def __truediv__(self,y):
        y=self.asS(y);w=y.a*y.a-y.d*y.b*y.b
        return self*S(y.a/w,-y.b/w,self.d)
    def __rtruediv__(self,y):return self.asS(y)/self
    def __eq__(self,y):
        y=self.asS(y);return (self.a,self.b)==(y.a,y.b)
    def __bool__(self):return bool(self.a or self.b)
    def __pow__(self,k):
        if k<0:return 1/self**(-k)
        x=self;v=self.asS(1)
        while k:
            if k%2:v*=x
            x*=x;k//=2
        return v

def trees(N):
    ts=[()];ns=[1];gam=[1]
    for n in range(2,N+1):
        def parts(j,k):
            if k==0:yield ();return
            for i in range(j,len(ns)):
                if ns[i]>k:break
                for tail in parts(i,k-ns[i]):yield (i,)+tail
        for e in list(parts(0,n-1)):
            ts.append(e);ns.append(n);gam.append(n*prod(gam[i] for i in e))
    return ts,ns,gam

def dot(x,y):return sum((a*b for a,b in zip(x,y)),F(0))
def Av(A,x):return tuple(dot(a,x) for a in A)
def outer_dot(b,A):return tuple(dot(b,v) for v in zip(*A))
def power(c,j):return tuple(x**j for x in c)
def had(x,y):return tuple(a*b for a,b in zip(x,y))
def evaluate(A,b,ts):
    V=[];AV=[]
    for e in ts:
        v=(F(1),)*len(A)
        for j in e:v=had(v,AV[j])
        V.append(v);AV.append(Av(A,v))
    return V,[dot(b,v) for v in V]

def prodpoly(R):
    p=[F(1)]
    for x in R:
        q=[F(0)]*(len(p)+1)
        for j,y in enumerate(p):q[j]-=x*y;q[j+1]+=y
        p=q
    return p

def Lagrange(c,i):return [u/prod(c[i]-c[j] for j in range(len(c)) if j!=i) for u in prodpoly(c[:i]+c[i+1:])]
def I(f,x):return sum(a*x**(j+1)/(j+1) for j,a in enumerate(f))

def eliminate(A):
    a=[list(v) for v in A];i=0
    for j in range(len(a[0])):
        k=next((k for k in range(i,len(a)) if a[k][j]),None)
        if k is None:continue
        a[i],a[k]=a[k],a[i]
        u=a[i][j];a[i]=[v/u for v in a[i]]
        for k in range(len(a)):
            if k!=i and a[k][j]:
                u=a[k][j];a[k]=[v-u*w for v,w in zip(a[k],a[i])]
        i+=1
        if i==len(a):break
    return i,a

def gauss(r):
    if r==2:
        c=[S(F(1,2),-F(1,6),3),S(F(1,2),F(1,6),3)];b=[F(1,2)]*2
    else:
        assert r==3
        c=[S(F(1,2),-F(1,10),15),S(F(1,2),F(0),15),S(F(1,2),F(1,10),15)]
        b=[F(5,18),F(4,9),F(5,18)]
    assert all(dot(b,power(c,k))==F(1,k+1) for k in range(2*r))
    H=[[F(1,i+j+1) for j in range(r)]+[-F(1,i+r+1)] for i in range(r)]
    n,Q=eliminate(H);assert n==r
    mon=[row[-1] for row in Q]+[F(1)]
    assert mon==prodpoly(c)
    z=[Lagrange(c,j) for j in range(r)]
    A=[tuple(I(l,x) for l in z) for x in c]
    R=[[F(1,(j+1)*(i+j+2)) for j in range(r)] for i in range(r)]
    assert [[sum(z[i][a]*z[j][k]*R[a][k] for a in range(r) for k in range(r))/b[i]
             for j in range(r)] for i in range(r)]==[list(row) for row in A]
    v=[l[-1] for l in z];u=[l/bj for l,bj in zip(v,b)]
    assert [dot(v,power(c,k)) for k in range(r)]==[F(0)]*(r-1)+[F(1)]
    assert [dot(b,had(u,power(c,k))) for k in range(r)]==[F(0)]*(r-1)+[F(1)]
    ts,ns,gt=trees(2*r)
    dts=[]
    for lam in (F(0),F(1,7),F(2,7)):
        T=[tuple(y+lam*u[i]*v[j] for j,y in enumerate(row)) for i,row in enumerate(A)]
        V,sc=evaluate(T,b,ts);assert Av(T,[F(1)]*r)==tuple(c)
        assert all((n==2*r and lam!=0) or s*g==1 for n,s,g in zip(ns,sc,gt))
        w=dot(b,had(power(c,r-1),Av(T,power(c,r-1))))
        assert w==F(1,2*r*r)+lam
        dts.append(w)
        for g in range(r):
            assert eliminate([z for z,n in zip(V,ns) if n<=g+1])[0]==g+1
        Us=[[tuple(b)]]
        for h in range(1,r):
            rows=Us[h-1]+[outer_dot(row,T) for row in Us[h-1]]
            for z,n in zip(V,ns):
                if 1<=n-1<=h:rows.extend(had(row,z) for row in Us[h-n+1])
            Us.append(rows)
            assert eliminate(rows)[0]==h+1
    assert all(dts[i]!=dts[j] for i in range(len(dts)) for j in range(i))
    p=2*r-1
    print(f'r={r}: exact Gauss quotient at order {2*r}, recovered nodal polynomial and A from paid moments. Two distinct rank-one perturbations both exact order {p}, with fixed b,c. All {len(ts)} rooted trees through order {2*r} checked; marked single-link witness outputs '+', '.join(str(x.a) for x in dts)+'. ρ=σ=r−1, δ=1.')


def moments(A,b,c,d):
    return {(a,k):dot(b,had(power(c,a),Av(A,power(c,k)))) for a in range(d+1) for k in range(d+1-a)}

def peel(M,b,c,E,d):
    rows={};rr=[i for i,es in enumerate(E) if es]
    for k,i in enumerate(rr):
        a=prodpoly([c[j] for j in rr[k+1:]])
        z=sum(x*c[i]**j for j,x in enumerate(a))
        a=[x/z for x in a]
        for j in E[i]:
            xx=[c[l] for l in E[i]];y=Lagrange(xx,E[i].index(j))
            assert len(a)+len(y)-2<=d
            v=sum(x*w*M[h,k2] for h,x in enumerate(a) for k2,w in enumerate(y))
            for (r,s),z in rows.items():
                if r==i:continue
                v-=z*sum(x*c[r]**h for h,x in enumerate(a))*sum(w*c[s]**k2 for k2,w in enumerate(y))
            rows[i,j]=v
    return [tuple(rows.get((i,j),0)/b[i] for j in range(len(c))) for i in range(len(c))]

def triangle(s,a=None):
    # Fixed common diagonal a, or a freely varying nonzero diagonal (None).
    c=[F(i+1,s+1) if a is None else a+F(i,s+1) for i in range(s)];b=[F(i+1,11) for i in range(s)]
    if a is None:
        A=[tuple(c[i] if i==j else F(0) for j in range(s)) for i in range(s)];E=[list(range(i+1)) for i in range(s)]
    else:
        A=[tuple((a if i==j else F(0))+(c[i]-a if j==0 else F(0)) for j in range(s)) for i in range(s)];E=[list(range(i)) for i in range(s)]
    d=s-1 if a is None else s-2
    support=E[-1];xs=[c[i] for i in support];v=[Lagrange(xs,j)[-1] for j in range(len(xs))];lam=F(1,17)
    B=A[:-1]+[tuple(x+(lam*v[j] if j in support else 0) for j,x in enumerate(A[-1]))]
    assert Av(A,[F(1)]*s)==Av(B,[F(1)]*s)==tuple(c)
    if a is None:assert B[-1][-1]
    for A0 in (A,B):
        work=[tuple(x-(a if a is not None and i==j else 0) for j,x in enumerate(row)) for i,row in enumerate(A0)]
        assert peel(moments(work,b,c,d),b,c,E,d)==work
    ts,ns,gt=trees(d+2);V,f=evaluate(A,b,ts);W,g=evaluate(B,b,ts)
    assert all(x==y for n,x,y in zip(ns,V,W) if n<=d+1)
    assert dot(b,had(power(c,0),Av(B,power(c,d))))-dot(b,Av(A,power(c,d)))==b[-1]*lam
    assert any(x!=y for n,x,y in zip(ns,f,g) if n==d+2)
    desc='free nonzero diagonal' if a is None else ('strict ERK' if a==0 else 'given nonzero common diagonal')
    print(f'{desc}, s={s}: exact peeling through order {d+2} recovers both matrices. Sharp variants share all stage trees through order {d+1} and differ at order {d+2}.')

def paid_triangles():
    c=[F(0),F(1,3),F(2,3),F(1)];b=[F(1,8),F(3,8),F(3,8),F(1,8)]
    A=[(F(0),)*4,(c[1],F(0),F(0),F(0)),(c[2],F(0),F(0),F(0)),(F(-3),F(4),F(0),F(0))]
    B=A[:-1]+[tuple(x+y for x,y in zip(A[-1],(1,-2,1,0)))]
    ts,n,gt=trees(4)
    f=evaluate(A,b,ts)[1];g=evaluate(B,b,ts)[1]
    assert all(x*t==y*t==1 for k,t,x,y in zip(n,gt,f,g) if k<=3)
    assert all(dot(b,Av(M,Av(M,Av(M,(F(1),)*4))))==0 for M in (A,B))
    assert f!=g and Av(A,(F(1),)*4)==Av(B,(F(1),)*4)==tuple(c)
    c=[F(1,4),F(3,4)];b=[F(1,2)]*2
    A=[(c[0],F(0)),(F(1,4),F(1,2))];B=[A[0],(F(0),c[1])]
    ts,n,gt=trees(3);f=evaluate(A,b,ts)[1];g=evaluate(B,b,ts)[1]
    assert all(x*t==y*t==1 for k,t,x,y in zip(n,gt,f,g) if k<=2)
    assert dot(b,power(c,2))!=F(1,3) and f!=g
    print('Actual paid limits: two four-stage ERKs of exact order 3 and two two-stage nonsingular DIRKs of exact order 2 have fixed b,c, but are not determined until tree order 4 and 3 respectively.')

if __name__=='__main__':
    for r in (2,3):gauss(r)
    for a in (F(0),F(2,7),None):triangle(4,a)
    paid_triangles()
