#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import combinations
from dataclasses import dataclass
@dataclass(frozen=True)
class Q:
    a:F=F(0);b:F=F(0)
    def __init__(self,a=0,b=0):
        if isinstance(a,Q): a,b=a.a,a.b
        object.__setattr__(self,'a',F(a));object.__setattr__(self,'b',F(b))
    def __add__(self,z):
        z=Q(z);return Q(self.a+z.a,self.b+z.b)
    __radd__=__add__
    def __neg__(self):return Q(-self.a,-self.b)
    def __sub__(self,z):return self+-Q(z)
    def __rsub__(self,z):return Q(z)+-self
    def __mul__(self,z):
        z=Q(z);return Q(self.a*z.a+15*self.b*z.b,self.a*z.b+self.b*z.a)
    __rmul__=__mul__
    def inv(self):
        d=self.a*self.a-15*self.b*self.b
        return Q(self.a/d,-self.b/d)
    def __truediv__(self,z):return self*Q(z).inv()
    def __rtruediv__(self,z):return Q(z)*self.inv()
    def __pow__(self,n):
        if n<0:return self.inv()**(-n)
        if not n:return Q(1)
        if n==1:return self
        x=self**(n//2)
        return x*x*(self if n%2 else 1)
    def __bool__(self):return bool(self.a or self.b)
    def __eq__(self,z):
        try:z=Q(z)
        except:return False
        return self.a==z.a and self.b==z.b
    def __float__(self):return float(self.a)+15**.5*float(self.b)
    def vec(self):return [str(self.a),str(self.b)]
def dot(A,B):return sum((a*b for a,b in zip(A,B)),Q())
def pe(A,x):
    r=Q()
    for a in A[::-1]: r=r*x+a
    return r
def pmul(A,B):
    r=[Q() for _ in range(len(A)+len(B)-1)]
    for i,a in enumerate(A):
        for j,b in enumerate(B):r[i+j]+=a*b
    return r
def pp(roots):
    out=[Q(1)]
    for a in roots:out=pmul(out,[-a,1])
    return out
def J(A):return [Q()]+[Q(x)/(k+1)for k,x in enumerate(A)]
def Lagrange(S,j):
    A=pp([z for i,z in enumerate(S)if i!=j])
    c=pe(A,S[j]);return [a/c for a in A]
def solve(M,y):
    n=len(M)
    A=[[Q(u)for u in r]+[Q(v)]for r,v in zip(M,y)]
    for k in range(n):
        p=next((j for j in range(k,n) if A[j][k]),None)
        if p is None:return
        A[k],A[p]=A[p],A[k]
        A[k]=[z/A[k][k]for z in A[k]]
        for j in range(n):
            if j!=k and A[j][k]:A[j]=[x-A[j][k]*z for x,z in zip(A[j],A[k])]
    return [z[-1]for z in A]
def mrow(R,which):
    n=len(R)
    return [R[k] if k in which else Q() for k in range(n)]
def orientation(P):
    aa,bb,cc,dd,ee=P
    N=[Q(0),Q(1),aa,bb,cc,dd,ee]
    W={x:pe(J(Lagrange(N,j)),Q(1)) for j,x in enumerate(N)}
    assert all(sum((W[x]*x**k for x in N),Q())==Q(1)/(k+1)for k in range(9))
    rs=[Q(1),aa,bb,aa,bb,cc,dd,ee]
    wt=[W[Q(1)],W[aa]/2,W[bb]/2,W[aa]/2,W[bb]/2,W[cc],W[dd],W[ee]]
    y=[1-x for x in rs]
    a,b=y[1:3]
    C=[Q() for _ in rs]
    L=[C[:]for _ in rs]
    def assign(i,known):
        for j,t in known.items():L[i][j]=t
        L[i][0]=y[i]-sum(L[i])
    L[1][0]=a
    k=b*(a-b)/a
    assign(2,{1:k})
    al=2*a*(3*b-2*a)/(6*(b-a));be=-2*a**3/(6*b*(b-a))
    assign(3,{1:al,2:be})
    U=[Q(),-a*a/2,k*a-b*b/2,a*a/2]+[Q()]*4
    w1=k*a*a-b**3/3
    h1=k*U[1]
    coef=solve([y[1:4],[z*z for z in y[1:4]],U[1:4]],[b*b/2-U[2],b**3/3-w1,-h1])
    if coef is None:return None
    assign(4,dict(enumerate(coef,1)))
    U[4]=-U[2]
    X=[Q(),Q(),Q(1),Q(),Q(-1)]+[Q()]*3 # second opposed B direction
    assert U[1] and X[2]
    payU=[dot(L[i],y)-y[i]**2/2 for i in range(5)]
    assert payU==U[:5]
    low=[dot(L[i],[z**3 for z in y])-y[i]**4/4 for i in range(5)]
    G=lambda s:(a+b)*s**3/3-a*b*s*s/2-s**4/4
    fixed=low+[G(y[5]),Q(),Q()]
    for i,j in [(1,3),(2,4)]:
        assert sum(wt[k]*(dot(L[k],[z*z for z in y])-y[k]**3/3)for k in (i,j))==0
        assert sum(wt[k]*dot(L[k],U)for k in (i,j))==0
        assert sum(wt[k]*fixed[k]for k in (i,j))==(wt[i]+wt[j])*G(y[i])
    P0=pp([Q(),dd,ee])
    D=sum((wt[i]*z*pe(P0,x)for i,(z,x)in enumerate(zip(fixed,rs))),Q())
    if not D:return
    T=sum((wt[i]*z*pe(P0,x)*x for i,(z,x)in enumerate(zip(fixed,rs))),Q())/D
    return L,rs,y,wt,U,X,fixed,pp([Q(),dd,ee,T]),T,W[Q()]
def seed(p,q,r,e,P):
    p,q,r,e=map(Q,(p,q,r,e))
    c=[Q(),e,2*p/3,p,q,r];s=c[2]
    A=[[Q()]*i for i in range(6)]
    A[1][0]=e;A[2]=[s-s*s/(2*e),s*s/(2*e)]
    A[3]=[p/4,Q(),3*p/4]
    def put(i,add=Q()):
        t=c[i];m1=t*t/2-add*q;m2=t**3/3-add*q*q
        as0=(p*m1-m2)/(s*(p-s));ap0=(m2-s*m1)/(p*(p-s))
        A[i]=[t-as0-ap0-add,Q(),as0,ap0]+([add] if i==5 else [])
    put(4)
    def ell(f):
        put(5,f)
        Q3=[dot(A[i],[z**3 for z in c])-c[i]**4/4 for i in (3,4,5)]
        V=[A[i][2]for i in (3,4,5)]
        return [Q3[(i+1)%3]*V[(i+2)%3]-Q3[(i+2)%3]*V[(i+1)%3]for i in range(3)]
    E=[pe(P,t)for t in (p,q,r)]
    l0,l1=ell(Q()),ell(Q(1))
    Z=dot(l0,E);D=dot(l1,E)-Z
    if not D:return
    f=-Z/D
    l=ell(f)
    assert dot(l,E)==0 and l[2]
    d=[dot(l,[k**i for k in (p,q,r)])for i in range(5)]
    i=next(k for k in range(1,5)if d[k])
    H=[]
    for j in range(1,5):
        if j==i:continue
        v=[Q()]*5;v[j]=Q(1);v[i]=-d[j]/d[i];assert dot(v,d)==0
        H.append(v)
    db=[[Q()]*6 for _ in range(4)]
    old=[Q(),p,q,r]
    for j,c0 in enumerate([0,3,4,5]):
        for i,v in enumerate(Lagrange(old,j)):db[i][c0]=v
    return A,c,db,H,f,l
def tail(O,S):
    L,x,y,w,u,v,p,test,tau,wzero=O
    A,old,Pi,H,f,ell=S
    eta=solve([[w[i]*pe(g,x[i])for i in (5,6,7)]for g in H],
              [-sum((w[i]*dot(L[i],v)*pe(g,x[i])for i in range(5)),Q())for g in H])
    if eta is None:return
    eta_p=None
    for ii,jj in combinations(range(3),2):
        H2=[H[ii],H[jj]]
        X2=[[w[i]*pe(g,x[i])for i in (6,7)]for g in H2]
        F2=[-sum((w[i]*p[i]*pe(g,x[i])for i in range(6)),Q())for g in H2]
        Z=solve(X2,F2)
        if Z is not None:eta_p=Z;break
    if eta_p is None:return
    for j,k in zip((6,7),eta_p):p[j]=k
    assert all(dot([w[i]*p[i]for i in range(8)],[pe(g,z)for z in x])==0 for g in H)
    U2=[z*z for z in y];U3=[z**3 for z in y]
    for i in (5,6,7):
        S0=5 if i==5 else 6
        R=[[Q(1)]*S0,y[:S0],U2[:S0],u[:S0],v[:S0]]
        D=[y[i],y[i]**2/2,y[i]**3/3,Q(),eta[i-5]]
        if i>5:R.append(U3[:S0]);D.append(y[i]**4/4+p[i])
        T=solve(R,D)
        if T is None:return
        L[i][:S0]=T
    g=[dot(L[i],U2)-y[i]**3/3 for i in range(8)]
    h=[dot(L[i],u)for i in range(8)]
    assert all(dot(L[i],y)-y[i]**2/2==u[i] for i in range(8))
    assert all(dot(L[i],U3)-y[i]**4/4==p[i] for i in range(8))
    for row in (u,g,h):
        assert all(sum((w[i]*row[i]for i in range(8)if x[i]==a),Q())==0 for a in set(x))
    assert all(dot([w[i]*dot(L[i],v)for i in range(8)],[pe(g,z)for z in x])==0 for g in H)
    n=len(x)
    B=[[w[n-1-j]*L[n-1-j][n-1-i]/w[n-1-i] if j<i else Q() for j in range(n)]for i in range(n)]
    cs=x[::-1]
    A0=[row+[Q()]*(14-len(row))for row in A]
    for i in range(n):
        vals=[cs[i]**(k+1)/(k+1)-dot(B[i],[z**k for z in cs])for k in range(4)]
        C=[dot(vals,[Pi[r][j]for r in range(4)])for j in range(6)]
        A0.append(C+B[i])
    b=[wzero]+[Q()]*5+w[::-1]
    assert [sum(row)for row in A0]==old+cs
    return A0,b,L,tau,ell,f,Pi,H
