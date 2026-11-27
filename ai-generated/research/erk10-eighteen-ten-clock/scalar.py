from fractions import Fraction as F
from math import prod, gcd
from itertools import product, combinations,permutations
from functools import lru_cache

def unpaid(a):
    a=abs(a)
    if not a:return 0
    for p in [2,3,5,7]:
        while a%p==0:a//=p
    return a
def paid(x):return unpaid(F(x).denominator)==1
def unit(x):return unpaid(F(x).numerator)==1 and paid(x)

def mul(a,b):
    out=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j]+=x*y
    return out
def hull(S):
    out=[F(1)]
    for a in S:out=mul(out,[-a,F(1)])
    return out
def dot(X,Y):return sum((a*b for a,b in zip(X,Y)),F(0))
def pe(P,x):
    r=F(0)
    for p in P[::-1]:r=r*x+p
    return r
def j0(P):return sum(a/(1+i) for i,a in enumerate(P))
def lagrange(S,i):
    a=S[i];T=S[:i]+S[i+1:]
    return [q/prod(a-b for b in T)for q in hull(T)]
def solve(M,Y):
    n=len(Y)
    X=[[F(a)for a in r]+[F(b)]for r,b in zip(M,Y)]
    for i in range(n):
        j=next((j for j in range(i,n)if X[j][i]),None)
        if j is None:return
        X[i],X[j]=X[j],X[i]
        a=X[i][i];X[i]=[z/a for z in X[i]]
        for k in range(n):
            if k!=i and (a:=X[k][i]):X[k]=[y-a*z for y,z in zip(X[k],X[i])]
    return tuple(r[-1]for r in X)
def det(X):
    A=[list(map(F,r)) for r in X]
    D=F(1)
    for i in range(len(A)):
        j=next((j for j in range(i,len(A))if A[j][i]),None)
        if j is None:return F(0)
        if i!=j:A[i],A[j]=A[j],A[i];D=-D
        d=A[i][i];D*=d
        for k in range(i+1,len(A)):
            r=A[k][i]/d
            if r:
                for j in range(i+1,len(A)):
                    A[k][j]-=r*A[i][j]
    return D

def units(h):return tuple(sorted({sgn*F(2)**a*F(3)**b*F(5)**c*F(7)**d
  for sgn,a,b,c,d in product((-1,1), range(-h,h+1), range(-h,h+1), range(-1,2), range(-1,2))},key=lambda x: abs(x.numerator)*x.denominator))
def mesh(extra=False):
    for j in range(9):
        for k in range(j+1,10):
            yield tuple(F(i-j,k-j)for i in range(10))
def squares10(nodes,w):
    E=tuple(x for x in nodes if x!=1)
    C=tuple(lagrange(E,i)for i in range(9))
    return E,tuple((j0(c),pe(c,F(1)))for c in C)
def found():
    U=units(5)
    top=[]
    for xs in mesh():
        X,C=squares10(xs,1)
        for w in U:
            W=tuple(a-w*b for a,b in C)
            if 0 in W:continue
            UU=tuple(x for x,a in zip(X,W) if x and unit(a))
            if len(UU)>=3:
                top.append((len(UU),sum(abs(a.numerator).bit_length()+a.denominator.bit_length()for a in W),w,X,W,UU))
    top.sort(key=lambda z:(-z[0],z[1]))
    return top
if __name__=='__main__':
    f=found();print('count',len(f))
    from collections import Counter
    print(Counter(z[0]for z in f))
    for i,(k,h,w,X,W,UU)in enumerate(f[:40]):print(i,k,'w=',w,'X=',','.join(map(str,X)),'U=',','.join(map(str,UU)),'W=',','.join(map(str,W)))
