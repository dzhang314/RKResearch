from sympy import Poly, symbols
from itertools import combinations
from functools import reduce
x=symbols('g')
def scan(p,v,w,s):
    P=lambda t: Poly(t,x,modulus=p)
    Z,O,X=P(0),P(1),P(x)
    def mul(a,b):
        c=[Z]*(len(a)+len(b)-1)
        for j,x in enumerate(a):
            for k,y in enumerate(b):c[j+k]+=x*y
        return c
    def moment(f,j):
        return sum((t*pow(i+j+1,-1,p)for i,t in enumerate(f)),Z)
    def hull(r):return reduce(mul,([(-r),O]for r in r),[O])
    def det(A):
        if len(A)<2:return A[0][0] if A else O
        return sum(((-1)**j*u*det([row[:j]+row[j+1:]for row in A[1:]])for j,u in enumerate(A[0])),Z)
    def aff(u,v):
        return [u[i]*v[j]-u[j]*v[i] for i,j in combinations(range(3),2)]
    def free(last):
        e=[moment(last,j)for j in range(4)]
        return aff(e[:3],e[1:])
    def two(H):
        e=[moment(H,j)for j in range(5)]
        return det([[e[i+j]for j in range(3)]for i in range(3)])
    d0=O-v*X;d1=O-w*X
    f0=hull([d0,d1,X,s*X])
    E=mul(f0,[Z,-4*X,O])
    F={}
    F['none'] = aff([moment(f0,j)for j in range(3)],[moment(E,j)for j in range(3)])
    F['terminal-repeat']=free(hull([d0,d1,X,s*X,(4-s)*X]))
    C={}
    for i,(p0,p1) in enumerate([(v,w),(w,v)]):
        D0,D1=O-p0*X,O-p1*X
        F[('one-Mid',i)]=free(hull([D0,D1,X,4*X-D0,s*X]))
        g=P(pow((1+p0)%p,-1,p))
        A,B=(O-p0*g,O-p1*g)
        R=hull([A,B,s*g])
        P2=[Z,-4*g,O]
        M=[mul(R,[Z]+P2),[Z]+R,[-x for x in mul(R,P2)],[-x for x in R]]
        A0=[tuple(moment(row,j)for row in M)for j in range(3)]
        coef=[(-1)**k*det([r[:k]+r[k+1:] for r in A0])for k in range(4)]
        C[('one-zero',i)]=coef[0]*coef[3]-coef[1]*coef[2]
        C[('two-zero-mid',i)]=two(hull([A,B,4*g-B,s*g]))
        for j,(kk,ll) in enumerate([(1,4-s),(4-s,1)]):
            if (kk+p0)%p:
                g=P(pow((kk+p0)%p,-1,p))
                C[('repeat-pinned',i,j)]=two(hull([O-p0*g,O-p1*g,ll*g,s*g]))
            else:
                C[('repeat-pinned',i,j)]=Z
    g=P(2*pow((4+v+w)%p,-1,p))
    C['two-mid']=two(hull([O-v*g,O-w*g,g,s*g]))
    return F,C
