from sympy import Poly, symbols
from itertools import combinations
from functools import reduce
x=symbols('g')
def scan(p,v,w,a,b):
    P=lambda t: Poly(t,x,modulus=p)
    Z,O,X=P(0),P(1),P(x)
    def mul(a,b):
        c=[Z]*(len(a)+len(b)-1)
        for j,x in enumerate(a):
            for k,y in enumerate(b):c[j+k]+=x*y
        return c
    def moment(f,j):
        return sum((u*pow(i+j+1,-1,p)for i,u in enumerate(f)),Z)
    def hull(r):return reduce(mul,([(-r),O]for r in r),[O])
    def det(A):
        if len(A)<2:return A[0][0] if A else O
        return sum(((-1)**j*u*det([row[:j]+row[j+1:]for row in A[1:]])for j,u in enumerate(A[0])),Z)
    F=hull([O-X*v,O-X*w,X,a*X,b*X])
    M=[moment(F,j)for j in range(4)]
    fam=[M[i]*M[j+1]-M[j]*M[i+1]for i,j in combinations(range(3),2)]
    D=[]
    for k in [1,a,b]:
        rr=list([1,a,b]);rr.remove(k)
        for vv in [v,w]:
            if not (k+vv)%p:
                D.append(Z);continue
            gx=P(pow((k+vv)%p,-1,p))
            E=[moment(hull([O-v*gx,O-w*gx]+[r*gx for r in rr]),j)for j in range(5)]
            D.append(det([[E[i+j]for j in range(3)]for i in range(3)]))
    return fam,D
