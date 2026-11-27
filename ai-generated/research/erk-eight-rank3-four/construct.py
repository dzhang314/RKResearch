#!/usr/bin/env python3
"""Exact rational ERK construction from a six-site order-eight quadrature."""
from fractions import Fraction as F
from functools import cache
from itertools import permutations
from collections import Counter
from math import prod
import json

qnodes=list(map(F,['0','-7/11','477/1796','1821/2639','41/35','1']))
qweights=list(map(F,[
    '622019131/7478792370', '-385592652577/3610108142645760',
    '7534498301755137329152/19263219522329061475515',
    '18191966663727249336671/43974089940447542430720',
    '-6584930078125/743123802553344', '845736233/6991544160',
]))
assert all(sum(w*x**k for x,w in zip(qnodes,qweights))==F(1,k+1) for k in range(8))

def solve(M,rhs):
    N=len(rhs)
    M=[list(map(F,row))+[F(z)] for row,z in zip(M,rhs)]
    for j in range(N):
        k=next(k for k in range(j,N) if M[k][j])
        M[k],M[j]=M[j],M[k]
        v=M[j][j]
        M[j]=[u/v for u in M[j]]
        for k in range(N):
            if k!=j and M[k][j]:
                v=M[k][j]
                M[k]=[x-v*y for x,y in zip(M[k],M[j])]
    return [a[-1] for a in M]

def poly_mul(a,b):
    res=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            res[i+j]+=x*y
    return res

def poly_val(p,z):
    return sum(a*z**k for k,a in enumerate(p))

def lagrange(C,j):
    p=[F(1)]
    for k in range(len(C)):
        if k!=j:
            den=C[j]-C[k]
            p=poly_mul(p,[-C[k]/den,1/den])
    return p

def construction(nodes,weights,dup=1,a=F(1,4)):
    '''nodes, weights are in original endpoint-one units, clock order 0,h,g,u,v,1.'''
    assert nodes[0]==0 and nodes[-1]==1 and len(set(nodes))==6
    w0,wh,wg,wu,wv,ws=weights
    T=nodes[1]
    _,h,g,u,v,s=[c/T for c in nodes]
    assert h==1
    pure=[F(0), h, g, u, v]
    yu,yv=s-u,s-v
    R=(wu*yu**2)/(wv*yv**2)*(1-2*(v-u)/yv)
    LU,LV=[lagrange(pure,j) for j in (3,4)]
    pol=[b-R*d for b,d in zip(LU,LV)]
    p=poly_val(pol,F(1,2))
    ff=[z-16*p*k for z,k in zip(pol,[0,0,1,-2,1])]
    assert all(poly_val(ff,z)==0 for z in (F(0),F(1,2),F(1)))
    if not ff[4]:
        return 'degree'
    x=-ff[3]/ff[4]-F(3,2)
    if x in [F(0),F(1,2),F(1)]:
        return 'collision'
    assert poly_val(ff,x)==0
    y=[F(0),a,F(1,2),h,h,x,g,u,v,pure[dup],s]
    f3=1/(8*a)
    f4=-1/(2*a)
    f6=x*x*(1-x)/a
    f=[F(0),F(0),f3,f4,F(0),f6,F(0),F(0),F(0),F(0),F(0)]
    A=[[F(0)]*11 for _ in range(11)]
    A[1][0]=a
    A[2][:2]=[F(1,2)-f3,f3]
    A[3][:3]=[-1-f4,f4,F(2)]
    A[4][:4]=[F(1,6),F(0),F(2,3),F(1,6)]
    m1=x*x/2-a*f6
    m2=x**3/3-a*f6/3
    a63=4*(m1-m2)
    atot=m1-a63/2
    a64=((F(1,2)-x)*f6-a63*f3)/f4
    A[5][1:5]=[f6,a63,a64,atot-a64]
    A[5][0]=x-sum(A[5])
    Q=[0,4,6,7,8]
    delta=[F(0)]*11
    delta[2]=8*(1-x)
    delta[3]=1-2*x
    delta[5]=-1/(2*x*x*(1-x))
    for k,col in enumerate(Q):
        L=lagrange(pure,k)
        delta[col]=-sum(delta[j]*poly_val(L,y[j]) for j in (2,3,5))
    assert all(sum(d*c**k for d,c in zip(delta,y))==0 for k in range(5))
    assert sum(d*v for d,v in zip(delta,f))==0
    assert sum(d*v*c for d,v,c in zip(delta,f,y))==0
    if not delta[8]:
        return 'zero_delta_v'
    assert delta[7]==R*delta[8]
    b=[w0,F(0),F(0),F(0),wh,F(0),wg,wu,wv,F(0),ws]
    earlier=Q[dup]
    b[9]=b[earlier]/2 if b[earlier] else F(1)
    b[earlier]-=b[9]
    eta=s-y[9]
    scale=wv*yv*yv/(2*b[9]*eta*delta[8])
    delta=[scale*q for q in delta]
    l1=-b[9]*eta
    l2=F(2,3)*yv*l1
    yg=s-g
    A[7][6],A[8][6]=solve(
        [[wu*yu,wv*yv],[wu*yu**2,wv*yv**2]],
        [wg*yg**2/2+l1*delta[6],wg*yg**3/3+l2*delta[6]])
    A[8][7]=(wu*yu**2/2+l1*delta[7])/(wv*yv)
    unknown=[0,2,3,4,5]
    M=[[y[j]**k for j in unknown] for k in range(4)]+[[f[j] for j in unknown]]
    for i in (6,7,8):
        rhs=[y[i]**(k+1)/(k+1)-sum(A[i][j]*y[j]**k for j in (6,7)) for k in range(4)]+[F(0)]
        for j,z in zip(unknown,solve(M,rhs)):
            A[i][j]=z
    A[9]=[a+d for a,d in zip(A[earlier],delta)]
    A[10]=[(b[k]*(s-y[k])-sum(b[i]*A[i][k] for i in range(10)))/b[10] if k<10 else F(0) for k in range(11)]
    assert [sum(row) for row in A]==y
    assert all(A[i][j]==0 for i in range(11) for j in range(i,11))
    return ([[c/s for c in row] for row in A],b,x,[c/s for c in y],delta)

@cache
def trees(n):
    if n==1:
        return [()]
    prev=[(k,t) for k in range(1,n) for t in trees(k)]
    def visit(rem,low):
        if rem==0:
            yield ()
        for j in range(low,len(prev)):
            size,tr=prev[j]
            if size>rem:
                break
            for tail in visit(rem-size,j):
                yield (tr,)+tail
    return list(visit(n-1,0))

@cache
def size(t):
    return 1+sum(size(u) for u in t)

@cache
def fact(t):
    return size(t)*prod(fact(u) for u in t)

def audit(A,b):
    N=len(b)
    @cache
    def profile(t):
        up=[profile(u) for u in t]
        return tuple(prod(sum(A[i][j]*p[j] for j in range(i)) for p in up) for i in range(N))
    failed=[]
    for k in range(1,9):
        for t in trees(k):
            truth=F(1,fact(t))
            found=sum(bi*pi for bi,pi in zip(b,profile(t)))
            if found!=truth:
                failed.append((t,found,truth))
    assert [len(trees(k)) for k in range(1,9)]==[1,1,2,4,9,20,48,115]
    bush9=((),)*8
    defect=fact(bush9)*sum(bi*pi for bi,pi in zip(b,profile(bush9)))-1
    return failed,defect

def find():
    stats=Counter(); goods=[]
    for perm in permutations(range(1,5)):
        idx=[0,*perm,5]
        for dup in range(5):
            res=construction([qnodes[j] for j in idx],[qweights[j] for j in idx],dup)
            if isinstance(res,str):
                stats[res]+=1
                continue
            A,b,x,c,delta=res
            fail,defect=audit(A,b)
            stats['pass' if not fail and defect else f'fail{len(fail)}']+=1
            if fail and stats[f'fail{len(fail)}']<2:
                print('failure',idx,dup,x,'first failure',fail[0])
            elif not fail and defect:
                size=prod(1 for _ in ()) + sum(len(str(z)) for i in range(11) for z in A[i][:i])+sum(len(str(z)) for z in b)
                goods.append((size,idx,dup,A,b,x,c,defect))
    print(stats)
    return min(goods) if goods else None

if __name__=='__main__':
    good=find()
    if good:
        size,idx,dup,A,b,x,c,defect=good
        print('success',size,idx,dup,x,c,defect)
        print('max numerator digits', max(len(str(x.numerator)) for row in A for x in row))
        print('max denominator digits',max(len(str(x.denominator)) for row in A for x in row))
        with open('tableau.json','w') as out:
            json.dump({'input_site_indices':idx,'duplicate_of_pure_prefix_index':dup,
                'A':[[str(z) for z in row[:i]] for i,row in enumerate(A)],'b':list(map(str,b)),
                'c':list(map(str,c)),'x_in_normalized_head_units':str(x),
                'bush9_normalized_defect':str(defect)},out,indent=2)
            out.write('\n')
