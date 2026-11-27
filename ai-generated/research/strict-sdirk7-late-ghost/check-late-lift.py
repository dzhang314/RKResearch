#!/usr/bin/env python3
"""Standard-library replay of the four-equation late-ghost Hensel lift."""
from functools import lru_cache
from itertools import permutations
from math import prod
from pathlib import Path
import json, argparse
P=19
C=(1,0,7,6,9,3)

def hull(xs):
    Z=[1]
    for x in xs:
        Z=[-x*Z[0]]+[Z[i-1]-x*Z[i] for i in range(1,len(Z))]+[Z[-1]]
    return Z

def det(A):
    n=len(A)
    return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))*
               prod(A[i][j] for i,j in enumerate(p))
               for p in permutations(range(n)))

def setup(T,m):
    z,u,a,b,c,t=T
    div=lambda a,b:a*pow(b%m,-1,m)%m
    M=u*u-4*u+2
    theta=div(1,M)
    E=lambda x:div(4+(4*theta-1)*(x-1),3)
    h=div(4-5*M,4-M)
    assert E(h)==0
    v=4-u
    ys=[a,b,c,v,u,1]
    I=lambda f:sum(div(k*z**j,j+1) for j,k in enumerate(f))%m
    Ks=[I(hull(ys[:i]+ys[i+1:])) for i in range(6)]
    ss=[div(1,prod(y-q for j,q in enumerate(ys) if i!=j)) for i,y in enumerate(ys)]
    bs=[s*k%m for s,k in zip(ss,Ks)]
    wu=(u-h)*div(M,2)*Ks[-2]
    w1=-(1-h)*div(Ks[-1],2)
    W=lambda y:div((u-y)*w1+(y-1)*wu,u-1)
    D=[div(si*W(y),y-h) for si,y in zip(ss,ys)]
    d0=div(W(h),prod(h-y for y in ys))
    vv=[div(W(y),k) for y,k in zip(ys,Ks)]
    v0=div(-sum(d*w for d,w in zip(D,vv)),d0)
    x=z-a; y=z-b
    q=lambda a:((2-t)*a+t-1)%m
    qh=lambda a:((a-1)*(a-1-t))%m
    Jq=lambda a:(div((2-t)*a*a,2)+(t-1)*a)%m
    Jh=lambda a:(div(a**3,3)-div((2+t)*a*a,2)+(1+t)*a)%m
    fg=lambda a:(Jq(a)-q(a))%m
    fh=lambda a:(Jh(a)-qh(a))%m
    ratio=div(vv[1],vv[0])
    e0=I(hull(ys))
    e1=(W(v)-(v-h)*div(M,2)*Ks[3])%m
    e2=sum(b*w*w for b,w in zip(bs,vv))%m
    e3=(qh(x)*(fg(y)-ratio*fg(x))-q(x)*(fh(y)-ratio*fh(x)))%m
    eb=lambda seq:seq[:3]+[0]+seq[3:]
    Y=ys[:3]+[h]+ys[3:]
    B=eb(bs)
    F=D[:3]+[d0]+D[3:]
    V=vv[:3]+[v0]+vv[3:]
    R=[B,[b*y for b,y in zip(B,Y)],[b*y*y for b,y in zip(B,Y)],F]
    pivots=dict(theta=theta,h=h,den=4-M,d0=d0,v0=v0,va=vv[0],vb=vv[1],Qa=q(x),
        qdet=q(x)*qh(y)-q(y)*qh(x),suffix=det([r[3:] for r in R]),t=t,z=z)
    return (e0,e1,e2,e3),{k:v%m for k,v in pivots.items()},(Y,B,F,V,R,q,qh,Jq,Jh,theta,x,y,vv,t,h,Ks,bs)

def jac():
    f,data,_=setup(C,P);assert f==(0,0,0,0)
    M=P*P
    a=setup(C,M)[0]
    J=[[0]*6 for _ in range(4)]
    for k in range(6):
        x=list(C); x[k]+=P
        f=setup(x,M)[0]
        for j in range(4):
            assert (f[j]-a[j])%P==0
            J[j][k]=(f[j]-a[j])//P%P
    return J,data

def gauss(A,m):
    A=[[(v%m) for v in row] for row in A]
    for j in range(len(A)):
        i=next(i for i in range(j,len(A)) if A[i][j]%P)
        A[j],A[i]=A[i],A[j]
        k=pow(A[j][j],-1,m)
        A[j]=[v*k%m for v in A[j]]
        for i,row in enumerate(A):
            if i!=j:
                scale=row[j]
                A[i]=[(v-scale*w)%m for v,w in zip(row,A[j])]
    return [row[-1] for row in A]


def lift(z,u,N):
    assert z%P==1 and u%P==0 and N>=1
    J,bp=jac()
    assert J==[[0,1,9,11,11,0],[16,13,8,11,14,0],
               [6,6,13,2,8,0],[15,7,7,5,9,8]]
    assert bp==dict(theta=10,h=16,den=2,d0=2,v0=2,va=17,vb=0,Qa=8,qdet=18,suffix=6,t=3,z=1)
    J=[r[2:] for r in J]
    assert det(J)%P==13
    X=[z,u,*C[2:]]
    m=P
    for _ in range(1,N):
        residual=setup(X,m*P)[0]
        assert all(e%m==0 for e in residual)
        digits=gauss([row+[-e//m] for row,e in zip(J,residual)],P)
        X[2:]=[a+m*d for a,d in zip(X[2:],digits)]
        m*=P
    return X,m


def build(T,m):
    checks,pivots,data=setup(T,m)
    assert checks==(0,0,0,0)
    Y,b,D,V,R,q,qh,Jq,Jh,theta,xa,xb,vv,t,h,K,Bout=data
    z,u,a,b0,c,t=T
    div=lambda a,b:a*pow(b%m,-1,m)%m
    f=lambda y:div(-4+(2*theta-2)*(y-1),3)
    rho=lambda y:1+theta*(1-y)
    x=[(z-y)%m for y in Y]
    qg=[q(a) for a in x]; qH=[qh(a) for a in x]
    lam=div(Jq(x[0])-qg[0],V[0])
    mu=div(qH[0]-Jh(x[0]),V[0])
    fwd=[[ (Jq(a)-lam*w)%m for a,w in zip(x,V)],
         [ (Jh(a)+mu*w)%m for a,w in zip(x,V)]]
    B=[[int(i==j) for j in range(7)] for i in range(7)]
    B[1][0]=div(fwd[0][1]-qg[1],qg[0])
    B[2][0],B[2][1]=gauss([[qg[0],qg[1],fwd[0][2]-qg[2]],
                           [qH[0],qH[1],fwd[1][2]-qH[2]]],m)
    targets=[[w*y%m for w,y in zip(b,Y)],
             [(div(w*y*y,2)-d)%m for w,y,d in zip(b,Y,D)],
             [(div(w*y**3,3)+f(y)*d)%m for w,y,d in zip(b,Y,D)],
             [rho(y)*d%m for y,d in zip(Y,D)]]
    for j in range(6):
        unknown=list(range(max(j+1,3),7))
        pre=range(j+1,max(3,j+1))
        eqs=[[r[k] for k in unknown]+[rhs[j]-r[j]-sum(r[k]*B[k][j] for k in pre)]
             for r,rhs in zip(R,targets)][:len(unknown)]
        for k,w in zip(unknown,gauss(eqs,m)):
            B[k][j]=w
    dot=lambda a,b:sum(v*w for v,w in zip(a,b))%m
    assert all(dot(row,[B[i][j] for i in range(7)])==tar[j]
               for row,tar in zip(R,targets) for j in range(7))
    assert all(dot(row,qg)==a and dot(row,qH)==b for row,a,b in zip(B,*fwd))
    A=[[1]+[0]*8,[t%m,1]+[0]*7]
    for xx,row in zip(x,B):
        h0=xx-sum(row)
        h1=div(xx*xx,2)-dot(row,x)
        feed1=div(h1-h0,t)
        A.append([(h0-feed1)%m,feed1]+row)
    return [[div(q,z) for q in row] for row in A], [0,0]+b


@lru_cache(None)
def size(t):return 1+sum(map(size,t))
@lru_cache(None)
def density(t):return size(t)*prod(map(density,t))
@lru_cache(None)
def trees(n):
    if n==1:return ((),)
    pool=tuple(t for k in range(1,n) for t in trees(k))
    def pick(start,left):
        if not left:yield ()
        for j in range(start,len(pool)):
            T=pool[j]
            d=left-size(T)
            if d<0:break
            for r in pick(j,d):yield (T,)+r
    return tuple(pick(0,n-1))


def verify(A,b,m):
    @lru_cache(None)
    def stage(T):
        return tuple(prod(sum(v*w for v,w in zip(row,stage(U))) for U in T)%m for row in A)
    res=lambda T:(density(T)*sum(w*v for w,v in zip(b,stage(T)))-1)%m
    checks=[T for k in range(1,8) for T in trees(k)]
    assert len(set(checks))==85 and all(res(T)==0 for T in checks)
    return res(tuple(() for _ in range(7)))

def check_affine_receipt():
    z,u,a,b,c,t=X=[10,0,9,8,12,3]
    F,piv,_=setup(X,P)
    assert F==(0,0,0,0) and piv['Qa']==1 and piv['qdet']==17 and piv['suffix']==8
    def moment(D,k=0):
        return sum(v*pow(z,j+k,P)*pow(j+k+1,-1,P) for j,v in enumerate(D))%P
    def eq(s,p):
        L=[-a*p,p+a*s,-s-a,1]
        I=[moment(L,j) for j in range(4)]
        return I[3]-5*I[2]+4*I[1],6*I[0]-14*I[1]+4*I[2]
    q=eq(0,0); r=eq(1,0); a1=eq(0,1)
    AJ=[[(r[k]-q[k])%P,(a1[k]-q[k])%P] for k in range(2)]
    assert AJ==[[11,4],[9,9]] and det(AJ)%P==6
    ratio=piv["vb"]*pow(piv["va"],-1,P)%P
    xb=z-b
    assert (xb*xb*pow(2,-1,P)-2*xb+1+ratio*pow(2,-1,P))%P==17
    m=P*P; D=setup(X,m)[0]
    cols=[]
    for j in (0,3,4,5):
        Y=X.copy(); Y[j]+=P
        if j==0: Y[2]+=P   # a=z-1 is held fixed as a relation
        F=setup(Y,m)[0]
        assert all((a-b)%P==0 for a,b in zip(F,D))
        cols.append([(a-b)//P%P for a,b in zip(F,D)])
    assert det(cols)%P==5

def check_literals():
    for label,ref in [('reflection',1),('arithmetic',1),('affine',6)]:
        d=json.loads(Path(__file__).with_name(f'f19-{label}-late.json').read_text())
        A,b=d['tableau'],d['b']; z=d['z']; gamma=pow(z,-1,P)
        assert verify(A,b,P)==ref
        assert all(row[i]==gamma and not any(row[i+1:]) for i,row in enumerate(A))
        assert [i+1 for i,t in enumerate(b) if not t]==[1,2,6]
        if label=='reflection':
            assert build(C,P)==(A,b)
        if label=='arithmetic':
            assert d['v']==(2*d['u']-1)%P and d['v']!=(4-d['u'])%P
        if label=='affine':
            assert (z-d['a'])%P==1
            assert build([10,0,9,8,12,3],P)==(A,b)

if __name__=='__main__':
    cli=argparse.ArgumentParser()
    cli.add_argument('--power',type=int,default=8)
    cli.add_argument('--z',type=int,default=1)
    cli.add_argument('--u',type=int,default=0)
    args=cli.parse_args()
    check_literals()
    check_affine_receipt()
    X,m=lift(args.z,args.u,args.power)
    A,b=build(X,m)
    e=verify(A,b,m)
    assert e%P==1
    print(dict(modulus=m,coordinates=X,all_85=True,eighth_bush=e))
