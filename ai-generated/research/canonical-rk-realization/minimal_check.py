#!/usr/bin/env python3
"""Exact stage minimization and finite-horizon quartic checks (stdlib only)."""
from fractions import Fraction as F
from math import prod


def quotient(A,b):
    """Rows are sparse dicts and ordered chronologically. Return canonical representative."""
    n=len(A);part=[0]*n
    def agg(row):
        d={}
        for j,v in row.items():d[part[j]]=d.get(part[j],0)+v
        return tuple(sorted((k,v) for k,v in d.items() if v))
    rounds=0
    while True:
        labels={};Q=[labels.setdefault((part[i],agg(row)),len(labels)) for i,row in enumerate(A)]
        if Q==part:break
        assert len(labels)>len(set(part));part=Q;rounds+=1
    r=len(set(part));reps=[part.index(k) for k in range(r)]
    B=[dict(agg(A[i])) for i in reps];w=[0]*r
    for i,x in enumerate(b):
        assert dict(agg(A[i]))==B[part[i]]
        w[part[i]]+=x
    stack=[i for i,x in enumerate(w) if x];keep=set(stack)
    while stack:
        for j in B[stack.pop()]:
            if j not in keep:keep.add(j);stack.append(j)
    remap={j:i for i,j in enumerate(sorted(keep))}
    return ([{remap[j]:x for j,x in B[i].items()} for i in sorted(keep)], [w[i] for i in sorted(keep)], r, rounds)


def Aop(A,x):return tuple(sum((v*x[j] for j,v in r.items()),F(0)) for r in A)
def dot(x,y):return sum((u*v for u,v in zip(x,y)),F(0))

def tree_data(N):
    ts=[()];ns=[1];gm=[1]
    for n in range(2,N+1):
        def get(lo,r):
            if r==0:yield ();return
            for i in range(lo,len(ns)):
                if ns[i]>r:break
                for tail in get(i,r-ns[i]):yield (i,)+tail
        for ch in list(get(0,n-1)):
            ts.append(ch);ns.append(n);gm.append(n*prod(gm[i] for i in ch))
    return ts,ns,gm

def output(A,b,ts):
    av=[];sc=[]
    vv=(F(1),)*len(A)
    for ch in ts:
        x=vv
        for j in ch:x=tuple(a*z for a,z in zip(x,av[j]))
        av.append(Aop(A,x));sc.append(dot(b,x))
    return sc

def demo():
    A=[{}, {0:F(1)}, {0:F(1)}, {0:F(2)}, {1:F(3),2:F(-2)}];b=[0,2,-2,0,1]
    Q,w,r,rounds=quotient(A,b)
    assert Q==[{}, {0:1}, {1:1}] and w==[0,0,1] and r==4
    td,_,_=tree_data(8);assert len(td)==200
    assert output(A,b,td)==output(Q,w,td)
    # All raw graph paths from the duplicate class now cancel after aggregation.
    A[-1]={0:F(3),1:F(1),2:F(-1)}
    Q,w,r,rounds=quotient(A,b)
    assert Q==[{}, {0:3}] and w==[0,1] and r==4
    assert output(A,b,td)==output(Q,w,td)
    print('Exact toy minimizations: 5 physical stages → 4 reachable classes → respectively 3 and 2 visible classes. All 200 rooted outputs through order 8 match the quotients.')


def poly(roots):
    coeff=[F(1)]
    for w in roots:
        q=[F(0)]*(len(coeff)+1)
        for j,u in enumerate(coeff):q[j]-=w*u;q[j+1]+=u
        coeff=q
    return coeff

def integ(f,x):return sum(a*x**(j+1)/(j+1) for j,a in enumerate(f))
def cardinal(X):return [[a/prod(x-u for u in X if x!=u) for a in poly([u for u in X if x!=u])] for x in X]


def core(p):
    L=p+2;roots=[F(0),F(1,8),F(1,4),F(3,8)];u=F(1,2);v=F(5,8)
    f=poly(roots);P=lambda x:prod(x-r for r in roots)
    c=roots+[u,v];A=[{}]+[{0:x} for x in c[1:]];b=[F(0)]*len(A)
    def row(row,x):
        assert sum(row.values(),F(0))==x and all(0<=j<len(A) for j in row)
        A.append({j:a for j,a in row.items() if a});c.append(x);b.append(F(0));return len(A)-1
    Xk=lambda k:[1+F(k*L+j,(p+1)*L) for j in range(1,L+1)]
    prev=[];X=Xk(0)
    for x in X:
        J=integ(f,x);a=J*(v-x)/((v-u)*P(u));d=J*(x-u)/((v-u)*P(v))
        assert a and d
        prev.append(row({0:x-a-d-3,1:F(1),2:F(1),3:F(1),4:a,5:d},x))
    for k in range(1,p):
        Y=Xk(k);lag=cardinal(X);bb=[[integ(h,y) for h in lag] for y in Y]
        # Direct exact transfer of every monomial available in the previous panel.
        mon=[[x**j for x in X] for j in range(L)]
        assert all(dot(r,mon[j])==y**(j+1)/(j+1) for r,y in zip(bb,Y) for j in range(L))
        assert all(any(r[i] for r in bb) for i in range(L))
        prev=[row(dict(zip(prev,r)),y) for r,y in zip(bb,Y)];X=Y
    lag=cardinal(X)
    outbase=[integ(h,F(1))-h[p]/(p+1) for h in lag]
    tau=next(t for t in range(L+1) if all(q+t*h[p+1] for q,h in zip(outbase,lag)))
    for j,q,h in zip(prev,outbase,lag):b[j]=q+tau*h[p+1]
    assert len(set(c))==len(c) and len(c)==6+p*L
    assert quotient(A,b)[:3]==(A,b,len(A))
    return A,b,c,P


def tp(A,c,P):
    a=Aop(A,[P(x) for x in c]);cpa=Aop(A,[x*P(x) for x in c]);aa=Aop(A,a)
    return tuple(x*j-v-w for x,j,v,w in zip(c,a,cpa,aa))


def pair(p,N,distinct,args):
    A,b,c,P=args;z=[F(j,8*(N+1)) for j in range(1,N+2)];k=len(A)
    weights=[1/prod(t-v for v in z if t!=v) for t in z]
    assert [dot(weights,[t**j for t in z]) for j in range(N+1)]==[F(0)]*N+[F(1)]
    y=[F(3,4)+(t if distinct else 0) for t in z];B=b+weights;C=c+y
    A0=A+[{0:x-t,1:t} for x,t in zip(y,z)];A1=A+[{0:x-2*t,1:t,4:t} for x,t in zip(y,z)]
    assert all(dot(B,[x**j for x in C])==F(1,j+1) for j in range(p)) and not dot(B,[x**p for x in C])
    r,u=c[1],c[4]
    for theta,Ac in enumerate((A0,A1)):
        assert Aop(Ac,(F(1),)*len(Ac))==tuple(C)
        vv=tp(Ac,C,P);assert vv==(F(0),)*k+tuple(theta*t*(x-u)*P(u) for x,t in zip(y,z))
        assert bool(dot([w*w for w in B],[v*v for v in vv]))==bool(theta)
        assert quotient(Ac,B)[:3]==(Ac,B,len(Ac))
        assert C[:4]==[F(0),F(1,8),F(1,4),F(3,8)]
    if p==8:
        ts,ns,gm=tree_data(10);assert len(ts)==1205
        f0=output(A0,B,ts);f1=output(A1,B,ts);assert f0==f1
        assert all(f*g==1 for f,n,g in zip(f0,ns,gm) if n<=p)
    # Exact higher-order rooted witness, not an assertion based on non-isomorphism.
    ac0=Aop(A0,C);ac1=Aop(A1,C)
    if distinct:
        assert len(set(C))==len(C)
        delta=dot(B,[(b-a)*x**(N-1) for b,a,x in zip(ac1,ac0,C)])
        assert delta==u
        H=N+1;witness='one order-2 branch and N−1 leaves, output change 1/2'
    else:
        delta=dot(B,[b**N-a**N for a,b in zip(ac0,ac1)])
        assert delta==(r+u)**N-r**N
        H=2*N;witness='N order-2 branches, output change (5/8)^N−(1/8)^N'
    print(f'p={p}, {len(A0)} stages, '+('all clocks distinct' if distinct else 'terminal clock repeated but its Ac witnesses distinct')+f'; both full-series minimal, fixed b,c, identical complete scalar data through order {H}. First different order {H+1}: {witness}. Actual quartic F0 loss 1 versus 0; unit sign-insensitive two-hole norm changes.'+(' All 1,205 rooted trees through order 10 checked directly.' if p==8 else ''))


if __name__=='__main__':
    demo()
    for p,N,D in ((8,5,9),(20,27,53)):
        A=core(p);pair(p,N,False,A);pair(p,D,True,A)
