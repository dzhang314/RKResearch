#!/usr/bin/env python3
"""Lift the exact cubic-dirty F19 tableau chart to arbitrary powers of 19.

All denominators arise from explicit 19-adic-unit tests. For proof of the
arbitrary-precision construction, see the five-equation local argument in
the README. Standard-library arithmetic only.
"""
from math import prod
from functools import lru_cache
from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path
import argparse
import json

pa = Path(__file__).with_name("check-dirty-chart.py")
spec = spec_from_file_location("dirty_chart", pa)
tree_library = module_from_spec(spec)
spec.loader.exec_module(tree_library)
trees, density = tree_library.trees, tree_library.density
P = 19
BASE = [8,9,15,7,5]


def hull(xs):
    z = [1]
    for t in xs:
        z = [-t*z[0]] + [z[j-1]-t*z[j] for j in range(1,len(z))] + [z[-1]]
    return z


def gaussian(rows, m):
    """Unique solution of a unit-pivot square system over Z/19^k."""
    rows=[[a%m for a in r] for r in rows]
    n=len(rows)
    for j in range(n):
        i=next(i for i in range(j,n) if rows[i][j]%P)
        rows[i],rows[j]=rows[j],rows[i]
        r=[a*pow(rows[j][j],-1,m)%m for a in rows[j]]
        rows[j]=r
        for k in range(n):
            if k!=j:
                rows[k]=[(a-rows[k][j]*b)%m for a,b in zip(rows[k],r)]
    return [r[-1] for r in rows]


def setup(x,m):
    z,a,b,c,h=x
    y=[a,b,c,4,0,1]
    inv=lambda x:pow(x%m,-1,m)
    div=lambda a,b:a*inv(b)%m
    Q=lambda w:sum(div(k*z**i,i+1) for i,k in enumerate(w))%m
    K=[Q(hull(y[:i]+y[i+1:])) for i in range(6)]
    s=[inv(prod(t-w for j,w in enumerate(y) if j!=i)) for i,t in enumerate(y)]
    b=[x*y%m for x,y in zip(K,s)]
    W0=-h*K[4]%m
    W1=-div((1-h)*K[5],2)%m
    D=[div(sj*(W0+(W1-W0)*yj),yj-h) for sj,yj in zip(s,y)]
    d3=-sum(D)%m
    v=[div((yj-h)*dj,bj) for yj,dj,bj in zip(y,D,b)]
    v3=div(-sum(dj*vj for dj,vj in zip(D,v)),d3)
    w=(z-h)%m
    t=inv(2)
    x2=(1+t)%m
    g2=(1+2*t-t*t)%m
    eta=div((x2-w)*x2-g2*(1-w),x2-w-g2*(1-w))
    q=lambda x:(x-w)*(x-eta)%m
    Jq=lambda x:(div(x**3,3)-div((w+eta)*x*x,2)+w*eta*x)%m
    f0=Q(hull(y))
    f1=(W0+(W1-W0)*4-(4-h)*K[3])%m
    f2=(2*(c+3)*div(D[2],b[2])+c**3-9*c*c+18*c-6)%m
    f3=sum(bj*vj*vj for bj,vj in zip(b,v))%m
    f4=(q(z-a)-Jq(z-a)+div(Jq(w)*v[0],v3))%m
    return (f0,f1,f2,f3,f4), (z,y,b,h,D,d3,v,v3,w,t,x2,g2,q,Jq)


def jacobian():
    m=P*P
    a=setup(BASE,m)[0]
    rows=[[0]*5 for _ in range(5)]
    for j in range(5):
        x=BASE.copy()
        x[j]+=P
        b=setup(x,m)[0]
        for i in range(5):
            assert (b[i]-a[i])%P==0
            rows[i][j]=(b[i]-a[i])//P%P
    return rows


def lift(exp):
    J=jacobian()
    x=BASE.copy()
    M=P
    for i in range(1,exp):
        a=setup(x,M*P)[0]
        assert all(y%M==0 for y in a)
        digit=gaussian([r+[-v//M] for r,v in zip(J,a)],P)
        x=[a+M*b for a,b in zip(x,digit)]
        M*=P
    assert setup(x,M)[0]==(0,)*5
    return x,M


def tableau(x,m):
    checks,data=setup(x,m)
    assert checks==(0,)*5
    z,y,b,h,D,d3,v,v3,w,t,x2,g2,q,Jq=data
    div=lambda a,b:a*pow(b%m,-1,m)%m
    cc=[(z-a)%m for a in y]
    R=[b,[a*t%m for a,t in zip(b,y)],[a*t*t%m for a,t in zip(b,y)],D]
    rho=lambda y:(1+div(1-y,2))%m
    f=lambda y:(-div(4,3)-div(y-1,3))%m
    target=[[(b[j]*y[j])%m for j in range(6)],
            [(div(b[j]*y[j]**2,2)-D[j])%m for j in range(6)],
            [(div(b[j]*y[j]**3,3)+f(y[j])*D[j])%m for j in range(6)],
            [D[j]*rho(y[j])%m for j in range(6)]]
    B=[[int(i==j) for j in range(6)] for i in range(6)]
    W=[(Jq(c)-div(Jq(w)*vj,v3))%m for c,vj in zip(cc,v)]
    B[1][0]=div(W[1]-q(cc[1]),q(cc[0]))
    for j in range(5):
        ks=list(range(max(2,j+1),6)) if j<2 else list(range(j+1,6))
        rows=[[R[i][k] for k in ks]+[(target[i][j]-R[i][j]-
            (R[i][1]*B[1][0] if j==0 else 0))%m] for i in range(len(ks))]
        taps=gaussian(rows,m)
        for k,tap in zip(ks,taps):
            B[k][j]=tap
    # Independent exact check of all 24 reverse constraints and six forward constraints.
    assert all(sum(R[i][k]*B[k][j] for k in range(6))%m==target[i][j]
        for i in range(4) for j in range(6))
    assert all(sum(B[i][j]*q(cc[j]) for j in range(6))%m==W[i] for i in range(6))
    a=[[0]*9 for _ in range(9)]
    a[0][0]=1
    a[1][:2]=[t,1]
    g=[1,g2,0]
    k=div(w*w-4*w+2,2*t)
    a[2][:3]=[(w-1-k)%m,k,1]
    H=[1,x2,w]
    vv=(a[2][0]+k*g2)%m
    for i in range(6):
        c=cc[i]
        rest=[(c-sum(B[i]))%m,(div(c*c,2)-sum(row*q for row,q in zip(B[i],cc)))%m,div(vv*v[i],v3)]
        M=gaussian([[1,1,1,rest[0]],H+[rest[1]],g+[rest[2]]],m)
        a[i+3][:]=M+B[i]
    return [[div(x,z) for x in row] for row in a], [0,0,0]+b


def verify(A,b,m):
    @lru_cache(None)
    def stage(T):
        return tuple(prod(sum(A[i][j]*stage(U)[j] for j in range(9)) for U in T)%m
                     for i in range(9))
    residual=lambda T:(density(T)*sum(a*w for a,w in zip(b,stage(T)))-1)%m
    ordered=[T for n in range(1,8) for T in trees(n)]
    assert len(ordered)==85
    assert all(residual(T)==0 for T in ordered)
    bush=tuple(() for _ in range(7))
    assert residual(bush)%P==5
    return residual(bush)


if __name__=='__main__':
    arg=argparse.ArgumentParser()
    arg.add_argument('--power',type=int,default=5)
    arg.add_argument('--output')
    args=arg.parse_args()
    assert args.power>=1
    x,m=lift(args.power)
    A,b=tableau(x,m)
    v=verify(A,b,m)
    record=dict(modulus=m,power=args.power,center=x,jacobian=jacobian(),tableau=A,b=b,order8_bush_residual=v)
    report=json.dumps(record,indent=2)
    print(report)
    if args.output:
        Path(args.output).write_text(report+'\n')
