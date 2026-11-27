#!/usr/bin/env python3
"""Independent finite-quotient replay; unit checked over all field extensions."""

from sympy import GF
from sympy.polys.rings import ring
import sys
gp=[-2430,28512,-140670,376686,-587973,530922,-253204,46200,2016]
pp=[709443967905,-6582222614817,24916972066389,-48858014778303,51867299523606,-27886169534188,5605993175160,240326547552]
Pden=7990348842
def gu(p):
    R,X,Y=ring('a,b',GF(p))
    D=R.domain
    t=lambda a:D.convert(a)
    d=lambda a,b:t(a)/t(b)
    calc=lambda cs,z:sum(t(c)*z**i for i,c in enumerate(cs))
    gx=calc(gp,X);gy=calc(gp,Y)
    dp=calc(pp,X)*d(1,Pden)
    dq=calc(pp,Y)*d(1,Pden)
    uf=6*dp-X*X; ur=6*dq-Y*Y
    def mul(ca,cb):
        acc=[R.zero]*(len(ca)+len(cb)-1)
        for i,a in enumerate(ca):
            for j,b in enumerate(cb):
                acc[i+j]=acc[i+j]+a*b
        return [v.rem([gx,gy]) for v in acc]
    f=mul([dp,-X,1],[-dp*X,uf])
    ar=mul([1-Y+dq,Y-2,1],[ur-dq*Y,-ur])
    poly=mul(f,ar)
    def M(h):
        ans=sum(a*d(1,h+i+1) for i,a in enumerate(poly))
        ans=(ans-sum(poly)*d(1,30)-(poly[0]*d(1,30) if h==0 else 0)).rem([gx,gy])
        return ans
    moms=[M(h) for h in range(4)]
    ms=[(moms[i]*moms[i+2]-moms[i+1]**2).rem([gx,gy]) for i in range(2)]
    ms.append((moms[0]*moms[3]-moms[1]*moms[2]).rem([gx,gy]))
    def amat(e):
        cols=[(e*X**i*Y**j).rem([gx,gy]) for i in range(8) for j in range(8)]
        return [[int(z.get((i,j),D.zero)) for z in cols] for i in range(8) for j in range(8)]
    def inverse(e):
        A=amat(e)
        b=[1]+[0]*63
        for i in range(64):
            piv=next((j for j in range(i,64) if A[j][i]),None)
            if piv is None:
                return None
            A[i],A[piv]=A[piv],A[i]
            b[i],b[piv]=b[piv],b[i]
            inv=pow(A[i][i],-1,p)
            A[i]=[(v*inv)%p for v in A[i]]
            b[i]=b[i]*inv%p
            for j in range(64):
                if j!=i and A[j][i]:
                    m=A[j][i]
                    A[j]=[(x-m*y)%p for x,y in zip(A[j],A[i])]
                    b[j]=(b[j]-m*b[i])%p
        H=sum(b[8*i+j]*X**i*Y**j for i in range(8) for j in range(8))
        assert (e*H).rem([gx,gy])==R.one
        return b
    inv = inverse(ms[0])
    assert inv is not None
    print(f"mod {p}: J0 J2 - J1² is a unit in the 64-dimensional octic tensor quotient")
    return inv

if __name__ == "__main__":
    for p in map(int,sys.argv[1:]) if len(sys.argv)>1 else (419,719):
        gu(p)
