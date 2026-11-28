#!/usr/bin/env python3
"""Independent small rational checks for the geometry-free late-zero reads."""
from fractions import Fraction as F
from verify import ad, hull, mul, scl, sub, trim


def qrem(a,b):
    a=trim(a)
    while len(a)>=len(b):
        k=len(a)-len(b)
        a=sub(a,[F(0)]*k+scl(b,a[-1]/b[-1]))
    return a


def integ(p):
    return sum(F(v,i+1) for i,v in enumerate(p))


def mom(p):
    assert not p[0]
    return sum(8*F(v,i) for i,v in enumerate(p[1:],1))-p[1]/2


def main():
    P=list(map(F,[3,-12,10]))
    N=[F(0),F(3,2),F(-4),F(5,2)]
    remainders=[(F(136,3),F(-640,9)),(F(64,3),F(-40)),
                (F(12),F(-80,3)),(F(8),F(-20)),(F(6),F(-16)),
                (F(24,5),F(-66,5))]
    Ms=[]
    for k,R in enumerate(remainders,1):
        lhs=mul(N,R)
        if k==1:lhs=[F(0)]+lhs
        target=([F(0)]*max(0,k-2))+[F(1)]
        assert not qrem(sub(lhs,target),P)
        Ms.append(-R[1]/10+(F(7,18) if k==1 else F(0)))
    assert Ms==[F(15,2),F(4),F(8,3),F(2),F(8,5),F(33,25)]
    print("fixed-pole affine remainders and six exact moment constants")
    assert integ([F(0)]+P)==0
    assert integ([F(0)]*2+P)==0
    assert integ([F(0)]*3+P)==F(1,60)
    assert integ([F(0)]*2+N)==-F(1,120)
    assert all(Ms[k]/8==F(1,k+1) for k in range(1,5))
    assert Ms[5]/8+F(1,600)==F(1,6)
    # The symbolic C-dependent cancellation in degree five is also
    # checked in the native scalar module.
    print("actual a-row remainder integrals and degree-six mode constants")
    x=F(2,5)
    wp=hull(F,[F(0),F(0),F(1),F(1),x])
    assert mom(wp)==0 and integ(wp)==F(1,300)
    assert F(54,625)*x==3*x**3*(x-1)**2/2
    print("genuine masked quintic zero mode and second-live late tap scale")


if __name__=="__main__":
    main()
