#!/usr/bin/env python3
"""Exact modular replays of the repeated-live reverse chronology gates."""
from itertools import permutations
P=1013
D=(-42,840,-5040,12600,-13860,5544)
INNER=(347,468,507,546,667)
LIVE=(*INNER,1)


def val(f,z):
    r=0
    for x in reversed(f):
        r=(r*z+x)%P
    return r


def main():
    assert all(P%k for k in range(2,32)) and D[-1]%P!=0
    assert tuple(z for z in range(P) if val(D,z)==0)==INNER
    n=m=t=0
    for a,x,y,z in permutations(LIVE,4):
        s1=x+y+z; s2=x*y+x*z+y*z; s3=x*y*z
        assert (12*a**3-15*s1*a*a+20*s2*a-30*s3)%P
        n+=1
        if a!=1:
            assert (2*a**3-3*s1*a*a+5*s2*a-10*s3)%P
            m+=1
    for z,a,b in permutations(LIVE,3):
        assert (5*z*z-(3*a+4*b)*z+2*a*b)%P
        t+=1
    assert (n,m,t)==(360,300,120)
    print("mod 1013: 360 unanchored, 300 interior anchored, 120 derivative gates nonzero")


if __name__=="__main__":
    main()
