"""Exact checks of the Newton pin and third-row scalar obstructions."""
from fractions import Fraction as Q
from itertools import product

def mul(p,q):
    r=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):r[i+j]+=x*y
    return r

def sub(p,q):
    return [x-y for x,y in zip(p,q)]

def scaled(c,p):
    return [c*a for a in p]

def homogeneous(p,a,b):
    return sum(c*a**j*b**(len(p)-1-j) for j,c in enumerate(p))

def check():
    D=[3,-90,1125,-7560,28075,-51750,33750]
    B=[15,-432,5135,-32400,112245,-193200,118125]
    C=[10,-270,2943,-16440,49035,-72450,39375]
    m0,m1,m2,m3=([Q(1,j+4),Q(-9,j+3),Q(23,j+2),Q(-15,j+1)] for j in range(4))
    assert D==scaled(1800,sub(mul(m0,m2),mul(m1,m1)))
    assert scaled(2,B)==scaled(12600,sub(mul(m0,m3),mul(m1,m2)))
    assert C==scaled(12600,sub(mul(m1,m3),mul(m2,m2)))
    for a,b in product(range(4),repeat=2):
        if a%2==0 and b%2==0: continue
        d,h,c=(homogeneous(p,a,b) for p in (D,B,C))
        assert d%4 == (1 if a%2 and b%2 else 2 if a%2 else 3)
        assert (h*h-7*c*d)%4==3
    assert {(x*x)%4 for x in range(4)}=={0,1}
    assert all((y**3-9*y*y+18*y-6)%5 for y in range(5))
    print("Cramer identities, all 12 primitive residue pairs, and mod-5 cubic check pass")

if __name__=="__main__":
    check()
