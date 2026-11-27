"""Exact stdlib check of the finite integer reduction for the central repeat."""
from fractions import Fraction as F
from itertools import product
from math import gcd, prod

def chk_residues():
    for m,n in product(range(2),repeat=2):
        if m or n:
            assert (5*m*m+5*m*n+n*n)%2==1
            assert (3*m**3-3*m*n*n-n**3)%2==1
    for m,n in product(range(3),repeat=2):
        if m or n:
            assert (5*m*m+5*m*n+n*n)%3!=0
    for m,n in product(range(5),repeat=2):
        if m or n:
            assert (3*m**3-3*m*n*n-n**3)%5!=0

def enumerate_candidates():
    found = set()
    for p,q in product((1,-1,5,-5),(1,-1,3,-3)):
        bound = abs(-9*p**3+125*q*q) or abs(225*p*q)
        assert bound <= 3375
        for n in range(1,bound+1):
            if bound % n:continue
            U,V=3*(p-n*n),2*n**3+3*n*p+5*q
            if 5*V*V+5*n*U*V+(n*n-p)*U*U:continue
            if U:
                if V%U:continue
                ms = [V//U]
            else:
                if V:continue
                assert (p,n,q)==(1,1,-1)
                ms = [-1,0]
            for m in ms:
                if gcd(m,n)!=1:continue
                if (5*m*m+5*m*n+n*n, 3*m**3-3*m*n*n-n**3)==(p,q):
                    found.add(F(m,n))
    return found

def forced_weights(a):
    p=5*a*a+5*a+1
    q=3*a**3-3*a-1
    r=3*a*a-1
    u=(5*a*a-3)*q/(p*r)
    v=-p/(5*q)
    sites=[a,u,v,-a]
    assert len(set(sites))==4
    def w(x):
        other=[v for v in sites if x!=v]
        return (-sum(other)/3-prod(other))/prod(x-v for v in other)
    return w(a),w(u)

def main():
    chk_residues()
    # The integer bound comes from the constant term after extracting n.
    # These are all the algebraic candidates, before checking R or weights.
    got = enumerate_candidates()
    assert got=={F(0),F(-1),F(-3,4),F(-2,5),F(-1,2),F(-2,3),F(-1,3)}
    assert 3*(-3)**2-4**2==11 and 3*(-2)**2-5**2==-13
    assert forced_weights(F(-1,2))[1]==F(1,1404)
    assert forced_weights(F(-2,3))[0]==F(31,78)
    assert forced_weights(F(-1,3))[1]==F(1,1160)
    print("All seven central repeated-clock candidates excluded over Z[1/30].")
if __name__=="__main__":
    main()
