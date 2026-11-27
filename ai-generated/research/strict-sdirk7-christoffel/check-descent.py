#!/usr/bin/env python3
"""Finite certificates in the accompanying two-isogeny proof. Standard Python only."""
from itertools import combinations
from math import gcd, prod

def squarefree_divisors(ps):
    return {prod(t) for k in range(len(ps)+1) for t in combinations(ps,k)}

def signed_divisors(ps):
    return {s*d for s in [-1,1] for d in squarefree_divisors(ps)}

def basis_coset(d,b):
    g=gcd(abs(d),b)
    return d*b//(g*g)

def no_local(a,b,d,q):
    assert b%d==0
    squares={s*s%q for s in range(q)}
    return all((A+a*t*t+C*t**4)%q not in squares
               for A,C in [(d,b//d),(b//d,d)] for t in range(q))

def num_points(a,b,p):
    assert 16*b*b*(a*a-4*b)%p
    return 1+sum(y*y%p==x*(x*x+a*x+b)%p for x in range(p) for y in range(p))

def main():
    a,b=1350,23625
    A,B=-2*a,a*a-4*b
    assert (A,B)==(-2700,1728000)
    assert b==3**3*5**3*7==105*15**2
    assert B==2**9*3**3*5**3==30*240**2
    c1={-15:27,-5:16,-3:256,-1:16,3:16,5:256,15:16}
    c2={3:625,5:81,15:27}
    reps=set(c1)|{1}
    assert reps|{basis_coset(d,105) for d in reps}==signed_divisors([3,5,7])
    reps=set(c2)|{1}
    assert reps|{basis_coset(d,30) for d in reps}==squarefree_divisors([2,3,5])
    for aa,bb,table in [(a,b,c1),(A,B,c2)]:
        for d,q in table.items():
            assert no_local(aa,bb,d,q)
            print("both projective unit charts excluded",aa,bb,d,q)
    n1,n2=(num_points(a,b,p) for p in [11,17])
    assert (n1,n2)==(6,16) and gcd(n1,n2)==2
    assert n2%11 and n1%17
    print("good-reduction counts at 11 and 17:",n1,n2)

if __name__=="__main__":
    main()
