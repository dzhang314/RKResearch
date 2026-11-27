"""Independent exact replay for the nine-stage factorial-localized ERK7.

This literal tableau and the proof in Lean have separate representations;
the replay is not a Lean axiom nor a source of its kernel certificates.
"""
from fractions import Fraction as F
from functools import cache
from math import lcm,prod

def row(s):
    return tuple(F(x) for x in s.split())

A = (
    row(''),
    row('1/6'),
    row('0 1/3'),
    row('1/8 0 3/8'),
    row('1/8 0 3/16 -1/16'),
    row('64 0 474 -88 -448'),
    row('151/972 0 13/27 -28/243 -320/1701 -1/6804'),
    row('23637/168070 0 114/343 -7492/84035 -52576/588245 -93/1176490 -729/84035'),
    row('1169/900 0 13/5 5204/675 -147136/1575 -13/18900 -2376/25 4802/27'),
)
b = row('7/40 0 0 328/135 -512/35 -1/7560 -729/40 16807/540 1/8')


@cache
def forests(n, lower=()):
    if n == 0:
        return ((),)
    return tuple((t,) + rest for k in range(1, n+1)
                 for t in trees(k) if lower <= t
                 for rest in forests(n-k, t))

@cache
def trees(n):
    return forests(n-1)

@cache
def order(t):
    return 1 + sum(map(order, t))

@cache
def factorial(t):
    return order(t) * prod(map(factorial, t))

@cache
def stage(t):
    return tuple(prod(sum(a*value for a,value in zip(r,stage(q))) for q in t)
                 for r in A)

def defect(t):
    return factorial(t) * sum(w*v for w,v in zip(b,stage(t))) - 1

def main():
    assert len(A)==len(b)==9 and all(len(r)==i for i,r in enumerate(A))
    D=lcm(*(x.denominator for r in (*A,b) for x in r))
    assert D==11435482800 and 5040**6 % D==0
    assert [sum(r) for r in A]==list(row("0 1/6 1/3 1/2 1/4 2 1/3 2/7 1"))
    count=0
    for n,want in enumerate([1,1,2,4,9,20,48],start=1):
        ts=trees(n)
        assert len(ts)==len(set(ts))==want
        assert all(order(t)==n and defect(t)==0 for t in ts)
        count+=len(ts)
    print(f"all {count} rooted order conditions verified")
    next_tree=((((),)*5,),)
    assert order(next_tree)==8 and factorial(next_tree)==336
    assert defect(next_tree)==F(1,12)
    print("the double unary graft of the six-vertex bush fails order eight by 1/12")
    print(f"common denominator {D} divides (7!)^6")

if __name__=="__main__":
    main()
