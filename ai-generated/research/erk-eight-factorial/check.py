"""Independent exact replay for the twelve-stage factorial-localized ERK8.

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
    row('2/27'),
    row('1/36 1/12'),
    row('1/24 0 1/8'),
    row('296/1029 0 -352/343 384/343'),
    row('11/196 0 0 32/147 1/84'),
    row('19/512 0 0 41/120 539/1536 -147/640'),
    row('-1157/32 0 0 1858/15 5243/96 -5733/40 0'),
    row('-607/4 0 0 7456/15 -1715/12 -15778/45 448/3 8/9'),
    row('25939/76832 0 0 -398/735 53/672 1291/2520 2368/7203 -58/21609 9/9604'),
    row('10387/76832 0 0 -398/735 53/672 3091/2520 -3392/7203 32/21609 -11/9604 2/7'),
    row('-325/672 0 0 122/63 -91/288 -329/324 32/189 1/378 11/13608 0 343/486'),
)
b = row('7/80 0 0 0 0 16807/38880 -16/405 -1/38880 -1/38880 16807/77760 16807/77760 7/80')


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
    assert len(A)==len(b)==12 and all(len(r)==i for i,r in enumerate(A))
    D=lcm(*(x.denominator for r in (*A,b) for x in r))
    assert D==1493614080 and 40320**4 % D==0
    assert [sum(r) for r in A]==list(row("0 2/27 1/9 1/6 8/21 2/7 1/2 -1 2 5/7 5/7 1"))
    count=0
    for n,want in enumerate([1,1,2,4,9,20,48,115],start=1):
        ts=trees(n)
        assert len(ts)==len(set(ts))==want
        assert all(order(t)==n and defect(t)==0 for t in ts)
        count+=len(ts)
    print(f"all {count} rooted order conditions verified")
    bush=((),)*8
    tall=()
    for _ in range(8): tall=(tall,)
    assert order(bush)==order(tall)==9 and factorial(bush)==9 and factorial(tall)==362880
    db,dt=defect(bush),defect(tall)
    assert (db,dt)==(F(-263,27440),F(362,735))
    assert -117*27440*db-85*735*dt==1
    print(f"ninth-order bush and tall defects: {db}, {dt}")
    print("their displayed integer linear combination is 1")
    print(f"common denominator {D} divides (8!)^4")

if __name__=="__main__":
    main()
