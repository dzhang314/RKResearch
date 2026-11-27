"""Independent stdlib replay of one universally paid strict SDIRK tableau."""
from fractions import Fraction as Q
from math import lcm, prod

A = [list(map(Q,row.split())) for row in (
    "1/4", "-1 1/4", "-3/16 -1/16 1/4",
    "17/128 17/384 7/96 1/4",
    "1107/4000 209/4000 21/1000 0 1/4",
    "345/1024 35/1024 0 27/64 -75/256 1/4")]
b = list(map(Q,"0 0 7/54 2 -125/54 32/27".split()))
c = [sum(row) for row in A]

def check():
    assert [len(row) for row in A] == list(range(1,7))
    assert all(a[-1] == Q(1,4) for a in A)
    d = lcm(*(a.denominator for row in A for a in row), *(w.denominator for w in b))
    assert d == 3456000 and 30**10 % d == 0
    trees, sizes, fac = [()], [1], [1]
    for n in range(2,6):
        def visit(j, left, branch):
            if left == 0:
                trees.append(tuple(branch))
                sizes.append(n)
                fac.append(n * prod(fac[k] for k in branch))
                return
            while j < len(trees) and sizes[j] <= left:
                visit(j, left-sizes[j], branch+[j])
                j += 1
        visit(0,n-1,[])
    assert [sizes.count(i) for i in range(1,6)] == [1,1,2,4,9]
    branches = []
    for tree, f in zip(trees, fac):
        phi = [prod(branches[j][i] for j in tree) for i in range(6)]
        branches.append([sum(a*x for a,x in zip(row,phi)) for row in A])
        assert f * sum(w*x for w,x in zip(b,phi)) == 1
    v = [Q(1)]*6
    for _ in range(5):
        v = [sum(a*x for a,x in zip(row,v)) for row in A]
    tall = 720*sum(w*x for w,x in zip(b,v))-1
    bush = 6*sum(w*x**5 for w,x in zip(b,c))-1
    assert (tall,bush) == (Q(11,64),Q(-7,400))
    assert 128*tall + 1200*bush == 1
    print("All 17 trees pass at scale 3456000; order-six discrepancies combine to one.")

if __name__ == "__main__":
    check()
