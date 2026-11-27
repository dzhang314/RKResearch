"""Independent exact rooted replay of the two denominator charts."""
from fractions import Fraction as Q
from math import gcd, lcm, prod

TABLEAUX = [
    (
        [["1"], ["-6/11", "1"], ["14907/2900", "-13167/2900", "1"],
         ["-15818893/310500", "190522673/6520500", "7279319/326025", "1"],
         ["173/92", "-6655/2484", "-28271375/155877831", "-5000/251011", "1"]],
        ["47/216", "14641/22680", "-4940875/569292948", "14375/8032352", "23/160"],
        (Q(-151), Q(-29, 550)), (-5, 14300)
    ),
    (
        [["1/4"], ["-3/2", "1/4"], ["1971/6200", "819/6200", "1/4"],
         ["1642391/6480000", "-31991/28080000", "1665289/8424000", "1/4"],
         ["107/270", "-2/195", "2850760/18855369", "-2000/53719", "1/4"]],
        ["47/81", "1/1404", "5645875/56566107", "-50000/53719", "5/4"],
        (Q(11, 64), Q(-217, 3200)), (-8832, -22400)
    )
]

def trees_to(n):
    trees, size, fac = [()], [1], [1]
    for k in range(2,n+1):
        def visit(i, budget, branch):
            if budget==0:
                trees.append(tuple(branch))
                size.append(k)
                fac.append(k*prod(fac[j] for j in branch))
                return
            while i<len(trees) and size[i]<=budget:
                visit(i,budget-size[i],branch+[i])
                i+=1
        visit(0,k-1,[])
    return trees, size, fac

def check():
    dd = []
    for rows, b, errors, bezout in TABLEAUX:
        A = [list(map(Q,row)) for row in rows]
        b = list(map(Q,b))
        assert [len(row) for row in A] == list(range(1,6))
        assert all(a[-1]==A[0][0] for a in A) and A[0][0] != 0
        d = lcm(*(v.denominator for a in A for v in a),*(v.denominator for v in b))
        dd.append(d)
        trees, size, fac = trees_to(5)
        assert [size.count(k) for k in range(1,6)] == [1,1,2,4,9]
        branches = []
        for tree, n in zip(trees, fac):
            phi = [prod(branches[j][i] for j in tree) for i in range(5)]
            branches.append([sum(x*y for x,y in zip(row,phi)) for row in A])
            assert n*sum(w*x for w,x in zip(b,phi)) == 1
        v = [Q(1)]*5
        for _ in range(5):
            v = [sum(x*y for x,y in zip(row,v)) for row in A]
        tall = 720*sum(w*x for w,x in zip(b,v))-1
        bush = 6*sum(w*sum(row)**5 for w,row in zip(b,A))-1
        assert (tall,bush)==errors and bezout[0]*tall+bezout[1]*bush==1
        print(f"scale {d}: all 17 conditions; sixth defects {tall}, {bush}")
    d1,d2 = dd
    assert 134909209*d1 - 4016871581*d2 == gcd(d1,d2) == 324000
    assert 324000*75 == 30**5

if __name__ == "__main__":
    check()
