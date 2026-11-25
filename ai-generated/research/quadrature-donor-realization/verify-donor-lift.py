#!/usr/bin/env python3
"""Fixed exact checks of the recursive donor formulas; no search or Lean."""
from collections import defaultdict
from fractions import Fraction as F
from functools import cache
from math import prod


def check(test, why):
    if not test:
        raise AssertionError(why)


def mul_linear(coef, x):
    out = [F(0)] * (len(coef)+1)
    for k, a in enumerate(coef):
        out[k] -= x*a
        out[k+1] += a
    return out


@cache
def lagrange(z):
    check(len(z) == len(set(z)), ("singular donor bank", z))
    result = []
    for j, x in enumerate(z):
        coef = [F(1)]
        delta = F(1)
        for k, y in enumerate(z):
            if k != j:
                coef = mul_linear(coef, y)
                delta *= x-y
        result.append(tuple(a/delta for a in coef))
    return tuple(result)


def pairing(x, y):
    return sum((a*b for a,b in zip(x,y)), F(0))


def moment(rule, k):
    return sum((b*x**k for x,b in rule.items()), F(0))


def defect(rule, k):
    return moment(rule,k)-F(1,k+1)


def from_raw(xb):
    rule = defaultdict(F)
    for x,b in xb:
        rule[F(x)] += F(b)
    return {x:b for x,b in rule.items() if b}


def realize(p, xb, diagonal, extra=False):
    """Sparse exact tableau; maps every given active mass unchanged."""
    rule = from_raw(xb)
    check(p >= 1 and all(defect(rule, k) == 0 for k in range(p)),
          ("input order", p))
    check(not extra or p >= 2, "no nonbush perturbation at order one")
    A, b, c, grade, strict_terms = [], [], [], [], []
    anchor = F(diagonal(0))
    A.append({0: anchor})
    b.append(F(0)); c.append(anchor); grade.append(1)
    bank = [0]
    blocked = set(rule) | {anchor}
    counter = -1

    def fresh():
        nonlocal counter
        while counter in blocked:
            counter -= 1
        x = F(counter)
        blocked.add(x)
        counter -= 1
        return x

    def append(x, donors, order, output=F(0), xi=F(0)):
        i = len(A)
        d = F(diagonal(i))
        z = tuple(c[j] for j in donors)
        RHS = tuple(x**(k+1)/F(k+1) - d*x**k +
                    (xi if k == p-1 else 0) for k in range(len(donors)))
        a = tuple(pairing(ell,RHS) for ell in lagrange(z))
        h = max(1,order-1)
        check(all(j<i and grade[j]>=h for j in donors), "causal pure donors")
        row = {j:y for j,y in zip(donors,a)}
        row[i] = d
        A.append(row)
        c.append(sum(row.values(), F(0)))
        b.append(output)
        grade.append(order)
        strict_terms.append(len(donors))
        check(c[-1] == x, "actual physical row sum")
        for k in range(len(donors)):
            total = sum((coeff*c[j]**k for j,coeff in row.items()), F(0))
            expected = x**(k+1)/F(k+1) + (xi if k == p-1 else 0)
            check(total==expected, ("exact paid primitive", i,k))

    if extra and p==2:
        append(fresh(),bank,1)
        bank.append(1)
    for g in range(2,p):
        start = len(A)
        for _ in range(g+(extra and g==p-1)):
            append(fresh(),bank,g)
        bank = list(range(start,len(A)))
    helpers = len(A)
    for i,(x,w) in enumerate(rule.items()):
        # When the next bush passes, setting this to 1 makes the
        # next non-bush sequence fail while retaining that bush.
        xi = F(int(extra and i==0 and defect(rule,p)==0))
        append(x,bank,p,w,xi)
    check(helpers == max(1, p*(p-1)//2) + int(extra), ("helper count",p,extra))
    check(all(not w for w in b[:helpers]), "zero helper outputs")
    check(len(A) == helpers+len(rule) and from_raw(zip(c,b))==rule, "weighted support")
    check(all(A[j][j]==F(diagonal(j)) and all(k <= j for k in A[j])
              for j in range(len(A))), "prescribed triangular diagonal")
    return A,b,c,grade,rule,sum(strict_terms)


@cache
def tree_order(t):
    return 1+sum(map(tree_order,t))


@cache
def ff(t):
    return prod(tree_order(u)*ff(u) for u in t)


@cache
def bush(p):
    return ((),)*(p-1)


def rooted_trees(p):
    by_order = [(), ((),)]
    for n in range(2,p+1):
        pool = [(t, k) for k in range(1,n) for t in by_order[k]]
        def children(rest, start):
            if rest==0:
                yield ()
            else:
                for j in range(start,len(pool)):
                    t,k = pool[j]
                    if k<=rest:
                        for suffix in children(rest-k,j):
                            yield (t,)+suffix
        by_order.append(tuple(children(n-1,0)))
    return by_order


def rooted_audit(result,p,failed):
    A,b,c,g,_,_ = result
    @cache
    def phi(t):
        if not t:
            return (F(1),)*len(A)
        cols = tuple(phi(u) for u in t)
        return tuple(prod(sum(a*v[j] for j,a in row.items()) for v in cols)
                     for row in A)
    trees = rooted_trees(p)
    for r in range(1,p+1):
        for t in trees[r]:
            col = phi(t)
            check(all(g[i]<r or col[i]==c[i]**(r-1)/ff(t)
                      for i in range(len(A))), ("local pure grade", r, t))
            check(pairing(b,col)==F(1,r*ff(t)), ("literal rooted output",r,t))
    check(tree_order(failed)==p+1 and
          pairing(b,phi(failed)) != F(1,tree_order(failed)*ff(failed)),
          ("exact next order fail", p, failed))
    return sum(map(len,trees))


ERK = lambda _: F(0)
DIRK = lambda i: F(1+i%5,7)
SDIRK = lambda _: F(1,2)

x1 = [(F(2,3), F(1))]
x2 = [(F(1,2), F(3,4)), (F(1,2), F(1,4)), (F(2), F(5)), (F(2), F(-5))]
simpson = [(F(0),F(1,6)),(F(1,2),F(2,3)),(F(1),F(1,6))]
for p,raw,kind,diag in [
    (1,x1,"ERK",ERK), (2,x2,"varying-diagonal DIRK",DIRK),
    (4,simpson,"strict SDIRK",SDIRK)]:
    data=realize(p,raw,diag)
    n=rooted_audit(data,p,bush(p+1))
    print(f"Small {kind} p={p}: {n} literal paid tree types; next bush fails.")
for p in (2,3):
    check(defect(from_raw(simpson),p)==0, ("Simpson pays next bush", p))
    data=realize(p,simpson,SDIRK,extra=True)
    n=rooted_audit(data,p,(bush(p),))
    print(f"Exact p={p} with scalar order 4: {n} paid tree types; "
          "one extra helper, unary bush fails.")

# Reconstruct the approved standalone 19-site scalar fixture by its
# Lagrange formula, not from any tableau data.
u=(1,3,6,11,18,26,34,44,54,64,74,84,94,102,110,117,122,125,127)
sites = tuple(F(i,128) for i in u)
masses = tuple(sum((a/F(k+1) for k,a in enumerate(ell)),F(0))
               for ell in lagrange(sites))
fixture=tuple(zip(sites,masses))
check(all(w>0 for w in masses), "19-site positive masses")
err = F(-35673661962961255473941956091,
        302182019494570093201085819637437237821440)
check(defect(from_raw(fixture),20)==err, "known exact degree-20 defect")
for kind,diag in [("ERK",ERK),("varying-diagonal DIRK",DIRK),
                 ("strict SDIRK, gamma=1/2",SDIRK)]:
    A,b,c,g,rule,rowsum = realize(20,fixture,diag)
    check(len(A)==209 and sum(w!=0 for w in b)==19, "19 active rows")
    check(sum(b[i]*c[i]**20 for i in range(len(A)))-F(1,21)==err,
          ("next reviewed bush defect",kind))
    if diag is SDIRK:
        check(c.count(F(1,2))==2 and b[0]==0, "first-clock coincidence does not add mass")
    print(f"Order-20 {kind}: 190 zero-output helpers, 19 live sites, "
          f"{rowsum} exact row equations; next bush defect reproduced.")
print("PASS: exact donor checks; no held data, search, or Lean.")
