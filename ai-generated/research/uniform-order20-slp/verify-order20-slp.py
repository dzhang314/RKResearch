#!/usr/bin/env python3
"""One fixed q-local replay of the rational SLP; no search and no big expansion."""
from collections import Counter
from math import isqrt
from time import monotonic

Q = 2147483647
STEPS = (
    ("t", "e1"), ("s", "e2"), ("z", "e3"),       # verified degree-10 seed
    ("1a", "1c"),                              # seed's marked pair
    ("4a", "4b"), ("5a", "5b"), ("6a", "6b"), ("7a", "7b"),
    ("8a", "8b"), ("9a", "9b"), ("10a", "10b"),
)
STEP_SECONDS, TOTAL_SECONDS = 2, 15
STEP_OPS, TOTAL_OPS = 40000, 350000
started = monotonic()
step_started = started
step_ops = total_ops = 0
biggest = 0


def need(predicate, description):
    if not predicate:
        raise AssertionError(description)


def fold(v):
    global step_ops, total_ops, biggest
    bits = abs(v).bit_length()
    need(bits <= 63, "temporary integer bit cap")
    biggest = max(biggest, bits)
    step_ops += 1
    total_ops += 1
    need(step_ops <= STEP_OPS and total_ops <= TOTAL_OPS, "per-step/total operation cap")
    if step_ops % 256 == 0:
        now = monotonic()
        need(now-step_started <= STEP_SECONDS and now-started <= TOTAL_SECONDS, "clock stop")
    return v % Q


def div(n, d):
    d = fold(d)
    need(d != 0, "inverse must be a unit modulo the certified prime")
    return fold(fold(n) * pow(d, -1, Q))


def polynomial(roots):
    coeff = [1]
    for root in roots:
        new = [0] * (len(coeff) + 1)
        for i, c in enumerate(coeff):
            new[i] = fold(new[i] - root*c)
            new[i+1] = fold(new[i+1] + c)
        coeff = new
    return coeff


def product(xs):
    r = 1
    for x in xs:
        r = fold(r*x)
    return r


def integral(coeff, shift):
    out = 0
    for i, c in enumerate(coeff):
        out = fold(out + div(c, i+shift+1))
    return out


def inspect(roots):
    coeff = polynomial(roots)
    need(integral(coeff, 0) == integral(coeff, 1) == 0, "paid-row residue cross-check")
    h = integral(coeff, 2)
    cofs = [integral(polynomial(roots[:i]+roots[i+1:]), 0) for i in range(len(roots))]
    need(h != 0 and all(cofs), "exact next defect and all cofactors must be nonzero")
    return coeff, h, cofs


def guarded_begin():
    global step_started, step_ops
    need(monotonic()-started <= TOTAL_SECONDS, "total wall stop")
    step_started = monotonic()
    step_ops = 0


def guarded_end():
    now = monotonic()
    need(now-step_started <= STEP_SECONDS and now-started <= TOTAL_SECONDS, "wall stop")


def replay():
    guarded_begin()
    need(Q > 21 and Q % 2 and all(Q % j for j in range(3,isqrt(Q)+1,2)),
         "prime proof and all uniform moment denominators are paid")
    labels = ["z", "e1", "e2", "e3", "e4", "s", "t"]
    roots = [0, 1, 1, 1, 1, div(1,6), div(1,2)]
    coeff, h, cofs = inspect(roots)
    need(h == div(1,30240), "replay of the known confluent constant")
    print(f"Prime {Q}; initial degree {len(roots)}, distinct {len(set(roots))}, h={h}.")
    guarded_end()
    for j, (ulabel,vlabel) in enumerate(STEPS,1):
        guarded_begin()
        ui,vi = labels.index(ulabel),labels.index(vlabel)
        u,v = roots[ui], roots[vi]
        ell = fold(v-u)
        ell3 = fold(fold(ell*ell)*ell)
        a = div(h,fold(cofs[ui]*ell3))
        b = div(-h,fold(cofs[vi]*ell3))
        need(a and b, "nonzero pole residues")
        t = [
            div(fold(a*fold(b+1)), fold(a-b)),
            div(fold(a-b), fold(a+1)),
            div(fold(a+1), fold(b+1)),
        ]
        need(product(t)==a and product([fold(x-1) for x in t])==fold(-b),
             "product identities for the exact rational step")
        new = [fold(u+ell*x) for x in t]
        left = [r for i,r in enumerate(roots) if i not in (ui,vi)]
        need(len(set(new))==3 and not(set(new)&(set(left)|{u,v})), "distinct collision-free roots")
        S = fold(sum(new))
        tau = fold(S-u-v)
        R_u,R_v = fold(fold(ell*ell)*a),fold(fold(ell*ell)*b)
        physical = polynomial([u,v,tau])
        physical[0] = fold(physical[0]-fold(R_u*v)-fold(R_v*u))
        physical[1] = fold(physical[1]+R_u+R_v)
        need(physical==polynomial(new), "physical cubic residue cross-check")
        k = integral(coeff,3)
        roots = left+new
        labels = [label for i,label in enumerate(labels) if i not in (ui,vi)]+[f"{j}{l}" for l in "abc"]
        oldh = h
        coeff,h,cofs = inspect(roots)
        need(h==fold(k-fold(oldh*S)), "next exact defect residue cross-check")
        counts = Counter(roots)
        need(len(roots)==7+j and len(counts)==min(4+2*j,7+j)
             and counts[1]==max(4-j,1) and all(c==1 for x,c in counts.items() if x!=1),
             "expected confluent width, then strictly squarefree support")
        print(f"{j:2d}: ({ulabel},{vlabel}) -> {tuple(new)} ; degree={len(roots)} distinct={len(counts)} h={h} Cprod={product(cofs)}")
        guarded_end()
    guarded_begin()
    need(len(roots)==len(set(roots))==18, "actual maximum support count")
    weights=[]
    for i, (x, c) in enumerate(zip(roots,cofs)):
        derivative = product(fold(x-y) for k,y in enumerate(roots) if k != i)
        weights.append(div(c,derivative))
    need(all(weights), "every final aggregate weight contributes")
    actual = [fold(sum(fold(w*pow(x,j,Q)) for x,w in zip(roots,weights))) for j in range(21)]
    need(actual[:20]==[div(1,j+1) for j in range(20)], "all paid scalar moments modulo q")
    need(h==fold(div(1,21)-actual[20])!=0, "literal first unpaid scalar moment")
    need(roots[labels.index("1b")]==div(-3,32), "the exact exterior retained site")
    print("Final label order:", " ".join(labels))
    print("Final sites mod q:", tuple(roots))
    print("Final weights mod q:", tuple(weights))
    print(f"Uniform exact order 20: 18 active sites, first defect mod q = {h}.")
    print(f"Resource guards: {total_ops} bounded modular operations, actual temporary max {biggest} bits, zero group-law increments.")
    print("PASS: fixed rational SLP and modular nonzero/unit certificate; no expanded coefficient table.")
    guarded_end()


if __name__=="__main__":
    replay()
