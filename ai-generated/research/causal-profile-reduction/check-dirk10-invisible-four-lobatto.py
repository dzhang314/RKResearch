#!/usr/bin/env python3
"""Exact mod-227 certificate for the four-invisible-distinct DIRK10 branch.

No tableau coefficients are reduced. Only the four fixed Lobatto roots,
their distinct orders, and deformed reverse clock matrices enter here.
See dirk-order10-invisible-four-lobatto.md for the good-reduction argument.
"""
from itertools import permutations

P = 227

def div(a, b):
    b %= P
    assert b
    return a*pow(b, -1, P)%P

def solve(nodes, target, kappa=None, ell=None, contrast=False):
    """Columns for the weighted reverse primitive rows k=1,...,n."""
    n = len(nodes)
    a = []
    for k in range(1, n+1):
        coeffs = [x**k for x in nodes]
        transfer = (kappa if k == 3 else ell if k == 4 else None)
        if transfer is not None:
            pos = -1 if contrast else 0
            coeffs[pos] -= transfer
        a.append([(x%P) for x in coeffs]+[div(target**(k+1),k+1)])
    for j in range(n):
        k = next(k for k in range(j,n) if a[k][j])
        a[j],a[k] = a[k],a[j]
        normalizer = div(1,a[j][j])
        a[j] = [x*normalizer%P for x in a[j]]
        for k in range(n):
            if k != j:
                t = a[k][j]
                a[k] = [(v-t*u)%P for v,u in zip(a[k],a[j])]
    return [r[-1] for r in a]

def lerp(x, y, fx, fy, z):
    return (fx+div((fy-fx)*(z-x),y-x))%P

Y = [x for x in range(P) if (42*x**4-84*x**3+56*x**2-14*x+1)%P == 0]
assert Y == [24,51,177,204]
assert all((1+6*x*(1-x))%P for x in Y)
case_count = 0
for u,v,w,z in permutations(Y+[1],4):
    # First exterior row: a single core donor, no preceding exterior.
    tv,dv = solve([u,v],v)
    assert tv and dv
    kappa = div(dv*v**3+tv*u**3-div(v**4,4),tv)
    Lv = div(dv*v**4+tv*u**4-div(v**5,5),tv)

    # Earlier copy of the core has not yet appeared.
    tw,vw,dw = solve([u,v,w],w,kappa)
    assert tw and dw
    Lw = div(dw*w**4+tw*u**4+vw*v**4-div(w**5,5),tw)
    Lz = lerp(v,w,Lv,Lw,z)
    assert solve([u,v,w,z],z,kappa,Lz)[-1]
    # The second core copy appears after exactly two ordinary labels.
    Lu = lerp(v,w,Lv,Lw,u)
    assert solve([u,v,w,u],u,kappa,Lu)[-1]

    # The second core copy appears after exactly one ordinary label.
    hq,vq,dq = solve([u,v,u],u,kappa)
    assert hq and dq
    Lu1 = div((hq+dq)*u**4+vq*v**4-div(u**5,5),hq)
    Lw1 = lerp(u,v,Lu1,Lv,w)
    # The contrast column is separate from the common core total.
    assert solve([u,v,w,0],w,kappa,Lw1,contrast=True)[2]
    case_count += 1
assert case_count == 120
print("120 ordered triples after the core: all deformed matrices and required diagonals nonzero mod 227")
