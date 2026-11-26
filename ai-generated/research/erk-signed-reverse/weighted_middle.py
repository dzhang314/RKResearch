"""Shared small charts for the weighted-receiver construction at orders 11–16."""

from fractions import Fraction as F
from math import comb, prod


def prepare(rk, order, vv, mul, add, scale, cardinal):
    z,o = rk.Z,rk.O
    a,b = F(1,3),F(1,2)
    centers = [z,a,b]
    clock = lambda v:(1+v)/2
    grid_pure = {-o,o,-a,a,-b,b,z}
    h = [o,z,-o]
    ell6_w = [1/((1-u*u)**2*prod(u*u-v*v for v in centers if v!=u)) for u in centers]
    assert all(rk.unit(w) for w in ell6_w)
    ell6 = lambda polynomial:rk.dot(ell6_w,[vv(polynomial,v) for v in centers])
    ell6op = lambda j:rk.dot(ell6_w,[clock(v)**j for v in centers])

    def chart6():
        rows, ops, data = rk.short(5)
        new = rk.prepend((ops,data),[clock(a),clock(b)],rows)
        return rows, ops[:3]+ops[4:]+new[0], data[:3]+data[4:]+new[1]

    def chart7():
        rows, ops, data = chart6()
        new_sites = [-b,-a,a,b]
        new = rk.prepend((ops,data),[clock(v) for v in new_sites],rows)
        return rows, ops[:2]+new[0]+[ell6op], data[:2]+new[1]+[[z]*8+ell6_w]

    def high7(rows):
        sites = [-b,-a,a,b,o]
        hplus = [o,2*o,o]
        kernel = mul(hplus,rk.nodal(sites))
        deriv = lambda poly:[j*c for j,c in enumerate(poly) if j]
        dpivot = vv(deriv(kernel),o)
        assert dpivot==F(8,3) and rk.unit(dpivot)
        weights = []
        for u in sites:
            pol = mul(hplus,scale(cardinal(sites,u),1/(1+u)**2))
            pol = add(pol,scale(kernel,-vv(deriv(pol),o)/dpivot))
            weights.append(ell6(deriv(pol)))
        read = [z]*len(rows)
        for j,w in zip([11,12,13,14,7],weights):
            read[j] = w
        func = lambda poly:rk.dot(weights,[vv(poly,v) for v in sites])
        return func,read

    if order==11:
        fgrade = 5
        fwd,fo,fr = rk.short(5)
        fwd_pin = lambda p:sum(c*rk.average(j) for j,c in enumerate(p))
        high_fwd_row = fr[2]
    elif order<=14:
        fgrade = 6
        fwd,fo,fr = chart6()
        fwd_pin,high_fwd_row = ell6,[z]*8+ell6_w
    else:
        fgrade=7
        fwd,fo,fr = chart7()
        fwd_pin,high_fwd_row = high7(fwd)

    pins = []
    high_r = []
    boundary = h
    if order in (11,12):
        reverse = rk.eight_row_grade_five()[0][:6]
        top=4
        R = lambda p:vv(p,-a)-F(64,81)*vv(p,z)-F(4,81)*vv(p,o)
        Rop = lambda j: F(1,3)**j-F(64,81)*F(1,2)**j-F(4,81)
        Rrow = [z,z,F(-64,81),F(-4,81),z,o]
        ro = [rk.eval_at(z),rk.eval_at(o),rk.moment(0),Rop]
        rr = [rk.basis(0,6),rk.basis(4,6),[F(1,6),z,F(2,3),F(1,6),z,z],Rrow]
        pins = [R]
        high_r = [(Rop,Rrow)]
    elif order==13:
        reverse,ro,rr = rk.eight_row_grade_five()
        top=5
        boundary=[o,o]
        R = lambda p:vv(p,-a)-F(17,81)*vv(p,o)
        Rop = lambda j:F(1,3)**j-F(17,81)
        Rrow = [x-F(17,81)*y for x,y in zip(rk.basis(6,8),rk.basis(4,8))]
        pins = [R]
        high_r = [(Rop,Rrow)]
    elif order in (14,15):
        reverse,ro,rr = chart6()
        top=6
        if order==14:
            pins=[ell6]
            high_r=[(ell6op,[z]*8+ell6_w)]
    else:
        reverse,ro,rr = chart7()
        top=7
        boundary=[o,o]
        pin, row = high7(reverse)
        pins=[pin]
        high_r=[(lambda n:pin([F(comb(n,k),2**n) for k in range(n+1)]),row)]

    if order<=14:
        radii=(1,2,3,4,6) if order<=12 else (1,2,3,4,5,6)
        grid = [z]+[F(s*i,6) for s in (-1,1) for i in radii]
    else:
        grid = [z]+[F(s*i,12) for s in (-1,1) for i in (1,2,3,4,6,8,12)]
        grid_pure |= {F(1,12)}
    early = sorted(set(grid)-grid_pure)
    late = sorted(grid_pure-({-o,o,z} if order==11 else {-o,o} if order<=14 else {o}))
    split = [z] if order==16 else []
    injection = {11:17280,12:F(-320,9),13:F(640,9),14:F(-1280,9),
                 15:F(76800,7),16:F(-153600,7)}[order]
    exact_high_r = list(zip(ro[:1 if order in (13,16) else 2],rr[:1 if order in (13,16) else 2]))+high_r
    exact_high_f = list(zip(fo[:1 if order>=15 else 2],fr[:1 if order>=15 else 2]))
    return (fwd,fo,fr,fgrade,fwd_pin,high_fwd_row,exact_high_f,
            reverse,ro,rr,top,boundary,pins,exact_high_r,sorted(grid),split,early,late,injection)
