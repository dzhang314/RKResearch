#!/usr/bin/env python3
"""Exact reduced nine-stage cubic-dirty SDIRK7 chart, deliberately specialized to F19.

No claim of rational or p-adic existence follows.  The search uses no CAS,
no floating point and no external dependencies.  Every found tableau is
independently checked on all rooted trees through size seven.
"""
from functools import lru_cache
from itertools import product
from math import prod
import argparse
import json

P = 19
INV = (0,) + tuple(pow(a, -1, P) for a in range(1, P))
def DIV(a, b):
    assert b % P
    return a * INV[b % P] % P
I2, I3 = INV[2], INV[3]


def mul_linear(f, a):
    g = [0] * (len(f) + 1)
    for i, v in enumerate(f):
        g[i] = (g[i] - a * v) % P
        g[i + 1] = (g[i + 1] + v) % P
    return g


def hull(x):
    f = [1]
    for a in x:
        f = mul_linear(f, a)
    return f


def integrate(f, mom, shift=0):
    return sum(v * mom[i + shift] for i, v in enumerate(f)) % P


def gaussian(rows, n):
    rows = [[v % P for v in r] for r in rows]
    piv = []
    k = 0
    for j in range(n):
        i = next((i for i in range(k, len(rows)) if rows[i][j]), None)
        if i is None:
            continue
        rows[k], rows[i] = rows[i], rows[k]
        r = rows[k]
        f = INV[r[j]]
        r = rows[k] = [x * f % P for x in r]
        for i in range(len(rows)):
            if i != k and rows[i][j]:
                s, f = rows[i], rows[i][j]
                rows[i] = [(x - f * y) % P for x, y in zip(s, r)]
        piv.append(j)
        k += 1
    if any(r[n] for r in rows[k:]):
        return None
    x = [0] * n
    for i, j in enumerate(piv):
        x[j] = rows[i][n]
    return x


def solve_table(z, ys, b, d, h, d0, v, v0, theta, f, t):
    """All A equations are linear once the seven clocks and D are fixed."""
    clock = [1, 1+t, (z-h) % P] + [(z-y) % P for y in ys]
    yall = [(z-x) % P for x in clock]
    B = [0, 0, 0] + b
    D = [0, 0, d0] + d
    a = [[int(i == j) for j in range(9)] for i in range(9)]
    a[1][0] = t
    x, w = clock[1:3]
    a[2][1] = DIV(w*w-4*w+2, 2*t)
    a[2][0] = (w-1-a[2][1]) % P
    g = [1, (1+2*t-t*t) % P, 0] + [0] * 6
    vg = DIV(a[2][0]*g[0] + a[2][1]*g[1], v0)
    vh = DIV(a[2][0] + a[2][1]*x*x+w*w - I3*w**3, v0)
    unknown = [(i, j) for i in range(3, 9) for j in range(i)]
    eqs = []
    def eq(coef, target):
        rhs = target - sum(coef(i, j)*a[i][j] for i in range(9) for j in range(i+1))
        eqs.append([coef(i, j) for i, j in unknown] + [rhs])
    for i in range(3, 9):
        zc, vi = clock[i], v[i-3]
        for col, target in [([1]*9, zc), (clock, I2*zc**2), (g,vg*vi),
                ([x*x for x in clock],I3*zc**3+vh*vi)]:
            eq(lambda r,j: col[j] if r==i else 0, target)
    for j in range(9):
        yy = yall[j]
        for row, target in [
            (B, B[j]*yy),
            ([bb*y for bb,y in zip(B,yall)], I2*B[j]*yy**2-D[j]),
            ([bb*y*y for bb,y in zip(B,yall)],I3*B[j]*yy**3+f(yy)*D[j]),
            (D,D[j]*(1+theta*(1-yy))),
        ]:
            eq(lambda i,k: row[i] if k==j else 0,target)
    ans = gaussian(eqs, len(unknown))
    if ans is None:
        return None
    for (i,j), e in zip(unknown, ans):
        a[i][j] = e
    physical = [[DIV(x,z) for x in row] for row in a]
    return physical, B, a, clock, g


@lru_cache(None)
def size(T):
    return 1+sum(size(U) for U in T)


@lru_cache(None)
def density(T):
    return size(T)*prod(density(U) for U in T)


@lru_cache(None)
def trees(n):
    if n == 1:
        return ((),)
    ts = tuple((k,U) for k in range(1,n) for U in trees(k))
    def choice(left, idx):
        if left == 0:
            yield ()
        else:
            for j, (k,U) in enumerate(ts[idx:],idx):
                if k > left:
                    break
                for tail in choice(left-k,j):
                    yield (U,)+tail
    return tuple(choice(n-1,0))


def verify(a,b):
    @lru_cache(None)
    def stage(T):
        return tuple(prod(sum(a[i][j]*stage(U)[j] for j in range(9)) for U in T)%P
                    for i in range(9))
    order7 = [T for n in range(1,8) for T in trees(n)]
    assert len(order7) == 85
    residual = lambda T: (density(T)*sum(bi*wi for bi,wi in zip(b,stage(T)))-1) % P
    assert all(residual(T)==0 for T in order7), 'Invalid order-seven search candidate'
    bad = next((T for T in trees(8) if residual(T)),None)
    assert bad is not None
    return bad, residual(bad)


def search():
    stats = dict(quadratures=0, third=0, fourth=0, dirty=0, linear=0)
    for u in range(P):
        if u == 1:
            continue
        du = (I2*u*u-2*u+1) % P
        assert du
        theta = INV[2*du % P]
        f = lambda y: (-4*I3+(2*theta-2)*I3*(y-1)) % P
        for q in sorted({(4-u)%P,(2*u-1)%P}-{1,u}):
            dqs = []
            for dq in range(P):
                tap = DIV(I2*q*q-2*q+1-dq,u-1)
                r = (q-1-tap)%P
                if (q*q+tap*u*u+r-I3*q**3-f(q)*dq)%P:
                    continue
                if (tap*du-I2*r-theta*(1-q)*dq)%P == 0:
                    dqs.append(dq)
            for z in range(1,P):
                mom = [DIV(pow(z,i,P),i+1) for i in range(7)]
                free = sorted(set(range(P))-{1,u,q})
                for a, b5 in product(free,repeat=2):
                    if a==b5:
                        continue
                    base = hull((1,u,q,a,b5))
                    L0,L1 = integrate(base,mom), integrate(base,mom,1)
                    cs = (DIV(L1,L0),) if L0 else (() if L1 else free)
                    for c in cs:
                        if c in (1,u,q,a,b5):
                            continue
                        ys = [a,b5,c,q,u,1]
                        no = [ys[:i]+ys[i+1:] for i in range(6)]
                        s = [INV[prod(yi-yj for yj in r)%P] for yi,r in zip(ys,no)]
                        B = [s[i]*integrate(hull(r),mom)%P for i,r in enumerate(no)]
                        if 0 in B:
                            continue
                        stats['quadratures'] += 1
                        for dq in dqs:
                            # (y-h)D_y / s_y is affine in y, even if h itself is a tail clock.
                            fix = [B[3]*dq%P, B[4]*du%P, -B[5]*I2%P]
                            K = [DIV(d,w) for d,w in zip(fix,s[3:])]
                            wy, wz = DIV(q-1,u-1), DIV(u-q,u-1)
                            A0=(q*K[0]-wy*u*K[1]-wz*K[2])%P
                            A1=(K[0]-wy*K[1]-wz*K[2])%P
                            hs=(DIV(A0,A1),) if A1 else (() if A0 else range(P))
                            for h in hs:
                                qa = (u-h)*K[1] % P
                                qb = (1-h)*K[2] % P
                                slope = DIV(qa-qb,u-1)
                                wt = [(qb+slope*(y-1))%P for y in ys]
                                variants=[]
                                if h not in ys:
                                    D = [DIV(w*s0,y-h) for w,s0,y in zip(wt,s,ys)]
                                    variants.append(((-sum(D))%P,D))
                                else:
                                    j = ys.index(h)
                                    if wt[j]:
                                        continue
                                    D = [slope*si%P for si in s]
                                    d0s = ((D[j]-fix[j-3])%P,) if j>=3 else range(1,P)
                                    for d0 in d0s:
                                        D0=D.copy()
                                        D0[j]=(D0[j]-d0)%P
                                        variants.append((d0,D0))
                                for d0, D in variants:
                                    if not d0:
                                        continue
                                    assert D[3:]==fix and all(
                                        (sum(di*pow(y,k,P) for di,y in zip(D,ys))+d0*pow(h,k,P))%P==0
                                        for k in range(5))
                                    stats['third'] += 1

                                    # Three future entries in the fourth reverse row
                                    # are determined by the first three reads.
                                    d6 = DIV(D[2],B[2])
                                    values = [c-1, I2*c*c-c-d6, I3*c**3-c*c+f(c)*d6]
                                    tt = gaussian([[pow(y,i,P) for y in ys[3:]]+[values[i]]
                                                   for i in range(3)],3)
                                    assert tt is not None
                                    if (sum(DIV(di,bi)*ti for di,bi,ti in zip(D[3:],B[3:],tt))
                                         -theta*(1-c)*d6)%P:
                                        continue
                                    stats['fourth'] += 1
                                    vi = [DIV((y-h)*di,bi) for y,di,bi in zip(ys,D,B)]
                                    if not any(vi) or sum(bi*w*w for bi,w in zip(B,vi))%P:
                                        continue
                                    v0=DIV(-sum(di*w for di,w in zip(D,vi)),d0)
                                    if not v0:
                                        continue
                                    stats['dirty'] += 1
                                    for t in range(1,P):
                                        stats['linear']+=1
                                        sol=solve_table(z,ys,B,D,h,d0,vi,v0,theta,f,t)
                                        if sol:
                                            A,b,H,x,g=sol
                                            bad,value=verify(A,b)
                                            return dict(z=z,sample_theta=theta,tableau=A,b=b,
                                                normalized_clocks=x,first3_zero=True,seed=g,
                                                physical_diagonal=INV[z],reflection=ys,helper_reflection=h,
                                                d_row=[0,0,d0]+D,dirty_column=[0,0,v0]+vi,
                                                exact_order8_obstruction_tree=bad,order8_residual=value,stats=stats)
    return {'status':'No dirty solution in the enumerated chart','stats':stats}


if __name__ == '__main__':
    arg=argparse.ArgumentParser()
    arg.add_argument('--output')
    args=arg.parse_args()
    result=search()
    report=json.dumps(result,indent=2)
    print(report)
    if args.output:
        with open(args.output,'w') as f:
            f.write(report+'\n')
