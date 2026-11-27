#!/usr/bin/env python3
"""Independent exact residue separator, requiring only Python integers."""
from itertools import permutations


def replay(p):
    def div(a, b):
        assert b % p, ("denominator", b)
        return a * pow(b % p, -1, p) % p

    def clock_poly(x):
        return (42*x**4 - 84*x**3 + 56*x*x - 14*x + 1) % p

    def H(x):
        return x * clock_poly(x) % p

    def primitive(coeffs, x):
        return sum(div(c*x**(k+1), k+1) for k,c in enumerate(coeffs)) % p

    def product(nodes):
        c = [1]
        for z in nodes:
            c = [((c[k-1] if k else 0) - z*(c[k] if k < len(c) else 0)) % p
                 for k in range(len(c)+1)]
        return c

    def tap(nodes, z, x):
        rest = tuple(u for u in nodes if u != z)
        assert len(rest) == 4
        d = 1
        for u in rest:
            d = d*(z-u) % p
        tap = div(primitive(product(rest), x), d)
        assert tap
        return tap

    def fpoly(tau):
        h = [0,1,-14,56,-84,42]
        f = [0]*5
        f[4] = h[5]
        for k in range(3,-1,-1):
            f[k] = (h[k+1]+tau*f[k+1]) % p
        assert (h[0]+tau*f[0]) % p == 0
        return f

    roots = tuple(z for z in range(p) if clock_poly(z) == 0)
    assert len(roots) == 4 and 0 not in roots and 1 not in roots
    if p == 227:
        assert roots == (24,51,177,204)
    for a,x in permutations((*roots,1), 2):
        assert (5*a*(x-a)-x*x) % p, (a,x)
    for k in (2,3,4,5,6,36,60):
        assert div(k,k) == 1
    for q_core in (True,False):
        count = 0
        for tau,x in permutations(roots, 2):
            q = div(x*(2*x*x-3*(tau+1)*x+5*tau), 3*x*x-5*(tau+1)*x+10*tau)
            assert q not in (*roots,0,1), (tau,x,q)
            xi, a = (q,tau) if q_core else (tau,q)
            labels = (0,xi,a,1,x)
            S = {v:tap(labels,v,x) for v in labels}
            if q_core:
                f = fpoly(tau)
                scaled_a = (div(primitive(f,x),S[a]) - sum(c*tau**i for i,c in enumerate(f))) % p
            else:
                scaled_a = div(-H(a),a-tau)
            sh = {a:scaled_a, 1:div(-1,1-tau)}
            assert all(sh.values())
            for y,z in ((a,1),(1,a)):
                hy = div(xi**2*y**3,36*(y-xi))
                gamma = div(xi**3,6)
                alpha = div(3*(y-xi)*(y-2*xi),xi**2)
                term = gamma*(y-div(xi,2))*sh[y]
                if q_core:
                    before = (alpha*H(xi)*hy - term*(xi-tau)) % p
                else:
                    before = (alpha*hy*(S[y]*sh[y]+S[z]*sh[z]) - term*S[xi]) % p
                after = (36*(xi-y)*(y-2*z)*sh[z]*hy - xi**2*z**3*(2*y-z)*sh[y]) % p
                assert before and after, (tau,x,y,z,q,before,after)
                count += 2
        assert count == 48
        print(f"mod {p}, q as {'core' if q_core else 'head'}: {count} timing cases excluded")


if __name__ == "__main__":
    replay(227)
    replay(419)
