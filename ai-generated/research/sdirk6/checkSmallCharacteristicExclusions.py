"""Exact independent check of the new scalar residues and nodal obstruction.

Requires SymPy; reads only polynomial definitions (never executes Lean text).
Run from any working directory. The old physical and scalar receipts are
the input of this check, not outputs of a Gröbner solver.
"""
import re
from pathlib import Path

from sympy import Poly, gcdex, symbols
from sympy.parsing.sympy_parser import parse_expr

RECEIPTS = (Path(__file__).resolve().parents[2] /
            "lean/RKCert/ReviewedNative/SDIRKSixIntegralReceipts.lean")


def check(raw):
    v, u, z = symbols("v u z")
    wanted = {"factorThree", "hThree", "vThree", "terminal"}
    defs = {}
    for name, body in re.findall(
            r"^def (\w+) \(z u v : K\) : K := (.+)$", raw, re.M):
        if name not in wanted:
            continue
        assert re.fullmatch(r"[0-9zuv*^+\- ]+", body)
        defs[name] = parse_expr(body.replace("^", "**"), local_dict=dict(z=z, u=u, v=v))
    assert defs.keys() == wanted
    terminal = defs["terminal"]
    factors = (3846112, 198898968576, 122267206287360000, 6214370355160790146744320000)
    for p, root in ((7, 1), (3533, 1645)):
        assert [i for i, a in enumerate(factors) if a % p == 0] == [1]
        assert all(pow(30, j, p) != 0 for j in range(1, 14))
        norm = lambda q: Poly(q, v, u, z, modulus=p).as_expr()
        sum_u_v = norm((-defs["vThree"] + 8*(u + v))*pow(8, -1, p))
        prod_u_v = norm((defs["hThree"] - u*defs["vThree"] + 8*u*v)*pow(8, -1, p))
        assert sum_u_v.free_symbols <= {z} and prod_u_v.free_symbols <= {z}
        # The terminal polynomial depends only on u+v and uv.
        x, y = symbols("x y")
        t = Poly(terminal, u, v)
        a, b, c, d, e, g = (t.coeff_monomial(m) for m in
                          (u**3*v**3, u**3*v**2, u**3*v, u*u*v*v, u*u*v, u*v))
        T = y*(a*y*y+b*x*y+c*(x*x-2*y)+d*y+e*x+g)
        assert Poly(T.subs({x:u+v,y:u*v}) - terminal, v, u, z).is_zero
        fz = Poly(defs["factorThree"], z, modulus=p)
        r = Poly(T.subs({x:sum_u_v, y:prod_u_v}), z, modulus=p).rem(fz)
        assert gcdex(r, fz)[2].as_expr() == z-root
        sn = int(sum_u_v.subs(z, root)) % p
        pn = int(prod_u_v.subs(z, root)) % p
        if p == 7:
            assert (sn, pn) == (0, 6)
            for un, nodes, integral in [(1, [0, 1, 2, 3], 1), (-1, [0, 1, -1], 5)]:
                forced = {t % p for t in [1, 1+un, 1+2*un, root-1+un, root-1]}
                assert forced == {t % p for t in nodes}
                mask = Poly(1, z)
                for a in nodes:
                    mask *= Poly(z-a, z)
                assert mask.eval(1) == 0 and mask.degree()+1 < 6
                for j in (0, 1):
                    value = sum(int(a)*pow(k+j+1, -1, p) for (k,), a in mask.terms())
                    assert value % p == integral
        else:
            assert (sn, pn) == (824, 524)
            delta = (sn**2 - 4*pn) % p
            assert delta == 2077
            assert pow(delta, (p-1)//2, p) == p-1
            assert all(x*x % p != delta for x in range(p))
        print(f"characteristic {p}: cubic terminal forces z={root}; endpoint checked")


if __name__ == "__main__":
    check(RECEIPTS.read_text())
