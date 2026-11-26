"""Standalone exact integer column-receipt utility; no RK fixtures or solvers."""
from fractions import Fraction as Q
from math import gcd,lcm


def require_paid(d, pay):
    assert d > 0
    k, q = 0, 1
    while q % d:
        assert gcd(d // gcd(d, q), pay) > 1, d
        k, q = k + 1, q * pay
    return {"den": str(d), "pay_exp": k, "pay_cofactor": str(q // d)}

def encode(value, dim, pay):
    flat = value if dim == 1 else [x for row in value for x in row]
    d = lcm(*(Q(x).denominator for x in flat))
    def integer(x):
        z = Q(x) * d
        assert z.denominator == 1
        return str(z.numerator)
    num = [integer(x) for x in value] if dim == 1 else [[integer(x) for x in row] for row in value]
    return {**require_paid(d, pay), "num": num}

def ints(a):
    return [[str(x) for x in col] for col in a]

def egcd(a, b):
    r0, r1, x0, x1, y0, y1 = a, b, 1, 0, 0, 1
    while r1:
        q, r = divmod(r0, r1)
        r0, r1, x0, x1, y0, y1 = r1, r, x1, x0-q*x1, y1, y0-q*y1
    return (r0, x0, y0) if r0 >= 0 else (-r0, -x0, -y0)

def add_scaled(v, a, w, b):
    return [a*x+b*y for x, y in zip(v, w, strict=True)]

def strip_paid(col, pay):
    """Remove only invertible integer content before reducing the lattice."""
    content = gcd(*col)
    if content == 0:
        return col
    paid = 1
    while (g := gcd(content, pay)) != 1:
        content //= g
        paid *= g
    return [x//paid for x in col]

def pivots_mod(a_rows, prime):
    a = [[v % prime for v in row] for row in a_rows]
    row_order, columns = list(range(len(a))), []
    h = 0
    for j in range(len(a[0])):
        k = next((k for k in range(h,len(a)) if a[k][j]),None)
        if k is None:
            continue
        columns.append(j)
        a[k],a[h] = a[h],a[k]
        row_order[k],row_order[h] = row_order[h],row_order[k]
        inv = pow(a[h][j],-1,prime)
        base = [(v*inv)%prime for v in a[h][j:]]
        for k in range(h+1,len(a)):
            coeff = a[k][j]
            if coeff:
                a[k][j:] = [(v-coeff*w)%prime for v,w in zip(a[k][j:],base,strict=True)]
        h += 1
        if h == len(a):
            break
    return row_order[:h], columns

def modular_bilattice(candidates, pay):
    """Compute the same kind of integral coordinate receipts via modular HNF.

    The small-prime projection is only a generator hint, verified by the final
    full-coordinate identities. No modular rank is trusted by the checker.
    """
    from sympy import Matrix
    from sympy.matrices.normalforms import hermite_normal_form

    a = [strip_paid(col,pay) for col in candidates]
    all_rows = [list(row) for row in zip(*a,strict=True)]
    for prime in (1000003,1000033,1000037):
        rows, cols = pivots_mod(all_rows,prime)
        if not cols:
            continue
        square = Matrix([[all_rows[i][j] for j in cols] for i in rows])
        det = abs(int(square.det(method="domain-ge")))
        projected = Matrix([all_rows[i] for i in rows])
        H = hermite_normal_form(projected,D=det)
        assert H.rows == H.cols == len(rows)
        coordinates_in_old = square.inv()*H
        ambient = Matrix([[r[j] for j in cols] for r in all_rows])*coordinates_in_old
        if not all(x.q==1 for x in ambient):
            continue
        basis = [strip_paid([int(ambient[i,j]) for i in range(ambient.rows)],pay)
                 for j in range(ambient.cols)]
        coefficients=[]
        for source in candidates:
            v, c = source, [0]*len(basis)
            for j in reversed(range(len(basis))):
                i = rows[j]
                z,rem = divmod(v[i],basis[j][i])
                if rem:
                    break
                c[j] = z
                if z:
                    v = add_scaled(v,1,basis[j],-z)
            if any(v):
                break
            coefficients.append(c)
        if len(coefficients)==len(candidates):
            return basis,coefficients
    raise ArithmeticError("no projected integer lattice with verified full coordinates")

def dot(a, b):
    return sum((x*y for x, y in zip(a, b, strict=True)), 0)

def matvec(a, v):
    return [dot(r,v) for r in a]

def native_attach(a0, d_f, n, v, w):
    return [u*n*aw for u,aw in zip(v[:-1],matvec(a0,w[:-1]),strict=True)] + [d_f*v[-1]*w[-1]]
