"""Build the signed-reverse paid explicit Runge–Kutta family with exact fractions."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import chain
import json
from math import factorial, gcd, lcm, prod
from pathlib import Path


HERE = Path(__file__).resolve().parent
SEED_SHA256 = '8d066b0962766081b81d29c5f2c8331c6f814ed137a440f04674cc71829b1c39'
Z, O = F(0), F(1)
PAID = factorial(13)


def paid_integer(n):
    while (d := gcd(abs(n), PAID)) > 1:
        n //= d
    return abs(n) == 1


def unit(x):
    return paid_integer(x.numerator) and paid_integer(x.denominator)


def dot(a, b):
    return sum((u * v for u, v in zip(a, b)), Z)


def pad(a, n):
    return a + [Z] * (n - len(a))


def basis(i, n):
    return [F(j == i) for j in range(n)]


def solve(matrix, target):
    """Solve exactly over Q and verify that the determinant is a paid unit."""
    m = [list(row) + [v] for row, v in zip(matrix, target)]
    det, n = O, len(target)
    for j in range(n):
        i = next(i for i in range(j, n) if m[i][j])
        if i != j:
            m[i], m[j], det = m[j], m[i], -det
        pivot = m[j][j]
        det *= pivot
        m[j] = [v / pivot for v in m[j]]
        for i in range(n):
            if i != j and (v := m[i][j]):
                m[i] = [u - v * w for u, w in zip(m[i], m[j])]
    assert unit(det), det
    return [row[-1] for row in m], det


def read(ops, rows, desired):
    """Represent a polynomial functional by a literal stage-vector read."""
    ns = len(ops)
    scalars, det = solve([[f(j) for f in ops] for j in range(ns)], [desired(j) for j in range(ns)])
    n = max(map(len, rows))
    return [dot(scalars, c) for c in zip(*(pad(r, n) for r in rows))], det


def eval_at(x):
    return lambda j: x ** j


def primitive_at(x):
    return lambda j: x ** (j + 1) / (j + 1)


def moment(k):
    return lambda j: F(1, j + k + 1)


def nodal(roots):
    coefficients = [O]
    for x in roots:
        coefficients = [s - x * t for s, t in zip([Z] + coefficients, coefficients + [Z])]
    return coefficients


def average(j):
    return Z if j % 2 else F(1, j + 1)


def omega_average(j):
    return average(j) - 2 * average(j + 2) + average(j + 4)


def merge(a, b):
    representatives, indices, rows, weights, mergers = [], {}, [], [], []
    assert len(a) == len(b)
    for i, (r, wt) in enumerate(zip(a, b)):
        assert len(r) <= i
        padded = [Z] * len(rows)
        for j, value in enumerate(r):
            padded[representatives[j]] += value
        key = tuple((j, value) for j, value in enumerate(padded) if value)
        if key not in indices:
            indices[key] = (len(rows), i+1)
            rows.append(key)
            weights.append(Z)
        j, original = indices[key]
        weights[j] += wt
        representatives.append(j)
        if i+1 != original:
            mergers.append((i+1,original))
    return rows, weights, mergers


def prepend(polys, new_x, a):
    ops, data = polys
    first = len(a)
    for x in new_x:
        a.append(read(ops, data, primitive_at(x))[0])
    return [eval_at(x) for x in new_x], [basis(i, len(a)) for i in range(first, len(a))]


def short(g):
    a = [list(map(F,r)) for r in [
        [],['1/3'],[0,'2/3'],['1/12','1/3','-1/12'],
        ['7/4',-9,'9/4',6],['-3/64','9/8','-9/64','-27/64','-1/64'],
        ['-65/4',81,'9/4',-33,-1,-32],
    ]]
    b = list(map(F,['11/120',0,'27/40','27/40','1/12','-8/15','1/120']))
    mo = [pad([w*sum(row)**k for w,row in zip(b,a)],8) for k in range(2)]
    a.append(b)
    e = ([eval_at(Z),eval_at(O)],[basis(0,8),basis(7,8)])
    om = (e[0]+[moment(0),moment(1)],e[1]+mo)
    mid = prepend(om,[F(1,2)],a)
    om5 = (om[0]+mid[0],om[1]+mid[1])
    if g==5:
        return a, *om5
    ne = prepend(om5,[F(2,3),F(5,6)],a)
    op6 = (om[0][:3]+mid[0]+ne[0],om[1][:3]+mid[1]+ne[1])
    if g==6:
        return a, *op6
    assert g==7
    ne = prepend(op6,[F(i,6) for i in (1,2,4,5)],a)
    contrast_weights = (F(81,4),F(-2187,64),F(2187,100))
    contrast_sites = (F(1,2),F(2,3),F(5,6))
    contrast = lambda j: dot(contrast_weights,[x**j for x in contrast_sites])
    return a, e[0]+ne[0]+[contrast], e[1]+ne[1]+[[Z]*8+list(contrast_weights)]


def eight_row_grade_five():
    a = [[], [F(1,4)], [Z,F(1,2)], [O,F(-2),F(2)]]
    a += [[F(v,6) for v in (1,0,4,1)],
          [F(v,162) for v in (11,48,-4,-5,4)],
          [F(v,162) for v in (19,0,-20,3,-2,54)],
          [F(v,3072) for v in (350,0,-328,26,-9,729,0)]]
    mix=list(map(F,(0,0,'-64/81','-4/81',0,1,0,0)))
    midpoint=[F(81,64)*(e7-F(4,81)*e5-r)
              for e7,e5,r in zip(basis(6,8),basis(4,8),mix)]
    x=list(map(F,(0,'1/4','1/3','1/2',1)))
    return a, [eval_at(v) for v in x], [basis(0,8),basis(7,8),basis(6,8),midpoint,basis(4,8)]


def long(g, reverse, seed, projected=False, reflected_twenty=False, symmetric_last=False, regular_grade8=False):
    a = [list(map(F,row)) for row in seed['A']]
    b = list(map(F,seed['b']))
    mo = [pad([w*sum(row)**k for w,row in zip(b,a)],17) for k in range(4)]
    a.append(b)
    e = ([eval_at(Z),eval_at(O)],[basis(0,17),basis(16,17)])
    op6 = (e[0]+[moment(j) for j in range(4)],e[1]+mo)
    mid = prepend(op6,[F(1,2)],a)
    quarter = [u-v for u,v in zip(basis(10,18),basis(9,18))]
    qc = lambda j: F(1,4)**j-F(3,4)**j
    op7 = (op6[0][:-1]+[qc]+mid[0],op6[1][:-1]+[quarter]+mid[1])
    x_of = lambda z: (1+z)/2
    if g==8 and not projected and not regular_grade8:
        ne = prepend(op7,list(map(F,['1/12','1/4','1/3','1/2'])),a)
        return a, op6[0][:4]+ne[0],op6[1][:4]+ne[1]
    if projected:
        z = list(map(F, ['-1/3','1/3','-1/5','5'] if reverse else ['-5','-1/3','1/5','1/3']))
    else:
        z = list(map(F, ['-1/3','1/3','1/2','-2'] if reverse else ['-1/3','1/3','3/5','-5/3']))
    if reflected_twenty and not reverse:
        z = list(map(F, ('-5','-1/3','1/5','1/3')))
    if regular_grade8:
        z = list(map(F, ('-1/3','1/3','-1/5','5') if reverse and projected else ('-1/3','1/3','1/5','-5') if not reverse else ('-1/3','1/3','1/2','-2')))
    xx = list(map(x_of,z))
    ne = prepend(op7,xx,a)
    op8 = (op6[0][:4]+ne[0],op6[1][:4]+ne[1])
    if regular_grade8:
        assert g==8
        return a,*op8
    if projected and not reverse:
        assert g==8
        return a,*op8
    def weighted_read(nodes, action):
        ans = []
        for z in nodes:
            others = [u for u in nodes if u != z]
            den = (1-z*z)**2*prod(z-u for u in others)
            assert unit(den)
            ans.append(action(nodal(others))/den)
        return ans
    ell4 = weighted_read(z,lambda poly: sum(c*omega_average(j) for j,c in enumerate(poly)))
    ell4p = lambda j: dot(ell4, [x**j for x in xx])
    if projected:
        assert reverse and g==9
        q = lambda v: (1-v*v)*(153*v**6-155*v**4+35*v*v-1-48*v*(17*v**4-10*v*v+1))
        anchor = F(2,3)
        d0 = q(F(1,3))
        assert unit(d0)
        anchor_lo = pad(a[19],22)
        anchor_hi = read(*op8,primitive_at(anchor))[0]
        operators = op6[0][:3]+[ell4p]
        rows = op6[1][:3]+[[Z]*18+ell4]
        for u in map(F,('-1/3','-1/5','-1/2','1/2')):
            x=x_of(u)
            d=q(u)/d0
            new=read(*op8,primitive_at(x))[0]
            a.append([v-d*(h-l) for v,h,l in zip(new,anchor_hi,anchor_lo)])
            operators.append(lambda j,x=x,d=d: x**j-d*anchor**j)
            rows.append([v-d*w for v,w in zip(basis(len(a)-1,len(a)),basis(19,len(a)))])
        return a,operators,rows
    z2 = list(map(F,['-1/3','1/3','1/2','-2/3','2/3'] if reverse else ['-8/3','-1/3','1/3','-2','2']))
    if reflected_twenty:
        z2 = list(map(F, ('-8/11','4/7','-2','1/2','0') if reverse else ('0','-1/3','1/3','-1/2','1/2')))
    if symmetric_last:
        assert reverse and g==9
        z2 = list(map(F, ('0','-1/3','1/3','-1/2','1/2')))
    xx2 = list(map(x_of,z2))
    ne2 = prepend(op8,xx2,a)
    op9 = (op6[0][:3]+[ell4p]+ne2[0],op6[1][:3]+[[Z]*18+ell4]+ne2[1])
    if g==9:
        return a,*op9
    assert g==10
    def derivative_of_omega(poly):
        # Differentiate (1-u^2)^2 times the centered polynomial.
        ext = [Z]*(len(poly)+4)
        for j,c in enumerate(poly):
            ext[j]+=c
            ext[j+2]-=2*c
            ext[j+4]+=c
        return sum(c*j*dot(ell4,[v**(j-1) for v in z]) for j,c in enumerate(ext) if j)
    ell5 = weighted_read(z2,derivative_of_omega)
    assert all(unit(v) for v in ell5)
    ell5p = lambda j: dot(ell5,[x**j for x in xx2])
    new = [x_of(v) for v in z2[1:] + [Z,F(-2,3),F(2,3)]]
    if reflected_twenty:
        new = list(map(x_of, map(F, ('0','-2','2','-1/2','1/2','-4/7','4/7'))))
    ne3 = prepend(op9,new,a)
    return a,e[0]+[ell5p]+ne3[0],e[1]+[[Z]*22+ell5]+ne3[1]


targets = {
    11:(5,5,12,0,12,(1,),28),
    12:(5,6,12,0,12,(),32),
    13:(6,6,18,0,18,(1,2,4,5,17),35),
    14:(6,7,18,0,18,(1,2,4,17),40),
    15:(7,7,18,0,18,(1,2,17),45),
    16:(8,7,18,0,18,(1,17),53),
    17:(9,7,18,0,18,(1,),59),
    18:(8,9,12,-6,18,(-5,-4,-3,-1,13,17),64),
    19:(9,9,12,-6,18,(-5,-4,-3,-2,17),73),
    20:(9,10,12,-6,18,(-5,-4,-3,17),79),
}


def construct(p,seed,rational_grid=False,previous=False,verify_reads=False):
    assert not rational_grid or p==19
    if 17 <= p <= 20 and not rational_grid and not previous:
        import sys
        from weighted_regular import build
        return build(sys.modules[__name__],seed,p,verify_reads=verify_reads)
    global PAID
    PAID=factorial(p)
    m,r,N,lo,hi,omit,count=targets[p]
    f,fo,fr = short(m) if m<8 else long(m,False,seed,projected=p==18,reflected_twenty=p==20 or rational_grid)
    rev,ro,rr = eight_row_grade_five() if p==11 else (short(r) if r<8 else long(r,r==9 or p==20,seed,projected=p==18,reflected_twenty=p==20,symmetric_last=rational_grid))
    k = len(rev)
    ys = [F(j,N) for j in range(lo,hi+1) if j not in omit]
    if 11<=p<=20:
        if p<=12:
            ys=[F(j,12) for j in range(13) if j not in (1,11)]
        elif p==13:
            ys=[F(j,12) for j in range(13)]
        elif p==14:
            ys=[F(j,18) for j in range(19) if j not in (1,2,4,14,16,17)]
        elif p in (15,16):
            ys=[F(j,18) for j in range(19) if j not in (1,2,16,17)]
        elif p==17:
            ys=[F(j,18) for j in range(19) if j not in (1,17)]
        elif p==18:
            ys=sorted({F(1,2)} | { (1+sg*F(v))/2 for sg in (-1,1)
                          for v in ('1/5','1/3','1/2','2/3','1','3/2','2','5')})
        elif p==20:
            ys=sorted({F(1,2)} | {(1+sg*F(v))/2 for sg in (-1,1)
                      for v in ('1/3','1/2','1','2','8/11','4/7','4/5','4/3','8/3')})
        else:
            ys=sorted({F(1,2)} | {F(6+s*j,12) for s in (-1,1) for j in (1,2,3,4,5,6,7,8,12)})
        if rational_grid:
            core = (F(1,3),F(1,2),O,F(2),F(2,3),F(5,6),F(3,2))
            centered = [Z] + [sign*u for u in core for sign in (-1,1)]
            centered += [F(1,5),F(1,7),F(-4932943,2026806)]
            ys = sorted((1+u)/2 for u in centered)
            assert len(set(ys))==18
        count=len(f)+len(rev)+len(ys)-1
    assert m+r+1==p and p<=2*m+2
    assert set(map(sum,rev))|{Z,O} <= set(ys)
    site_x = [1-y for y in ys]
    def quadrature(poly):
        return sum(c/(j+1) for j,c in enumerate(poly))
    lam=[]
    for x in site_x:
        others = [v for v in site_x if v!=x]
        den=prod(x-v for v in others)
        assert den and (rational_grid or unit(den))
        lam.append(quadrature(nodal(others))/den)
    L = rev + [row.copy() for row in rev] + [read(ro,rr,primitive_at(y))[0] for y in ys]
    beta = [O]*k+[-O]*k+lam
    T = [[beta[i]*L[i][j] if j<len(L[i]) and j<k else Z
          for i in range(len(L)-1,-1,-1)] for j in range(len(L)-1,-1,-1)]
    x = [O-sum(row,Z) for row in reversed(L)]
    a = list(f)
    for i,ti in enumerate(T):
        assert not any(ti[i:])
        li = lambda degree: primitive_at(x[i])(degree)-dot(ti,[xi**degree for xi in x])
        a.append(read(fo,fr,li)[0]+ti[:i])
    rows,b,mergers=merge(a,[Z]*len(f)+beta[::-1])
    if p==20 or rational_grid:
        expected = (27,27,18,70) if rational_grid else (27,34,19,78)
        assert (len(f),k,len(ys),len(rows)) == expected
        # Receiver order is reversed; the old endpoint is forward row 17.
        origin = len(f) + len(ys) - ys.index(O)
        endpoint = len(f) + len(ys) - ys.index(Z)
        assert (origin,1) in mergers and (endpoint,17) in mergers
    assert len(rows)<=count, (p,len(rows),count)
    if not rational_grid:
        for wi,row in zip(b,rows):
            assert paid_integer(wi.denominator)
            assert all(paid_integer(v.denominator) for _,v in row)
    c=[sum(v for _,v in row) for row in rows]
    for degree in range(p):
        assert dot(b,[x**degree for x in c])==(F(1,degree+1) if degree<p else 0)
    common=lcm(*(v.denominator for row in rows for _,v in row),*(v.denominator for v in b))
    result={'A':[[str(dict(row).get(j,Z)) for j in range(i)] for i,row in enumerate(rows)],
            'b':list(map(str,b)), 'coefficient_common_denominator': str(common)}
    print(f"p={p}: {len(f)} forward + {k} donors + {len(ys)-1} pure = {count} allocated; {len(rows)} distinct after {len(mergers)} merges.",
          file=__import__('sys').stderr)
    return json.dumps(result,indent=2)+'\n'


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('p',type=int,choices=tuple(targets))
    parser.add_argument('--seed',type=Path,default=HERE.parent/'erk-eleven-twelve-moment-splice'/'paid9-seed.json')
    parser.add_argument('--rational-grid',action='store_true',help='use the 70-stage rational grid at order 19')
    parser.add_argument('--previous',action='store_true',help='rebuild the earlier unweighted construction for orders 18–20')
    parser.add_argument('--verify-reads',action='store_true',help='verify all required weighted chart reads and first-excess pins (orders 17–20)')
    args=parser.parse_args()
    assert not args.verify_reads or (17<=args.p<=20 and not args.previous and not args.rational_grid)
    assert not args.previous or (18<=args.p<=20 and not args.rational_grid)
    seed_bytes=args.seed.read_bytes()
    assert sha256(seed_bytes).hexdigest()==SEED_SHA256
    print(construct(args.p,json.loads(seed_bytes),rational_grid=args.rational_grid,previous=args.previous,verify_reads=args.verify_reads),end='')
