"""Reconstruct the paid 56-stage ERK17 with live quadrature probes."""

import json
from fractions import Fraction as F
from math import factorial, lcm, prod
import sys


def build(rk, seed):
    rk.PAID = factorial(17)
    z, o = rk.Z, rk.O

    def vv(poly, x):
        return sum((v*x**i for i, v in enumerate(poly)), z)

    def scale(poly, x):
        return [x*v for v in poly]

    def add(a, b):
        n = max(len(a), len(b))
        return [x+y for x, y in zip(rk.pad(a,n), rk.pad(b,n))]

    def mul(a, b):
        values = [z]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                values[i+j] += x*y
        return values

    def mean(poly):
        return rk.dot(poly,[rk.average(i) for i in range(len(poly))])

    def cardinal(nodes, a):
        other = [b for b in nodes if b != a]
        den = prod(a-b for b in other)
        assert rk.unit(den)
        return scale(rk.nodal(other),o/den)

    def center_primitive(f):
        # Integral from y=0 to y=(v+1)/2 of f(2y-1).
        poly = [z] + [x/(2*(i+1)) for i,x in enumerate(f)]
        poly[0] = -vv(poly,-o)
        return poly

    fo_prefix, fo, fr = rk.long(9,False,seed)
    _, _, grade10_reads = rk.long(10,False,seed)
    old_ell5 = grade10_reads[2]
    fwd_ell5 = lambda poly: rk.dot(old_ell5[22:], [vv(poly,2*sum(row)-1) for row in fo_prefix[22:]])
    reverse, ro, rr = rk.short(6)
    base_n = len(reverse)
    grid = [F(i,9) for i in (-9,-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,9)]
    split = [F(i,9) for i in (-3,3,6)]
    early = [F(i,9) for i in (-6,-5,-4,-2,2,4,5)]
    late = [F(i,9) for i in (-7,-3,-1,0,1,3,6,7)]
    pure = [a for a in grid if a not in early]
    weight = {a:mean(cardinal(grid,a)) for a in grid}
    assert all(sum(weight[a]*a**j for a in grid)==rk.average(j) for j in range(18))
    assert {2*sum(r)-1 for r in reverse}.issubset(pure)

    def probe(v):
        return rk.read(ro,rr,rk.primitive_at((1+v)/2))[0]

    h = [o,z,-o]
    q = mul(h,rk.nodal([z,*split]))
    p = rk.nodal(list(map(F,('-1/9','1/9','-7/9','7/9'))))
    pivot = mean(mul(p,q))
    assert pivot==F(2560,3**11*11) and rk.unit(pivot)
    assert all(not vv(mul(p,q),a) for a in pure)
    live = base_n + len(split) + len(early)
    split_nodes = [z,*split]
    poly_pins = {v:mul(h,scale(cardinal(split_nodes,v),o/vv(h,v))) for v in split_nodes}

    old_eval = {a:rk.read(ro,rr,rk.eval_at((1+a)/2))[0] for a in split+early}

    def discrepancy(j):
        """Column j of D, with its known scalar mass removed at unsplit probes."""
        if j >= base_n+len(split):
            a = early[j-base_n-len(split)]
            return scale(q,vv(p,a)/pivot)

        def diff(a):
            if j < base_n:
                return -rk.pad(old_eval[a],base_n)[j]
            return F(a==split[j-base_n])

        sigma0 = [z]
        point = {v:diff(v) for v in split}
        point[z] = F(27,16)*point[F(1,3)]-F(27,25)*point[F(2,3)]
        for v in split_nodes:
            sigma0 = add(sigma0,scale(poly_pins[v],point[v]))
        numerator = sum((weight[a]*vv(p,a)*(diff(a)-vv(sigma0,a)) for a in early), z)
        return add(sigma0,scale(q,numerator/pivot))

    d_cols = [discrepancy(j) for j in range(live)]
    assert not any(sum((d_cols[j][i] if i<len(d_cols[j]) else z)
                       * (weight[early[j-base_n-len(split)]] if j>=base_n+len(split) else o)
                       for j in range(live)) for i in range(7))
    l = [r.copy() for r in reverse]+[probe(a) for a in split+early]
    beta = [o]*(base_n+len(split))+[weight[a] for a in early]
    l += [r.copy() for r in l[:base_n+len(split)]]
    beta += [-o]*(base_n+len(split))
    l += [probe(a) for a in pure]
    beta += [weight[a] for a in pure]
    weighted_columns = {}
    for a in late:
        e = mul(h,scale(cardinal(late,a),o/vv(h,a)))
        gamma = fwd_ell5([(-1)**i*x for i,x in enumerate(e)])
        base = rk.pad(probe(a),live)
        corrected = []
        for j,poly in enumerate(d_cols):
            d6 = poly[6] if len(poly)>6 else z
            correction = mean(mul(e,center_primitive(poly)))+128*gamma*d6
            if j>=base_n+len(split):
                weighted_columns[(len(l),j)] = correction
                scalar = weight[early[j-base_n-len(split)]]
            else:
                scalar = o
            corrected.append(base[j]+scalar*correction)
        l.extend([corrected,base])
        beta.extend([o,-o])
        assert sum(corrected)==(1+a)/2

    fwd = list(fo_prefix)
    x = [o-sum(row,z) for row in reversed(l)]
    for rev_j in reversed(range(len(l))):
        i = len(l)-1-rev_j
        t = []
        for rev_h in reversed(range(rev_j+1,len(l))):
            if rev_j<base_n+len(split):
                coeff = l[rev_h][rev_j] if rev_j<len(l[rev_h]) else z
            else:
                coeff = weighted_columns.get((rev_h,rev_j),z)
            primal = beta[rev_h]*coeff
            reverse_coeff = l[rev_h][rev_j] if rev_j<len(l[rev_h]) else z
            assert beta[rev_j]*primal == beta[rev_h]*reverse_coeff
            t.append(primal)
        corr = lambda n: rk.primitive_at(x[i])(n)-rk.dot(t,[v**n for v in x[:i]])
        fwd.append(rk.read(fo,fr,corr)[0]+t)
    out,b,mergers = rk.merge(fwd,[z]*len(fo_prefix)+beta[::-1])
    assert len(out)==56
    pure_start = live+base_n+len(split)
    raw_stage = lambda a: len(fo_prefix)+len(l)-pure_start-pure.index(a)
    assert (raw_stage(o),1) in mergers and (raw_stage(-o),17) in mergers
    c = [sum(v for _,v in row) for row in out]
    assert all(rk.dot(b,[v**j for v in c])==F(1,j+1) for j in range(17))
    common = lcm(*(v.denominator for row in out for _,v in row),*(v.denominator for v in b))
    assert rk.paid_integer(common)
    print(f"p=17: 56 physical rows after {len(mergers)} literal merges.",file=sys.stderr)
    result={'A':[[str(dict(row).get(j,z)) for j in range(i)] for i,row in enumerate(out)],
            'b':list(map(str,b)), 'coefficient_common_denominator':str(common)}
    return json.dumps(result,indent=2)+'\n'
