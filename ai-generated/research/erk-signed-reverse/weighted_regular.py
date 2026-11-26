"""Reconstruct paid ERK methods with live weighted quadrature probes."""

import json
from fractions import Fraction as F
from functools import cache
from itertools import combinations
from math import comb, factorial, gcd, lcm, prod
import sys


def build(rk, seed, order, verify_reads=False):
    rk.PAID = factorial(order)
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

    def paid_left_inverse(entries):

        def extended_gcd(a,b):
            if b==0:
                return abs(a), (1 if a>=0 else -1), 0
            g,x,y = extended_gcd(b,a%b)
            return g,y,x-(a//b)*y

        def determinant(matrix):
            if not matrix:
                return 1
            return sum((-1)**i*x*determinant([row[:i]+row[i+1:] for row in matrix[1:]])
                       for i,x in enumerate(matrix[0]))

        den = lcm(*(v.denominator for row in entries for v in row))
        assert rk.paid_integer(den)
        n = len(entries[0])
        subsets = list(combinations(range(len(entries)),n))
        matrices = [[[int(x*den) for x in entries[i]] for i in indices] for indices in subsets]
        g, blend = 0, []
        seen = []
        for indices, mat in zip(subsets, matrices):
            d = determinant(mat)
            if not d:
                continue
            unpaid = d
            while (u := gcd(abs(unpaid),rk.PAID))>1:
                unpaid //= u
            g,x,y = extended_gcd(g,unpaid)
            blend = [x*v for v in blend]+[F(y*unpaid,d)]
            seen.append((indices,mat))
            if g == 1:
                break
        assert g == 1, (order,g)
        if verify_reads:
            active = sum(bool(x) for x in blend)
            print(f"Order {order}: {len(entries)} weights, {n} unknowns, "
                  f"{active} maximal minors in the unit certificate.",file=sys.stderr)
        outputs = [[z]*len(entries) for _ in range(n)]
        for weight,(indices,mat) in zip(blend,seen):
            if not weight:
                continue
            for i in range(n):
                for j in range(n):
                    sub = [r[:i]+r[i+1:] for k,r in enumerate(mat) if k!=j]
                    cofactor = (-1)**(i+j)*determinant(sub)
                    outputs[i][indices[j]] += weight*den*cofactor
        return outputs

    def center_primitive(f):
        # Integral from y=0 to y=(v+1)/2 of f(2y-1).
        poly = [z] + [x/(2*(i+1)) for i,x in enumerate(f)]
        poly[0] = -vv(poly,-o)
        return poly

    if order<17:
        from weighted_middle import prepare
        (fo_prefix,fo,fr,fgrade,fwd_pin,high_fwd_row,hf,
         reverse,ro,rr,top,boundary,old_pins,hr,grid,split,early,late,injection) = prepare(
             rk,order,vv,mul,add,scale,cardinal)
    else:
        fgrade = 8 if order==18 else 9
        fo_prefix, fo, fr = rk.long(fgrade,False,seed,regular_grade8=order==18)
        if order==18:
            fwd_pin = mean
        else:
            _, _, grade10_reads = rk.long(10,False,seed)
            old_ell5 = grade10_reads[2]
            fwd_pin = lambda poly: rk.dot(old_ell5[22:], [vv(poly,2*sum(row)-1) for row in fo_prefix[22:]])

        if order==17:
            reverse, ro, rr = rk.short(6)
            grid = [F(i,9) for i in (-9,-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,9)]
            split = []
            early = [F(i,9) for i in (-6,-5,-4,-2,2,4,5)]
            late = [F(i,9) for i in (-7,-3,-1,0,1,3,6,7)]
        elif order in (18,19):
            reverse, ro, rr = rk.long(8,True,seed,projected=order==18,regular_grade8=True)
            core = tuple(map(F, ('1/5','1/3','1/2','2/3','1','3/2','2','5'))) if order==18 else tuple(F(i,6) for i in (1,2,3,4,5,6,7,8,12))
            grid = sorted([z] + [sign*i for i in core for sign in (-1,1)])
            split = [F(-1,3)] if order==18 else []
            old = {2*sum(r)-1 for r in reverse}
            preserve = [F(1,6)] if order==19 else []
            early = [a for a in grid if a not in old and a not in preserve]
            late = sorted((old-{-o,o}-({F(-1,5),F(5)} if order==18 else set()))|set(preserve))
        else:
            reverse, ro, rr = rk.long(9,True,seed,symmetric_last=True)
            grid = sorted([z] + [F(sign*i,6) for i in (1,2,3,4,5,6,7,8,12)
                                 for sign in (-1,1)])
            split = [z]
            old = {2*sum(row)-1 for row in reverse}
            early = [a for a in grid if a not in old and a!=F(1,6)]
            late = sorted((old-{-o,o})|{F(1,6)})

    assert len(late)==(fgrade if order in (15,16) else fgrade-1)
    base_n = len(reverse)
    pure = [a for a in grid if a not in early]
    weight = {a:mean(cardinal(grid,a)) for a in grid}
    assert all(sum(weight[a]*a**j for a in grid)==rk.average(j) for j in range(order+(order in (17,19))))
    assert {2*sum(r)-1 for r in reverse}.issubset(pure)

    def probe(v):
        return rk.read(ro,rr,rk.primitive_at((1+v)/2))[0]

    h = [o,z,-o]
    live = base_n+len(split)+len(early)
    if order>=17:
        top = {17:6,18:8,19:8,20:9}[order]
        injection = {17:128,18:-256,19:512,20:-1024}[order]
    adjust = lambda poly: poly
    middle_rules = None
    if order<17:
        axes = [[z]*j+boundary for j in range(top-len(boundary)+2)]
        rows = [[pin(q) for q in axes] for pin in old_pins]
        rows += [[vv(q,a) for q in axes] for a in split]
        rows += [[weight[a]*vv(q,a) for q in axes] for a in early]
        inverse = paid_left_inverse(rows)
        for i,row in enumerate(inverse):
            for j in range(len(axes)):
                assert sum(x*r[j] for x,r in zip(row,rows))==F(i==j)
        middle_rules = list(zip(axes,(dict(zip(split+early,row[len(old_pins):])) for row in inverse)))
        split_nodes = split
    elif order==17:
        split_nodes = split
        axes = [[z]*j+h for j in range(5)]
        entries = [[weight[a]*vv(q,a) for q in axes] for a in early]
        rules = list(zip(axes, (dict(zip(early,row)) for row in paid_left_inverse(entries))))
    elif order==18:
        old4 = list(map(F, ('-1/3','1/3','-1/5','5')))
        ell = {a:mean(mul(mul(h,h),cardinal(old4,a)))/vv(h,a)**2 for a in old4}
        split_nodes = split
        basis = [mul([z]*j+h,rk.nodal(split_nodes)) for j in range(6)]
        def ell_value(poly):
            return sum(w*vv(poly,a) for a,w in ell.items())
        def tests(poly):
            return mean(poly),ell_value(poly)
        test_rows = [tests(poly) for poly in basis]
        def d(i,j):
            return test_rows[i][0]*test_rows[j][1]-test_rows[i][1]*test_rows[j][0]
        pivot_a,pivot_b = next((i,j) for i,j in combinations(range(len(basis)),2) if rk.unit(d(i,j)))
        det = d(pivot_a,pivot_b)
        if verify_reads:
            print(f"Order 18: constraint pivots {pivot_a}, {pivot_b}, determinant {det}.",file=sys.stderr)

        def adjust(poly):
            a,b = tests(poly)
            phi = (a*test_rows[pivot_b][1]-b*test_rows[pivot_b][0])/det
            chi = (test_rows[pivot_a][0]*b-test_rows[pivot_a][1]*a)/det
            return add(poly,add(scale(basis[pivot_a],-phi),scale(basis[pivot_b],-chi)))

        assert tests(adjust(h)) == (z,z)
        axes = [adjust(poly) for k,poly in enumerate(basis) if k not in (pivot_a,pivot_b)]
        entries = [[weight[a]*vv(q,a) for q in axes] for a in early]
        rows = paid_left_inverse(entries)
        rules = list(zip(axes, (dict(zip(early,row)) for row in rows)))
    elif order==19:
        split_nodes = []
        axes = [add([z]*j+h,scale(h,-mean([z]*j+h)/mean(h))) for j in range(1,7)]
        entries = [[weight[a]*vv(q,a) for q in axes] for a in early]
        rows = paid_left_inverse(entries)
        rules = list(zip(axes, (dict(zip(early,row)) for row in rows)))
    else:
        split_nodes = split
        axes = [[z]*j+h for j in range(1,8)]
        entries = [[weight[a]*vv(q,a) for q in axes] for a in early]
        rows = paid_left_inverse(entries)
        rules = list(zip(axes, (dict(zip(early,row)) for row in rows)))

    if order>=17:
        for i, (q,p) in enumerate(rules):
            assert all(rk.paid_integer(c.denominator) for c in p.values())
            for j,(q2,_) in enumerate(rules):
                assert sum(weight[a]*p[a]*vv(q2,a) for a in early)==F(i==j)
        if order in (18,19):
            assert all(mean(q)==0 for q,p in rules)
        poly_pins = {v:mul(h,scale(cardinal(split_nodes,v),o/vv(h,v))) for v in split_nodes}

    if verify_reads:
        def center_power(n):
            return [F(comb(n,i),2**n) for i in range(n+1)]

        for chart, grade, ops, reads in (
            (fo_prefix, fgrade, fo, fr), (reverse, top, ro, rr)
        ):
            assert rk.unit(rk.read(ops, reads, rk.eval_at(z))[1])
            _verify_chart(chart, grade, ops, reads, rk)
        if order<17:
            _verify_chart(fo_prefix,fgrade+1,[f for f,_ in hf]+[lambda j:fwd_pin(center_power(j))],
                          [r for _,r in hf]+[high_fwd_row],rk,only_top=True)
            _verify_chart(reverse,top+1,[f for f,_ in hr],[r for _,r in hr],rk,only_top=True)
        else:
            f_high_ops = [rk.eval_at(z),rk.eval_at(o),lambda j:fwd_pin(center_power(j))]
            f_high_rows = fr[:2]+([fr[2]] if order==18 else [old_ell5])
            _verify_chart(fo_prefix, fgrade+1, f_high_ops, f_high_rows, rk, only_top=True)
            if order==17:
                _, high_ops, high_rows = rk.short(7)
                r_high_ops = high_ops[:2]+[high_ops[-1]]
                r_high_rows = high_rows[:2]+[high_rows[-1][:base_n]]
            elif order==18:
                r_high_ops = ro[:3]+[lambda j:sum(w*((1+a)/2)**j for a,w in ell.items())]
                r_high_rows = rr[:3]+[[z]*18+[ell[a] for a in old4]]
            elif order==19:
                r_high_ops = ro[:3]
                r_high_rows = rr[:3]
            else:
                r_high_ops = ro[:2]
                r_high_rows = rr[:2]
            _verify_chart(reverse, top+1, r_high_ops, r_high_rows, rk, only_top=True)

    old_eval = {a:rk.read(ro,rr,rk.eval_at((1+a)/2))[0] for a in split+early}

    def discrepancy(j):
        """Column j of D, with its known scalar mass removed at unsplit probes."""
        if middle_rules is not None:
            ans = [z]
            for q, coeff in middle_rules:
                if j>=base_n+len(split):
                    value = coeff[early[j-base_n-len(split)]]
                elif j>=base_n:
                    value = coeff[split[j-base_n]]
                else:
                    value = -sum((weight[a] if a in early else o)*coeff[a]
                                 *rk.pad(old_eval[a],base_n)[j] for a in split+early)
                ans = add(ans,scale(q,value))
            return ans
        if j>=base_n+len(split):
            a = early[j-base_n-len(split)]
            values = [z]
            for q,p in rules:
                values = add(values,scale(q,p[a]))
            return values

        def diff(a):
            if j<base_n:
                return -rk.pad(old_eval[a],base_n)[j]
            return F(a==split[j-base_n])

        sigma0 = [z]
        point = {v:diff(v) for v in split}
        for v in split_nodes:
            sigma0 = add(sigma0,scale(poly_pins[v],point[v]))
        sigma0 = adjust(sigma0)
        model = sigma0
        for q,p in rules:
            coeff = sum((weight[a]*p[a]*(diff(a)-vv(sigma0,a)) for a in early),z)
            model = add(model,scale(q,coeff))
        return model

    d_cols = [discrepancy(j) for j in range(live)]
    assert not any(sum((d_cols[j][i] if i<len(d_cols[j]) else z)
                       * (weight[early[j-base_n-len(split)]] if j>=base_n+len(split) else o)
                       for j in range(live)) for i in range(top+1))
    l = [r.copy() for r in reverse]+[probe(a) for a in split+early]
    beta = [o]*(base_n+len(split))+[weight[a] for a in early]
    l += [r.copy() for r in l[:base_n+len(split)]]
    beta += [-o]*(base_n+len(split))
    l += [probe(a) for a in pure]
    beta += [weight[a] for a in pure]
    weighted_columns = {}
    for a in late:
        forward_factor = [o,-o] if order in (15,16) else h
        e = mul(forward_factor,scale(cardinal(late,a),o/vv(forward_factor,a)))
        assert len(e)+top<=order-1
        gamma = fwd_pin([(-1)**i*x for i,x in enumerate(e)])
        base = rk.pad(probe(a),live)
        corrected = []
        for j,poly in enumerate(d_cols):
            high = poly[top] if len(poly)>top else z
            correction = mean(mul(e,center_primitive(poly)))+injection*gamma*high
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
    assert len(out)=={11:23,12:26,13:30,14:33,15:40,16:45,17:53,18:60,19:66,20:72}[order]
    pure_start = live+base_n+len(split)
    raw_stage = lambda a: len(fo_prefix)+len(l)-pure_start-pure.index(a)
    assert (raw_stage(o),1) in mergers
    if order not in (15,16):
        assert (raw_stage(-o),8 if order<=14 else 17) in mergers
    if order==11:
        assert (raw_stage(z),9) in mergers
    c = [sum(v for _,v in row) for row in out]
    assert all(rk.dot(b,[v**j for v in c])==F(1,j+1) for j in range(order))
    common = lcm(*(v.denominator for row in out for _,v in row),*(v.denominator for v in b))
    assert rk.paid_integer(common)
    print(f"p={order}: {len(out)} physical rows after {len(mergers)} literal merges.",file=sys.stderr)
    result={'A':[[str(dict(row).get(j,z)) for j in range(i)] for i,row in enumerate(out)],
            'b':list(map(str,b)), 'coefficient_common_denominator':str(common)}
    return json.dumps(result,indent=2)+'\n'

@cache
def _forests(n, lower=(0, ())):
    if n==0:
        return ((),)
    return tuple((t,)+tail for k in range(max(1,lower[0]),n+1)
                 for t in _forests(k-1) if (k,t)>=lower
                 for tail in _forests(n-k,(k,t)))


@cache
def _size(tree):
    return 1+sum(map(_size,tree))


@cache
def _tree_factorial(tree):
    return _size(tree)*prod(map(_tree_factorial,tree))


def _verify_chart(a, grade, ops, reads, rk, *, only_top=False):
    @cache
    def phi(tree):
        children = [[rk.dot(row,phi(t)) for row in a] for t in tree]
        return [prod(v[i] for v in children) for i in range(len(a))]

    sizes = (grade,) if only_top else range(1,grade+1)
    count = 0
    for n in sizes:
        for t in _forests(n-1):
            for op,row in zip(ops,reads):
                assert rk.dot(row,phi(t))==F(n,_tree_factorial(t))*op(n-1)
            count += 1
    print(f"{len(a)} rows: all {count} tree columns tested at grades {sizes}.",file=sys.stderr)
