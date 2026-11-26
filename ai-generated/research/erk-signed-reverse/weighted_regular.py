"""Reconstruct paid ERK methods with live weighted quadrature probes."""

import json
from fractions import Fraction as F
from functools import cache
from math import comb, factorial, lcm, prod
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

    def two_mode_reads(axes, tests):
        entries = [[mean(mul(t,q)) for q in axes] for t in tests]

        def extended_gcd(a,b):
            if b==0:
                return abs(a), (1 if a>=0 else -1), 0
            g,x,y = extended_gcd(b,a%b)
            return g,y,x-(a//b)*y

        den = lcm(*(v.denominator for row in entries for v in row))
        assert rk.paid_integer(den)
        pairs = [(0,1),(1,2),(0,2)]
        determinants = [(entries[i][0]*entries[j][1]-entries[i][1]*entries[j][0])*den**2 for i,j in pairs]
        assert all(v.denominator==1 for v in determinants)
        g,x,y = extended_gcd(int(determinants[0]),int(determinants[1]))
        g,u,v = extended_gcd(g,int(determinants[2]))
        assert rk.paid_integer(g)
        blend = [F(u*x*den**2,g),F(u*y*den**2,g),F(v*den**2,g)]
        p1,p2 = [z],[z]
        for a,(i,j) in zip(blend,pairs):
            p1 = add(p1,scale(add(scale(tests[i],entries[j][1]),scale(tests[j],-entries[i][1])),a))
            p2 = add(p2,scale(add(scale(tests[j],entries[i][0]),scale(tests[i],-entries[j][0])),a))
        return list(zip(axes, (p1,p2)))

    def center_primitive(f):
        # Integral from y=0 to y=(v+1)/2 of f(2y-1).
        poly = [z] + [x/(2*(i+1)) for i,x in enumerate(f)]
        poly[0] = -vv(poly,-o)
        return poly

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
        split = [F(i,9) for i in (-3,3,6)]
        early = [F(i,9) for i in (-6,-5,-4,-2,2,4,5)]
        late = [F(i,9) for i in (-7,-3,-1,0,1,3,6,7)]
    elif order in (18,19):
        reverse, ro, rr = rk.long(8,True,seed,projected=order==18,regular_grade8=True)
        core = tuple(map(F, ('1/5','1/3','1/2','2/3','1','3/2','2','5'))) if order==18 else tuple(F(i,6) for i in (1,2,3,4,5,6,7,8,12))
        grid = sorted([z] + [sign*i for i in core for sign in (-1,1)])
        split = [F(-1,3),F(1,3)] + ([F(-1,5)] if order==18 else [F(1,2),z])
        old = {2*sum(r)-1 for r in reverse}
        preserve = [F(1,6)] if order==19 else []
        early = [a for a in grid if a not in old and a not in preserve]
        late = sorted((old-{-o,o}-({F(-1,5),F(5)} if order==18 else set()))|set(preserve))
    else:
        reverse, ro, rr = rk.long(9,True,seed,symmetric_last=True)
        grid = sorted([z] + [F(sign*i,6) for i in (1,2,3,4,5,6,7,8,12)
                             for sign in (-1,1)])
        split = list(map(F, ('-1/3','1/3','-1/2','1/2')))
        old = {2*sum(row)-1 for row in reverse}
        early = [a for a in grid if a not in old and abs(a)!=F(1,6)]
        late = sorted((old-{-o,o})|{F(1,6)})

    assert len(late)==fgrade-1
    base_n = len(reverse)
    pure = [a for a in grid if a not in early]
    weight = {a:mean(cardinal(grid,a)) for a in grid}
    assert all(sum(weight[a]*a**j for a in grid)==rk.average(j) for j in range(order))
    assert {2*sum(r)-1 for r in reverse}.issubset(pure)

    def probe(v):
        return rk.read(ro,rr,rk.primitive_at((1+v)/2))[0]

    h = [o,z,-o]
    live = base_n+len(split)+len(early)
    top = {17:6,18:8,19:8,20:9}[order]
    injection = {17:128,18:-256,19:512,20:-1024}[order]
    if order==17:
        split_nodes = [z,*split]
        missing, rest = z, None
        q = mul(h,rk.nodal(split_nodes))
        p = rk.nodal(list(map(F,('-1/9','1/9','-7/9','7/9'))))
        axis = mean(mul(p,q))
        assert axis==F(2560,3**11*11) and rk.unit(axis)
        rules = [(q,scale(p,o/axis))]
    elif order in (18,19):
        missing = F(5) if order==18 else F(-2)
        split_nodes = [*split,missing]
        old4 = [*split[:3],missing]
        ell = {a:mean(mul(mul(h,h),cardinal(old4,a)))/vv(h,a)**2 for a in old4}
        assert rk.unit(ell[missing])
        f = scale(mul(h,rk.nodal(old4)),-o)
        if order==19:
            rest = mul([z,o],f)
            assert mean(rest)==F(-60,945) and rk.unit(mean(rest))
            q = mul([z,F(4,15),o],f)
            r = rk.nodal([F(-1,2),F(2),F(1,6)])
            projection = mul(r,[F(2509*22275)-F(20*405405*4,9),-F(20*405405)])
            rules = [(q,projection)]
        else:
            rest = f
            assert rk.unit(mean(rest))
            q1 = mul([-F(12),o],f)
            q2 = mul([-o,z,o],f)
            r = rk.nodal(list(map(F, ('0','-1/2','1/2','-2','2'))))
            tests = [r,[z,z]+r,[z,z,z,z]+r]
            rules = two_mode_reads((q1,q2), tests)
    else:
        rest = missing = None
        split_nodes = split
        q = scale(mul(h,rk.nodal(split_nodes)),-o)
        mask = rk.nodal([z,F(-2),F(2),F(-1,6),F(1,6)])
        # q times mask is odd. Even tests read the odd powers and conversely.
        odd = ( [z]+q, [z,z,z]+q )
        even = ( q, [z,z]+q )
        rules = two_mode_reads(odd, [[z]*j+mask for j in (0,2,4)])
        rules += two_mode_reads(even, [[z]*j+mask for j in (1,3,5)])

    for i, (q,p) in enumerate(rules):
        assert len(q)+len(p)-2<=order-1
        assert mean(mul(q,p))==o
        assert all(not vv(mul(q,p),a) for a in pure)
        assert all(mean(mul(q2,p))==F(i==j) for j,(q2,_) in enumerate(rules))
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
        f_high_ops = [rk.eval_at(z),rk.eval_at(o),lambda j:fwd_pin(center_power(j))]
        f_high_rows = fr[:2]+([fr[2]] if order==18 else [old_ell5])
        _verify_chart(fo_prefix, fgrade+1, f_high_ops, f_high_rows, rk, only_top=True)
        if order==17:
            _, high_ops, high_rows = rk.short(7)
            r_high_ops = high_ops[:2]+[high_ops[-1]]
            r_high_rows = high_rows[:2]+[high_rows[-1][:base_n]]
        elif order in (18,19):
            r_high_ops = ro[:3]+[lambda j:sum(w*((1+a)/2)**j for a,w in ell.items())]
            r_high_rows = rr[:3]+[[z]*18+[ell[a] for a in old4]]
        else:
            r_high_ops = ro[:2]
            r_high_rows = rr[:2]
        _verify_chart(reverse, top+1, r_high_ops, r_high_rows, rk, only_top=True)

    old_eval = {a:rk.read(ro,rr,rk.eval_at((1+a)/2))[0] for a in split+early}

    def discrepancy(j):
        """Column j of D, with its known scalar mass removed at unsplit probes."""
        if j>=base_n+len(split):
            a = early[j-base_n-len(split)]
            values = [z]
            for q,p in rules:
                values = add(values,scale(q,vv(p,a)))
            return values

        def diff(a):
            if j<base_n:
                return -rk.pad(old_eval[a],base_n)[j]
            return F(a==split[j-base_n])

        sigma0 = [z]
        point = {v:diff(v) for v in split}
        if order==17:
            point[missing] = F(27,16)*point[F(1,3)]-F(27,25)*point[F(2,3)]
        elif missing is not None:
            point[missing] = -sum(ell[v]*point[v] for v in old4 if v!=missing)/ell[missing]
        for v in split_nodes:
            sigma0 = add(sigma0,scale(poly_pins[v],point[v]))
        if rest is not None:
            sigma0 = add(sigma0,scale(rest,-mean(sigma0)/mean(rest)))
        for q,p in rules:
            read = sum((weight[a]*vv(p,a)*(diff(a)-vv(sigma0,a)) for a in early),z)
            sigma0 = add(sigma0,scale(q,read))
        return sigma0

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
        e = mul(h,scale(cardinal(late,a),o/vv(h,a)))
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
    assert len(out)=={17:56,18:62,19:70,20:75}[order]
    pure_start = live+base_n+len(split)
    raw_stage = lambda a: len(fo_prefix)+len(l)-pure_start-pure.index(a)
    assert (raw_stage(o),1) in mergers and (raw_stage(-o),17) in mergers
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
