#!/usr/bin/env python3
"""Standalone rational replay for the 70-stage factorial-unit order-20 ERK witness.

Requires a read-only checkout containing the pinned published construct.py and
seed. This module performs no network requests and creates no files. It prints
a tableau to stdout only on explicit request and after the full exact audit.
Python 3.10+; standard library only.

The output digest is checked against the original literal tableau. The
optional reference receipt verifies the earlier forward and reverse charts
before checking the new stage folds and order conditions.
"""
import argparse
import hashlib
import importlib.util
import json
import math
import sys
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from pathlib import Path

sys.dont_write_bytecode = True
P = 20
M = G = 9
PAY = math.factorial(P)
Z, ONE = Q(0), Q(1)
H = [ONE, Z, -ONE]
LEFT = [ONE, -ONE]
PINS = tuple(map(Q, (-2487, -6632, 1473, 3928, 5433, 14488, 9393, 25048)))
S = tuple(map(Q, ("-2", "-1/2", "-1/3", "0", "1/3", "1/2", "2")))
S1 = (-ONE,) + S                         # Deliberate chronology, not sorted.
OLD = set(S) | {-ONE, ONE}
E = tuple(map(Q, ("1/6", "2/3", "5/6", "7/6", "3/2")))
B = tuple(map(Q, ("-4/3", "-5/6", "-2/3", "-1/6", "1/6", "2/3", "5/6",
                  "7/6", "3/2", "5/3", "13/6")))
H_LIVE = tuple(a for a in B if a not in E)
CENTERS = E + H_LIVE                     # Physical reverse chronology.
MASS_CORES = (25296799769, 1126380326711, 377568187, 6800022679,
              55633553, 714198643859, 4704931657, 1963953983,
              1850816909, 501344707, 1498008689)
SOURCE_PINS = {
    "construct.py": "74ee0b15daa00996a506ecb2c1fc09a5ebc979e35f26c74eed368b1104dc21c7",
    "weighted_middle.py": "54e072af8ad1a3c254f627e1871ea9db0d44bee41857e57660f267ebd74788ec",
    "../erk-eleven-twelve-moment-splice/paid9-seed.json":
        "8d066b0962766081b81d29c5f2c8331c6f814ed137a440f04674cc71829b1c39",
    "order-20-factorial-71/tableau-20-factorial-71.json":
        "cf0a69fa34755720e00e907ebfdce193c0180b8416c5efc4ff06c6014d2a2cc3",
}
LITERAL_SHA = "172b4074ca84dc5546907eacc434780a980662b1bfaa51c99e6b43ecab2e5e44"
HISTORICAL_RECEIPT_SHA = "30436e2f7643d6740a9419c778e26d03f6194021f9919f9f9881f6fc7e72eec2"
PRIOR_RECEIPT_SHA = "0ae5e7485fd9e2f9de0c8567322bfcc2c6660234e0de7511030727e89d17b40d"
D_EXPECT = 50910225475883910757171941895464960000000000
E_EXPECT = 2127745531711800000
QG = tuple(tuple(map(Q, row)) for row in (
    ("0", "-1/9", "0", "11/9", "0", "-19/9", "0", "1", "0"),
    ("0", "1/6", "-1/15", "-5/3", "7/9", "3/2", "-77/45", "0", "1"),
))
MASKS = tuple(tuple(map(Q, row)) for row in (
    (
        "41299030599546259497674925784895/738978552",
        "-8404694504991986824096876736535053/20535825024",
        "1629981814803037649491996037042149/9095120640",
        "448573324557054237238781551199573273/225104235840",
        "-8297572781521355277939010878807252953/3901806754560",
        "-14645093992722208954586089623051464089/5852710131840",
        "147443777034574275157910308564136227/37517372640",
        "151123470487664396220093337165271/694766160",
        "-19125839465485718539029911170003/9382230",
        "166685403377738391710823297981433/237683160",
        "-1",
    ),
    (
        "10397339093372404414588935600274471/35470970496",
        "-330616336040454419203432218279434029/154018687680",
        "769425156527943972286575410708529251/818560857600",
        "141164601685358000083401182802669492233/13506254150400",
        "-1305609910949741531808566474344019269889/117054202636800",
        "-2304382301565404734353051183366133777337/175581303955200",
        "23200044359105766710677421604459431981/1125521179200",
        "7926346095058055415768646941004441/6947661600",
        "-24075363934843088810153299933286917/2251735200",
        "26227683732438336366692798321078009/7130494800",
        "0",
        "-1",
    ),
))

def pad(v, n):
    assert len(v) <= n
    return list(v) + [Z] * (n - len(v))


def dot(u, v):
    return sum((a * b for a, b in zip(u, v, strict=True)), Z)


def tr(A):
    return [list(v) for v in zip(*A, strict=True)]


def act(A, v):
    return [dot(r, v) for r in A]


def mat(A, B):
    return [act(tr(B), r) for r in A]


def scale(v, c):
    return [a * c for a in v]


def plus(u, v):
    n = max(len(u), len(v))
    return [a+b for a, b in zip(pad(u,n), pad(v,n), strict=True)]


def prod_poly(u, v):
    w = [Z]*(len(u)+len(v)-1)
    for i, a in enumerate(u):
        for j, b in enumerate(v):
            w[i+j] += a*b
    return w


def ev(f, a):
    return sum((c*a**i for i,c in enumerate(f)), Z)


def hull(nodes):
    q = [ONE]
    for a in nodes:
        q = prod_poly(q, [-a, ONE])
    return q


def mean(f):
    return sum((a/(i+1) for i,a in enumerate(f) if i % 2 == 0), Z)


def integral(f):
    r = [Z] + [a/(2*(i+1)) for i,a in enumerate(f)]
    r[0] = -ev(r, -ONE)
    return r


def centered(f, reflect=False):
    """Change y=(1+v)/2; reflect=True uses x=(1-v)/2 instead."""
    return [sum((a*Q(math.comb(j,i),2**j) for j,a in enumerate(f) if j>=i), Z)
            * (-1 if reflect and i%2 else 1) for i in range(len(f))]


def in_y(f):
    """Convert centered v coefficients to y coefficients."""
    return [sum((a*math.comb(j,i)*2**i*(-1)**(j-i)
                 for j,a in enumerate(f) if j>=i),Z) for i in range(len(f))]


def h_div(f):
    q = []
    for i, v in enumerate(f[:-2]):
        q.append(v + (q[i-2] if i>=2 else 0))
    assert prod_poly(q,H) == list(f)
    return q


def strip_int(n):
    assert n
    while (d := math.gcd(n, PAY)) != 1:
        n //= d
    return n


def paid(x):
    return strip_int(Q(x).denominator) == 1


def unit(x):
    x = Q(x)
    return bool(x) and paid(x) and abs(strip_int(x.numerator)) == 1


def int_lcm(rows):
    return math.lcm(*(Q(a).denominator for row in rows for a in row))


def card(nodes, a):
    f = hull(b for b in nodes if b != a)
    d = ev(f,a)
    assert unit(d)
    return scale(f, 1/d)


def det(A):
    """Signed fraction-free determinant of an integer square matrix."""
    if not A:
        return 1
    B0 = [list(r) for r in A]
    prev, sign = 1, 1
    for j in range(len(B0)-1):
        i = next((i for i in range(j,len(B0)) if B0[i][j]), None)
        if i is None:
            return 0
        if i != j:
            B0[i], B0[j] = B0[j], B0[i]
            sign = -sign
        b0 = B0[j][j]
        for i in range(j+1,len(B0)):
            c0 = B0[i][j]
            for k in range(j+1,len(B0)):
                a0 = b0*B0[i][k] - c0*B0[j][k]
                assert a0 % prev == 0
                B0[i][k] = a0//prev
            B0[i][j] = 0
        prev = b0
    return sign*B0[-1][-1]


def egcd(a, b):
    """Positive gcd and the Python floor-division signed Euclidean coefficients."""
    if not b:
        return abs(a), (1 if a >= 0 else -1), 0
    g,x,y = egcd(b, a % b)
    return g, y, x-(a//b)*y


def left_inverse(A):
    """Deterministic paid adjugate combination, no individual mass inversion."""
    n, m = len(A[0]), len(A)
    d = int_lcm(A)
    assert paid(Q(1,d))
    Ai = [[int(a*d) for a in row] for row in A]
    sub = []
    for ids in combinations(range(m), n):
        rows = [Ai[i] for i in ids]
        v = det(rows)
        if v:
            core = strip_int(v)
            sub.append((abs(core),ids,rows,v,core))
    sub.sort(key=lambda t:(t[0],t[1]))
    g, chosen, coeffs = 0, [], []
    for _, ids, rows, v, core in sub:
        if math.gcd(g,core)==g:
            continue
        g,a,b = egcd(g,core)
        coeffs = [a*c for c in coeffs]+[b]
        chosen.append((ids,rows,v,core))
        if g==1:
            break
    assert g==1
    out = [[Z]*m for _ in range(n)]
    for (ids, rows, v, core), b in zip(chosen,coeffs,strict=True):
        for i in range(n):
            for j in range(n):
                minor = [[a for k,a in enumerate(row) if k!=i]
                         for h,row in enumerate(rows) if h!=j]
                out[i][ids[j]] += Q(d*core*b*(-1)**(i+j)*det(minor),v)
    assert all(paid(a) for r in out for a in r)
    assert mat(out,A)==[[Q(i==j) for j in range(n)] for i in range(n)]
    return out, [(ids,v,core,b) for (ids,_,v,core),b in zip(chosen,coeffs,strict=True)]


def pin_read(path, expected):
    s = path.read_bytes()
    assert hashlib.sha256(s).hexdigest()==expected, f"public source pin differs: {path}"
    return s


def load_public(source):
    for name,sha in SOURCE_PINS.items():
        pin_read(source/name,sha)
    spec = importlib.util.spec_from_file_location("rk20_pinned_chart",source/"construct.py")
    rk = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = rk
    spec.loader.exec_module(rk)
    rk.PAID = PAY
    seed = json.loads((source/"../erk-eleven-twelve-moment-splice/paid9-seed.json").read_bytes())
    f,fo,fr = rk.long(9,False,seed)
    r9,ro,rr = rk.long(9,True,seed,symmetric_last=True)
    r8,qo,qr = rk.long(8,True,seed,regular_grade8=True)
    assert (len(f),len(r8),len(r9))==(27,22,27)
    assert r8==r9[:22] and all(not any(row[22:]) for row in r9[22:])
    assert [2*sum(r,Z)-1 for r in r9[-2:]]==[Q(-1,2),Q(1,2)]
    fd = [pad(rk.read(fo,fr,lambda k,j=j:Q(k==j))[0],27) for j in range(M)]
    d8 = [pad(rk.read(qo,qr,lambda k,j=j:Q(k==j))[0],25) for j in range(8)]+[[Z]*25]
    R = r9[:25]
    assert {2*sum(r,Z)-1 for r in R} <= OLD
    m_y = [[f(j) for j in range(9)] for f in ro[:7]]
    r_num = [pad(v,27)[:25] for v in rr[:7]]
    y_powers = [pad(in_y([Z]*j+[ONE]),9) for j in range(9)]
    m_v = mat(m_y,tr(y_powers))
    Jc, control = left_inverse([r[:7] for r in m_v])
    # The historical presentation scales each of these seven rows by 9.
    assert len(control) == 1 and abs(control[0][2]) == 1
    assert 9**7 * control[0][1] == -3949233059431874504499037810458624000000
    Jc += [[Z]*7 for _ in range(2)]
    Jy = tr([in_y(col) for col in tr(Jc)])
    assert mat(m_y,Jy)==[[Q(i==j) for j in range(7)] for i in range(7)]
    hit = mat(m_y,d8)
    d0 = [plus(a,b) for a,b in zip(d8,mat(Jy,[plus(u,scale(v,-1)) for u,v in
                                           zip(r_num,hit,strict=True)]),strict=True)]
    assert mat(m_y,d0)==r_num
    assert all(not any(act(m_y,in_y(q))) for q in QG)
    assert [tuple(v[7:]) for v in QG]==[(1,0),(0,1)]
    return rk,f,fd,R,d8,d0,m_y,r_num


def evaluated(D, a):
    return [ev(col,a) for col in tr(D)]


def integrated(D, a):
    return [sum((x*a**(j+1)/(j+1) for j,x in enumerate(col)),Z) for col in tr(D)]


def build(source):
    rk,FA,FD,R,D8,D0,Mc,Rc = load_public(source)
    old = {0} | {s*r for s in (-1,1) for r in (1,2,3,4,5,6,7,8,12)}
    grid = tuple(sorted(Q(i,6) for i in (old-{8,-7})|{9,10,13}))
    assert len(grid)==20 and tuple(a for a in grid if a not in OLD)==B
    assert all(unit(a-b) for a,b in combinations(grid,2))
    lam = {a:mean(card(grid,a)) for a in grid}
    assert all(sum((lam[a]*a**j for a in grid),Z)==(Q(1,j+1) if j%2==0 else Z)
               for j in range(P))
    assert tuple(abs(strip_int(lam[a].numerator)) for a in B)==MASS_CORES
    assert all(math.gcd(a,b)==1 for a,b in combinations(MASS_CORES,2))
    K = [integral(q) for q in QG]
    mask = {a:[ev(q,a) for q in MASKS] for a in B}
    assert tuple(h_div(MASKS[0])[-1:])==(1,) and tuple(h_div(MASKS[1])[-2:])==(0,1)
    assert all(mask[a]==[-ev(q,a) for q in K] for a in E)
    top_hull = hull(S)
    pivot = dot(PINS,top_hull)
    assert pivot==Q(-31616) and unit(pivot)
    amb = prod_poly(LEFT,hull(S1))
    for s in range(2):
        for j in range(2):
            assert sum((lam[a]*mask[a][s]*ev(amb,a)*a**j for a in B),Z)==0
    c_left = {a:prod_poly(LEFT,scale(card(S1,a),1/(1-a))) for a in S1}
    c_late = {a:[-sum((lam[b]*mask[b][i]*ev(c_left[a],b) for b in B),Z)
                for i in range(2)] for a in S1}
    for k in range(10):
        for i in range(2):
            f0 = [Z]*k + LEFT
            assert sum((lam[a]*mask[a][i]*ev(f0,a) for a in B),Z)+sum(
                (c_late[a][i]*ev(f0,a) for a in S1),Z)==0
    ct = {-ONE:[Z]*(M+1)}
    for a in S:
        q = pad(scale(card(S,a),1/ev(H,a)),8)
        t = plus(q,scale(top_hull,-dot(PINS,q)/pivot))
        assert not dot(PINS,t)
        ct[a] = prod_poly(H,t)
    V = [[Z]*j+H for j in range(8)]
    U0 = [[lam[a]*ev(q,a) for q in QG] for a in E]
    J0, sc0 = left_inverse(U0)
    assert [(ids, core) for ids,_,core,_ in sc0]==[
        ((0,1),-39733408105657801027),
        ((0,4),62501285004289639939),
        ((2,4),-2725593691803541310669)]
    X = [[lam[a]*v for v in [ev(q,a) for q in V]+mask[a]] for a in B]
    JT, st = left_inverse(X)
    assert len(st)==11
    lo, count = 30,36
    slot = {a:25+j for j,a in enumerate(CENTERS)}
    f0 = lambda a:evaluated(D0,(1+a)/2)
    i0 = lambda a:integrated(D0,(1+a)/2)
    eta = []
    for r in J0:
        u = [Z]*lo
        for a,h in zip(E,r,strict=True):
            v = lam[a]*h
            u = plus(u,scale(f0(a),-v))
            u[slot[a]]=v
        assert not sum(u,Z)
        eta.append(u)
    def combo(v, coeff):
        r = pad(v,lo)
        for a,q in zip(coeff,eta,strict=True):
            r = plus(r,scale(q,a))
        return r
    decoder = lambda a:combo(f0(a),[ev(q,a) for q in QG])
    inlet = lambda a,k:combo(i0(a),[ev(q,a)+v for q,v in zip(K,k,strict=True)])
    reg = [a for a in grid if a not in B]
    labels0 = [2*sum(r,Z)-1 for r in R]
    raw = R+[i0(a) for a in E]+[inlet(a,mask[a]) for a in H_LIVE]+R+[inlet(a,[Z,Z]) for a in reg]
    labels = labels0+list(CENTERS)+labels0+reg
    beta = [ONE]*25+[lam[a] for a in CENTERS]+[-ONE]*25+[lam[a] for a in reg]
    for a in S1:
        lvec = [mean(prod_poly(ct[a],integral(v))) for v in V]+[Z,Z]
        tap = act(tr(JT),lvec)
        u = pad(inlet(a,c_late[a]),count)
        for b,c in zip(B,tap,strict=True):
            u = plus(u,scale(decoder(b),-lam[b]*c))
            u[slot[b]] += lam[b]*c
        raw.extend((u,inlet(a,[Z,Z])))
        beta.extend((ONE,-ONE))
        labels.extend((a,a))
    ns = 86
    assert len(raw)==len(beta)==len(labels)==ns
    raw = [pad(r,ns) for r in raw]
    assert all(not any(r[i:]) and sum(r,Z)==(1+a)/2
               for i,(r,a) in enumerate(zip(raw,labels,strict=True)))
    # Arithmetic is in Q for this reconstruction. Each ratio is checked in U20
    # before any base change; none of these masses is inverted in a base ring.
    norm = [[z/beta[j] if z else Z for j,z in enumerate(r)] for r in raw]
    assert all(paid(x) for r in norm for x in r)
    L = [r[::-1] for r in raw[::-1]]
    N = [r[::-1] for r in norm[::-1]]
    b = beta[::-1]
    x = [(1-a)/2 for a in labels[::-1]]
    T = [[b[j]*N[j][i] for j in range(ns)] for i in range(ns)]
    assert all(not any(t[i:]) for i,t in enumerate(T))
    ef = tr([evaluated(FD,a) for a in x])
    A = [pad(r,27+ns) for r in FA]
    for a,t in zip(x,T,strict=True):
        prefix = [u-v for u,v in zip(integrated(FD,a),act(ef,t),strict=True)]
        A.append(prefix+t)
    assert A[44]==A[0] and A[50]==A[16]
    raw_w = [Z]*27+b
    folded, weights, mergers = rk.merge([r[:i] for i,r in enumerate(A)],raw_w)
    assert len(folded)==len(weights)==70
    old_to_old = {i-1:j-1 for i,j in mergers}
    reps = [i for i in range(len(A)) if i not in old_to_old]
    new_index = {j:i for i,j in enumerate(reps)}
    owner = [new_index[old_to_old.get(i,i)] for i in range(len(A))]
    B0 = [[dict(v).get(j,Z) for j in range(70)] for v in folded]
    out = {"A":[list(map(str,r[:i])) for i,r in enumerate(B0)], "b":list(map(str,weights)),
           "coefficient_common_denominator":str(int_lcm(B0+[weights]))}
    return out, dict(A=A,raw_w=raw_w,B0=B0,weights=weights,owner=owner,reps=reps,L=L,
                     N=N,T=T,x=x,b=b,FD=FD,R=R,D8=D8,D0=D0,Mc=Mc,Rc=Rc,grid=grid,lam=lam)


@lru_cache(None)
def forests(n, lower=None):
    if n==0:
        return ((),)
    return tuple((t,)+u for k in range(1,n+1) for t in forests(k-1)
                 if lower is None or lower<=t for u in forests(n-k,t))


@lru_cache(None)
def shape(t):
    v = [shape(u) for u in t]
    n = 1+sum(q[0] for q in v)
    return n,n*math.prod(q[1] for q in v)


def omega(A):
    @lru_cache(None)
    def phi(t):
        q = [act(A,phi(u)) for u in t]
        return tuple(math.prod(r[i] for r in q) for i in range(len(A)))
    return phi


def word(s):
    t = ()
    for ch in reversed(s):
        t = (t,) if ch=="A" else t+((),)
    return t


def basis(candidates):
    """A basis spanning the candidates over Q, with exact ordered pivots."""
    pivots = []
    for raw in candidates:
        r = list(map(Q,raw))
        for j,v in pivots:
            a = r[j]
            if a:
                r = r[:j] + [x-a*y for x,y in zip(r[j:],v[j:],strict=True)]
        j = next((j for j,a in enumerate(r) if a), None)
        if j is not None:
            p = (j,scale(r,1/r[j]))
            pos = next((k for k,(i,_) in enumerate(pivots) if i>j),len(pivots))
            pivots.insert(pos,p)
    return [r for _,r in pivots]


def had(u,v):
    return [x*y for x,y in zip(u,v,strict=True)]


def verify_small_reverse(o):
    R = [pad(r,25) for r in o["R"]]
    D,D8,MR,RR = (o[k] for k in ("D0","D8","Mc","Rc"))
    phi = omega(R)
    nchecks = 0
    for k in range(1,10):
        model = [Q(j==k-1) for j in range(9)]
        for tree in forests(k-1):
            n,f = shape(tree)
            y = scale(phi(tree),Q(f,n))
            assert n==k and act(RR,y)==act(MR,model)
            dec = act(D,y)
            if k<=8:
                assert dec==act(D8,y)==model
            else:
                v = centered(plus(model,scale(dec,-1)))
                assert v==plus(scale(QG[0],v[7]),scale(QG[1],v[8]))
            nchecks += 1
    assert nchecks==486
    return nchecks


def verify_structure(o):
    """Independent exact identity audit on rational spans; descent to U20."""
    A,B0,b_all,b_lit,owner,reps = (o[k] for k in ("A","B0","raw_w","weights","owner","reps"))
    x,T,L,N,b,DF = (o[k] for k in ("x","T","L","N","b","FD"))
    n, ns, nf = 113,86,27
    assert len(A)==n and len(b_all)==n and len(B0)==len(b_lit)==70
    assert not any(v for i,r in enumerate(A) for v in r[i:])
    assert not any(v for i,r in enumerate(B0) for v in r[i:])
    assert len({tuple(r) for r in B0})==70
    assert all(paid(z) for A0 in (A,B0,L,N,T,DF) for r in A0 for z in r)
    assert all(paid(w) for w in b_all+b_lit)
    assert int_lcm(B0+[b_lit])==D_EXPECT and int_lcm([b_lit])==E_EXPECT
    assert PAY**5 % D_EXPECT==0 and PAY**2 % E_EXPECT==0
    assert A[44]==A[0] and A[50]==A[16] and owner[44]==owner[0] and owner[50]==owner[16]
    assert set(owner)==set(range(70)) and reps==sorted(set(reps))
    assert all(reps[k]<=j for j,k in enumerate(owner))
    assert all(owner[j]==k for k,j in enumerate(reps))
    def fold(u):
        t = [Z]*70
        for i,a in zip(owner,u,strict=True):
            t[i] += a
        return t
    assert all(fold(r)==B0[k] for r,k in zip(A,owner,strict=True))
    assert fold(b_all)==b_lit
    for i in range(ns):
        assert not any(T[i][i:]) and not any(L[i][:i+1]) and not any(N[i][:i+1])
        assert sum(A[nf+i],Z)==x[i]==1-sum(L[i],Z)
        assert A[nf+i][nf:]==T[i]
        for j in range(ns):
            assert L[i][j]==b[j]*N[i][j]
            assert T[i][j]==b[j]*N[j][i]
            assert b[i]*T[i][j]==b[j]*L[j][i]
    for k in range(P):
        assert dot(b,[a**k for a in x])==Q(1,k+1)

    Ecols = [[a**k for k in range(P)] for a in x]
    Icols = [[a**(k+1)/(k+1) for k in range(P)] for a in x]
    base = mat(T,Ecols)
    K = [plus(u,scale(v,-1)) for u,v in zip(base,Icols,strict=True)]  # TE - I.
    D = DF+[[Z]*nf]*(P-M)
    assert [r[:nf] for r in A[nf:]]==[scale(v,-1) for v in mat(K,D)]
    assert all(not any(r[nf:]) for r in A[:nf])

    # Establish exact forward closure without any exhaustive high-order trees.
    AF = [r[:nf] for r in A[:nf]]
    F = {1:[[ONE]*(nf+1)]}
    for n0 in range(2,M+3):
        at = []
        for a in range(1,n0):
            j = n0-a
            right = [(act(AF,r[:-1]),r[-1]) for r in F[j]]
            for u in F[a]:
                for r,z in right:
                    at.append(scale(had(u[:-1],r),j)+[u[-1]*z])
        F[n0] = basis(at)
    mid_sources, top_sources = [], []
    for n0,data in F.items():
        for u in data:
            w = [(u[-1] if j==n0-1 else Z)-val for j,val in enumerate(act(D,u[:-1]))]
            if n0<=M:
                assert not any(w)
                continue
            assert not any(w[n0:])
            p0 = centered(w[:n0],reflect=True)
            assert ev(p0,ONE)==0
            mid_sources.append(w)
            if n0==M+1:
                assert ev(p0,-ONE)==0 and dot(h_div(p0),PINS)==0
                top_sources.append(w)

    # Intentionally reconstruct the Q-spans rather than trust old HNF bytes.
    kt = tr(K)
    U = [[ONE]*ns]
    degrees = []
    for d in range(G+1):
        degrees.append(len(U))
        for u in U:
            charge = act(kt,had(b,u))
            if d<=G-2:
                assert not any(charge[:P-d-1])
            elif d==G-1:
                assert all(not dot(charge,w) for w in mid_sources)
            else:
                assert all(not dot(charge,w) for w in top_sources)
        if d<G:
            U = basis([had(x,u) for u in U]+[act(L,u) for u in U])
    return dict(forward_span_sizes=[len(v) for v in F.values()],dual_span_sizes=degrees,
                owner_checks=len(A)*len(B0),intermediate_sources=len(mid_sources),
                top_sources=len(top_sources))


NEXTRAW = (
    Q("521067783694089467535893794509760965147234890578182398269/1096826635008"),
    Q("10397346472839130375711127012518329281535388989062988020545/8989677126144"),
)
RAWBLEND = (
    -110632116235225616375527994982122892640580384243411432428142213056095917568,
    45442166849681245557059598666734587555904511052646134904480582006065681920,
)
NEXTDEFS = (
    Q("-4160686372402151673856869109755270888702390406387807813583244931/694949355941068800"),
    Q("-12695026331702817663261557776761061442024285895816002914575957571/694949355941068800"),
)
DEFBLEND = (
    -758356598009113487330143041987095269936349942504554806220223860709021584446259200,
    248544893119142397216985916541483308694869603342501480637890363714904896185958400,
)
BUSH_DEF = Q("315590668417/1900734293559214080")


def verify_next(o):
    A,b = o["B0"],o["weights"]
    phi = omega(A)
    sfx = ("CACCACCACC","CACCACCAAC","CACCACCCCC","CACCCCCCCC")
    coeffs = (136080,-272160,204120,-34020)
    raw,defs = [],[]
    for pref in ("CCCCCCCCCA","CCCCCCCCAA"):
        V = [word(pref+w) for w in sfx]
        shapes = list(map(shape,V))
        assert all(n==P+1 for n,_ in shapes)
        shall = [Q(1,f) for _,f in shapes]
        assert not dot(coeffs,shall)
        actual = [dot(b,phi(t)) for t in V]
        raw.append(dot(coeffs,actual))
        defs.append([f*a-1 for (_,f),a in zip(shapes,actual,strict=True)])
    assert tuple(raw)==NEXTRAW and dot(RAWBLEND,raw)==1
    actual = tuple(defs[0][:2])
    assert actual==NEXTDEFS and dot(DEFBLEND,actual)==1 and all(paid(z) for z in actual)
    scale0 = E_EXPECT*D_EXPECT**P
    nums = [x*scale0 for x in actual]
    assert all(x.denominator==1 for x in nums) and dot(DEFBLEND,nums)==scale0
    bush = ((),)*P
    assert (P+1)*dot(b,phi(bush))-1==BUSH_DEF


def check_prior_receipt(path,o):
    old = json.loads(pin_read(path,PRIOR_RECEIPT_SHA))
    def read(k):
        d = old[k]
        return [[Q(int(a),int(d["den"])) for a in row] for row in d["num"]]
    a,l,d = (read(k) for k in ("A_unfolded","L","DF"))
    assert old["p"]==20 and old["nf"]==27
    assert [r[:27] for r in a[:27]]==[r[:27] for r in o["A"][:27]]
    assert d==o["FD"]+[[Z]*27]*(P-M)
    oldr = [v[-27:][::-1][:25] for v in l[-27:][::-1][:25]]
    assert oldr==[pad(r,25) for r in o["R"]]


def main():
    a = argparse.ArgumentParser(description=__doc__)
    a.add_argument("source",type=Path,help="pinned erk-signed-reverse directory")
    a.add_argument("--prior-receipt",type=Path,help="optional pinned old order-20/71 receipt")
    a.add_argument("--emit-literal",action="store_true",help="write verified historical literal to stdout")
    opts = a.parse_args()
    literal, evidence = build(opts.source)
    if opts.prior_receipt is not None:
        check_prior_receipt(opts.prior_receipt,evidence)
    local = verify_small_reverse(evidence)
    finite = verify_structure(evidence)
    verify_next(evidence)
    payload = (json.dumps(literal,indent=2)+"\n").encode("ascii")
    digest = hashlib.sha256(payload).hexdigest()
    assert digest==LITERAL_SHA, f"reconstructed literal SHA {digest}, expected {LITERAL_SHA}"
    print(json.dumps(dict(p=20,stages=70,sha256=digest,projected_reverse_reads=local,**finite)),
          file=sys.stderr)
    if opts.emit_literal:
        sys.stdout.buffer.write(payload)


if __name__ == "__main__":
    main()
