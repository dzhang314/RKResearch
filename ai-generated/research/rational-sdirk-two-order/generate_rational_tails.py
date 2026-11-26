"""Exact rational construction from the pinned old witnesses; writes JSON to stdout.

Usage: python generate_rational_tails.py {8,9,10,12,14,16,18,20} --repo-root /path/to/RKResearch
No Lean or external dependency. This generator was not executed during the proof task.
The accompanying mathematics proves ordinary order; the program checks local and scalar receipts.
"""
from argparse import ArgumentParser
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import re

SEED = {
    7: ("RationalStrictSDIRKElevenStageSevenUpper.lean",
        "cb14583f04a53fe39c20f84c8b561942d81131e616269c04795bfdb448c60915",
        11493557522580, 17280),
    8: ("RationalStrictSDIRKFifteenStageEightCore.lean",
        "87e77e5ff39099a105ce098e5b817c70ce02ad1e8f585181556dab378310254b",
        1540104384000, 33075),
}
SIX = [
    ["1/4"],
    ["-1/2", "1/4"],
    ["-1/8", "-1/8", "1/4"],
    ["31/24", "7/24", "-5/6", "1/4"],
    ["7/48", "1/48", "11/96", "-1/32", "1/4"],
    ["119/768", "53/768", "-155/1536", "9/512", "-9/64", "1/4"],
    ["-119/256", "-29/256", "207/512", "-31/512", "15/64", "1/2", "1/4"],
]
CASES = {
    8: (3, [Q("1/2"), Q(-1)], [4], "1090/1081", "-1245689/697374720", "+++-+++"),
    9: (4, [Q(-1), Q(-2), Q(-3)], [], "302/255", "-87763/12965400", "-+-+++++"),
    10: (4, [Q(0), Q("1/4"), Q("1/2")], [7, 6, 12],
         "9075/9133", "-2432737/1580146360320", "+--+-++++"),
}
CONTINUE = {
    12: ("597420361/783319131", "-1151734070569817279/8045432679821389332480", "++-++-+++++"),
    14: ("68974053965/68685634853", "-481089601965156873323/51907773859107082076160", "+-+-++-++++++"),
    16: ("18597392131407/18589798585870", "-31190692020337801883236423/272949334598284557366067200", "+--+-+++-+-++++"),
    18: ("42860523819631628/42976648351311529", "-53423004336711538615343627383823/30518195131275698497920046202880", "--+-+-++++-+-++++"),
    20: ("44123254076509126587/44354273258678140634", "-93218764777653353237419043912078394203/2771688644799123950668448067213066240", "+--+-+-++-++-+-++++"),
}
EXPECTED = {8: 13, 9: 19, 10: 21, 12: 31, 14: 43, 16: 57, 18: 73, 20: 91}


def clocks(A):
    return [sum(r, Q(0)) for r in A]


def dot(u, v):
    return sum((a*b for a, b in zip(u, v, strict=True)), Q(0))


def solve(M, rhs):
    """Solve M U = rhs, with square M and any number of RHS columns."""
    n = len(M)
    assert n == len(rhs) and all(len(r) == n for r in M)
    rows = [list(m)+list(r) for m, r in zip(M, rhs, strict=True)]
    for j in range(n):
        t = next(t for t in range(j, n) if rows[t][j])
        rows[t], rows[j] = rows[j], rows[t]
        pivot = rows[j][j]
        rows[j] = [x/pivot for x in rows[j]]
        for i in range(n):
            if i != j and rows[i][j]:
                v = rows[i][j]
                rows[i] = [x-v*y for x, y in zip(rows[i], rows[j], strict=True)]
    return [r[n:] for r in rows]


def load_seed(repo, p):
    if p == 6:
        A = [[Q(x) for x in r]+[Q(0)]*(7-len(r)) for r in SIX]
        b = [Q(x) for x in (0, 0, "7/90", "7/90", "2/15", "16/45", "16/45")]
        return A, b
    name, digest, den_A, den_b = SEED[p]
    data = (repo / "ai-generated/lean/RKCert/ReviewedNative" / name).read_bytes()
    if sha256(data).hexdigest() != digest:
        raise ValueError(f"unexpected seed contents: {name}")
    t = data.decode("utf-8")
    matrix = re.search(r"!!\[([-\d,;\s]+)\]", t).group(1)
    weights = re.search(r"def bInt[^=]*=\s*!\[([-\d,\s]+)\]", t).group(1)
    A = [[Q(int(x), den_A) for x in r.split(",")] for r in matrix.split(";")]
    b = [Q(int(x), den_b) for x in weights.split(",")]
    assert len(A) == len(b) and all(len(r) == len(A) for r in A)
    return A, b


def local_paid(A, positions, p):
    """Check only the stated local claims; no exhaustive top-order verification."""
    c = clocks(A)
    # N_{u triangleleft t} = N_u ⊙ (|t| A N_t).
    shelves = [[], [[Q(1)]*len(A)]]
    images = [[], [[dot(r, v) for r in A] for v in shelves[1]]]
    for n in range(2, p+1):
        v = [[u_i*j*av_i for u_i, av_i in zip(u, av, strict=True)]
             for j in range(1, n) for u in shelves[n-j] for av in images[j]]
        assert all(f[i] == c[i]**(n-1) for i in positions for f in v)
        shelves.append(v)
        images.append([[dot(r, f) for r in A] for f in v])


def hull(nodes):
    h = [Q(1)]
    for x in nodes:
        g = [Q(0)]*(len(h)+1)
        for j, a in enumerate(h):
            g[j] -= x*a
            g[j+1] += a
        h = g
    return h


def at(P, x):
    s = Q(0)
    for a in reversed(P):
        s = s*x+a
    return s


def I(P, j=0):
    return sum((a/(i+j+1) for i, a in enumerate(P)), Q(0))


def eval_decoder(c, picks):
    n = len(c)
    return solve(
        [[c[i]**j for j in range(len(picks))] for i in picks],
        [[Q(int(i == a)) for a in range(n)] for i in picks],
    )


def moment_decoder(c, b, d, anchor=None):
    m = d if anchor is None else d-1
    mat = [[Q(1, i+j+1) for i in range(d)] for j in range(m)]
    rhs = [[w*x**j for x, w in zip(c, b, strict=True)] for j in range(m)]
    if anchor is not None:
        mat.append([c[anchor]**i for i in range(d)])
        rhs.append([Q(int(i == anchor)) for i in range(len(c))])
    return solve(mat, rhs)


def extend(p, q, A, b_old, early, reps, gates, D=None, check_local=True):
    n = len(A)
    gamma = A[0][0]
    a = p-q-1
    assert gamma and all(row[i] == gamma and not any(row[i+1:]) for i, row in enumerate(A))
    c_old = clocks(A)
    ladder = [1-(2*i-1)*gamma for i in range(a, 0, -1)]
    H = hull(early+ladder)
    z = I(H, 1)/I(H)
    assert z == Q(gates[0])
    x = early+[z]+ladder
    k = len(x)
    assert k == p-1 and len(set(x)) == k
    P = [hull(x[k-j:]) for j in range(k+1)]
    w = []
    for i, v in enumerate(x):
        h = hull(x[:i]+x[i+1:])
        w.append(I(h)/at(h, v))
    assert all(w)
    assert "".join("+" if u > 0 else "-" for u in w) == gates[2]
    assert all(dot(w, [v**j for v in x]) == Q(1, j+1) for j in range(p))
    assert I(P[k], 1) == Q(gates[1]) != 0

    S = [[Q(0)]*k for _ in range(k)]
    for i in range(k-1):
        ix = list(range(i+1, k))
        rhs = [[-w[i]*at(P[j+1], x[i])/(j+1)] for j in range(len(ix))]
        ss = solve([[w[l]*at(P[j], x[l]) for l in ix] for j in range(len(ix))], rhs)
        for l, row in zip(ix, ss, strict=True):
            S[l][i] = row[0]
    B = [[v+(gamma if i == j else 0) for j, v in enumerate(row)] for i, row in enumerate(S)]
    for j in range(k):
        left = [dot([w[i]*at(P[j], x[i]) for i in range(k)], col) for col in zip(*S)]
        assert left == [-w[i]*at(P[j+1], x[i])/(j+1) for i in range(k)]

    if D is None:
        D = moment_decoder(c_old, b_old, q)
    U = []
    for v, row in zip(x, B, strict=True):
        f = [v**(j+1)/(j+1)-dot(row, [u**j for u in x]) for j in range(len(D))]
        U.append([dot(f, col) for col in zip(*D)])
    if check_local and reps:
        local_paid(A, reps, q+1)
    for i, r in enumerate(reps):
        assert c_old[r] == x[i] and i < k-a
        U[i] = [A[r][j]-(gamma if r == j else 0)
                -sum((S[i][l] for l in range(i) if reps[l] == j), Q(0))
                for j in range(n)]

    W = [[w[i]*x[i]**j for i in range(k)] for j in range(a)]
    target = []
    for j in range(a):
        f = [Q(0)]*j+[Q(1)]
        gg = [Q(0)]*(j+2)
        for l in range(j, -1, -1):
            coefficient = f[l]
            for z1, value in enumerate(P[l]):
                f[z1] -= coefficient*value
                gg[z1] += gamma*coefficient*value
            for z1, value in enumerate(P[l+1]):
                gg[z1] -= coefficient*value/(l+1)
        vj = [Q(1,j+1)]+[Q(0)]*j+[-Q(1,j+1)]
        h = [u-v for u, v in zip(vj, gg, strict=True)]
        assert not any(h[j:])
        target.append([b_old[i]*at(h,c_old[i]) for i in range(n)])
    discrepancy = [[target[j][i]-dot(W[j], col) for i, col in enumerate(zip(*U))]
                   for j in range(a)]
    dd = solve([row[k-a:] for row in W], discrepancy)
    for i in range(a):
        U[k-a+i] = [r+d for r, d in zip(U[k-a+i], dd[i], strict=True)]
    assert all([dot(W[j], col) for col in zip(*U)] == target[j] for j in range(a))

    C = [list(row)+[Q(0)]*k for row in A]+[u+bb for u, bb in zip(U, B, strict=True)]
    b = [Q(0)]*n+w
    assert clocks(C)[n:] == x
    # The first unmerged receiver index is n, and merges do not alter the old indices.
    for r in reps:
        appended = list(C[n])
        assert appended[n] == gamma and not any(appended[n+1:])
        assert [appended[i]+(gamma if i == r else 0)
                for i in range(n)] == C[r][:n]
        del C[n]
        b[r] += b[n]
        del b[n]
        for row in C:
            row[r] += row[n]
            del row[n]
    assert all(C[i][:n] == A[i] and not any(C[i][n:]) for i in range(n))
    assert len(C) == EXPECTED[p]
    return C, b


def main():
    arg = ArgumentParser()
    arg.add_argument("order", type=int, choices=sorted(EXPECTED))
    arg.add_argument("--repo-root", type=Path, required=True)
    args = arg.parse_args()
    p = args.order
    first = min(p,10)
    old, bw = load_seed(args.repo_root, first-2)
    q, early, reps, *gates = CASES[first]
    D = None
    if first == 10:
        local_paid(old, [6,7,8,9,10,12], 5)
        D = eval_decoder(clocks(old), [6,7,8,9,10])
    A,b = extend(first,q,old,bw,early,reps,gates,D)
    anchor = len(old) if first == 10 else None
    if anchor is not None:
        local_paid(A, [anchor], 6)
    for current in range(12,p+1,2):
        m = current//2
        old_n = len(A)
        c = clocks(A)
        beta = Q(-1 if m%2 == 0 else -2)
        early = [c[anchor],beta]
        i = -1
        while len(early) < m-2:
            if Q(i) not in early:
                early.append(Q(i))
            i -= 1
        D = moment_decoder(c,b,m,anchor)
        A,b = extend(current,m-1,A,b,early,[anchor],CONTINUE[current],D,check_local=False)
        anchor = old_n
        assert clocks(A)[anchor] == beta
    print(json.dumps({
        "order":p, "stages":len(A), "common_diagonal":str(A[0][0]),
        "A":[[str(x) for x in row] for row in A], "b":[str(x) for x in b]
    },indent=2))


if __name__ == "__main__":
    main()
