# The old normalized quintic-head fit has degree two

**Result.** In the live direct \(F_n\) \(\alpha=\beta=1\) nonzero
ordinary-diagonal subchart of normalized invisible-six DIRK11/13,
the degree-two coefficient \(W_{0,2}\) of the common old fit
\(W_0=(IP_0/P)\bmod R\) is nonzero. This is a third independent
exceptional-slice exclusion, beyond \(K_*=0\) and \(B=z\), with
the same field and tableau hypotheses described in
[carrier slices](../dirk11-thirteen-invisible-six-alpha-one-live-fn-carrier-slices/README.md).
It is not an exclusion of the full direct \(F_n\) chart and does
not change the general real DIRK11 interval.

The old fit is a polynomial of degree at most two. Its symbolic
calculation has a live common inverse scale \(n\), and the
horizontal change of units is live as well. Thus an affine old
fit forces the exact old scalar \(h=[Y^2]\widehat W_0=0\).
Use this scalar twice, first as the sole seed in the rank-12
clock algebra (so its exact norm must vanish) and then as the
additional row in the same monic rank-two adjacent carrier algebra
as the genuine quintic pin \(Q_H=0\). This proof does not assume
\(\lambda=-1\), does not divide by any coefficient of
\(W_0\), and works without late-ghost or other extra conditions.

The raw/squarefree exact clock projection has degrees **312/168**,
after stripping only the known live ordinary base factors.
Its entire support and common ideal ranks are:

| Clock factor degree | Constant coefficient | Live mask | Exact cap | Residue degree at 103 | Joint rank |
|---:|---:|---|---:|---:|---:|
| 12 | 16227 | old ratio denominator | 22 | 12 | 22 |
| 12 | 54123 | \(c_2\) | 18 | 4 | 18 |
| 36 | −7295157 | 1 | 24 | 4 | 24 |
| 48 | 1865429207937 | \(q\) | 22 | 1 | 22 |
| 60 | −1461941766456 | \(n\) | 22 | 1 | 22 |

The same rank argument as in the carrier-slice packet applies:
over the exact factor field, the joint image of
multiplications by \(G h\) and \(GQ_H\) lies in the image of
the live mask power \(G\). The rational rank cap is checked from
the exact mask norms, with no semisimplicity assumption. One
nonzero residue minor of the same cap gives equality of these
images in characteristic zero. Thus the image contains \(G\);
evaluation would make the live \(G\) zero. The degree-36 factor
uses the residue \(V^4+16V^3+54V^2+101V+100\) of the exact clock
polynomial at 103. No unknown tableau or clock is reduced.

Replay via `bash verify.sh` with python-flint 0.9; the wrapper
verifies the hash of the previously audited sibling engine and
changes only the seed, extra row, and expected complete factor
inventory. This is exact executable source arithmetic, not yet
an end-to-end native Lean exclusion.
