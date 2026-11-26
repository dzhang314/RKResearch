# Exact SDIRK upper-bound comparison through order 20

**No unrestricted published upper entry changes.** With the allowed
real-algebraic coefficients and in the matched sharp-depth diagonal
regimes, the confirmed higher-budget construction first improves the
published one-degree layered bound at order 7 and continues to improve
it through order 20. Its order-20 count is **130 at depth 19**, versus
146 in that same regime. The exceptional **145 at depth 18** and the
unrestricted published **59-stage** order-20 witness answer different
questions and are not improved or replaced here.

## Publication and scope pins

The source is published main
`8779cc0bdc81be6f7a7266d86bf4540e426548c0`. The upper ends of
the strict SDIRK column of `ai-generated/CURRENT.md` agree row-for-row
with the upper-witness rows of
`ai-generated/upper-bounds/README.md`. Those entries allow free
choice of the nonzero common diagonal, depth, and real-algebraic
coefficients. They do not certify the same counts at a prescribed
diagonal, sign, dependency depth, or coefficient field. They are
upper witnesses, not stage minima or stability claims.

The previously published layer constructions are
`strict-sdirk-dependency-depth/QUADRATIC-STAGE-BOUND.md` (full-column)
and `PAID-WIDTH-REDUCTION.md` (one-degree). For this comparison use
q=ceil(p/2) terminal nodes and U=pq−q(q−1)/2. The independently reviewed
higher-budget inputs are the source theorem and field addendum with
SHA-256 6902ff3c432fbede1d31a56f0f1e99f38683238c5ee80d540fe7a1a364acd4ec
and 58fbc8df8cd81227ea1479e7be89d4f8c93602ceb8ab832a65914176dbe13e4e.
This packet does not rerun their proof audit.

## Depth p−1: match the nonzero diagonal regime before comparing

For p≥2, write λ_j(1)=ℓ((I−γ id)^j1). The sharp-depth nonexceptional
branch is λ_{p−1}(1)≠0.

* **Any prescribed nonexceptional real-algebraic γ**, with coefficient
  extensions allowed: the published full-column count is U and the
  published one-degree count is U−(q−2+e₂) for p≥3, with the two-stage
  p=2 case separate. Here e₂ is 1 when λ_{p−2}(1)≠0. The conservative
  column below does not use that extra cancellation. Exact order is
  available, including when λ_p(1)=0, by taking the published
  q-node rule exact through degree p−1 but not degree p.
* **Matched higher-budget regime:** every prescribed negative
  real-algebraic γ, or sufficiently small or large positive
  real-algebraic γ for this p. The positive ranges can also require
  λ_{p−2}, λ_{p−1}, λ_p nonzero (ignore λ_{p−2} when p=2), since
  these are nonzero at zero and have nonzero leading terms. Then
  the old method has e₂=1 whenever that layer exists, and its
  count is U−q+1. The higher-budget method uses exactly the sum
  H=Σ_{s=1}^p min(q,ceil((2s−1)/3)). The same q Gaussian terminal
  clocks and weights can be used in both; the first unpaid
  shifted tall tree gives exact order and the paid one gives
  sharp depth. A prescribed larger admissible terminal rule with q'≤p
  can stay unchanged, with H+(q'−q) stages by the field addendum.
* **A particular positive γ or a fixed small coefficient field**
  is not certified by the mere generic nonsingularity of the
  moment system. The confirmed positive ranges depend on p; a
  specified value needs verified membership in a suitable range or
  a separate split-hull proof.
  Even with rational γ the earlier real-algebraic nodes can
  require an extension, so these are not rational-coefficient
  upper bounds. The older published q=p−1 rational-clock
  construction remains available over Q(γ), with its own larger
  counts and no extension. Negative γ itself forces depth p−1,
  so the negative cases cannot enter the shallow column below.

Stage counts (upper witnesses, not asserted optima):

| p | Published free upper | q | Full-column | One-degree, no extra loss | One-degree, matched | Higher-budget, matched | Matched saving |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | - | - | - | - | - | - |
| 2 | 1 | 1 | 2 | 2 | 2 | 2 | 0 |
| 3 | 2 | 2 | 5 | 5 | 4 | 4 | 0 |
| 4 | 3 | 2 | 7 | 7 | 6 | 6 | 0 |
| 5 | 5 | 3 | 12 | 11 | 10 | 10 | 0 |
| 6 | 7 | 3 | 15 | 14 | 13 | 13 | 0 |
| 7 | 9 | 4 | 22 | 20 | 19 | 18 | 1 |
| 8 | 11 | 4 | 26 | 24 | 23 | 22 | 1 |
| 9 | 14 | 5 | 35 | 32 | 31 | 29 | 2 |
| 10 | 17 | 5 | 40 | 37 | 36 | 34 | 2 |
| 11 | 20 | 6 | 51 | 47 | 46 | 42 | 4 |
| 12 | 23 | 6 | 57 | 53 | 52 | 48 | 4 |
| 13 | 26 | 7 | 70 | 65 | 64 | 58 | 6 |
| 14 | 30 | 7 | 77 | 72 | 71 | 65 | 6 |
| 15 | 34 | 8 | 92 | 86 | 85 | 76 | 9 |
| 16 | 38 | 8 | 100 | 94 | 93 | 84 | 9 |
| 17 | 43 | 9 | 117 | 110 | 109 | 97 | 12 |
| 18 | 48 | 9 | 126 | 119 | 118 | 106 | 12 |
| 19 | 54 | 10 | 145 | 137 | 136 | 120 | 16 |
| 20 | 59 | 10 | 155 | 147 | 146 | 130 | 16 |

Order 1 is outside the p≥2 layer formulas. The published free one-stage
entry is kept unchanged. For an elementary prescribed-diagonal check,
a one-stage consistent tableau has b=1 and second-order value γ, so
it has exact order 1 unless γ=1/2. For that prescribed value, a
two-stage lower-triangular tableau with a nonzero strict entry into
the only output stage and b=(0,1) already has exact order 1.

## Exceptional depth p−2, not interchangeable with the table above

For p≥2 the exceptional algebraic diagonals are the positive reciprocals
of roots of L_{p−1}^(1). The published full-column and one-degree
counts here are U−2 and U−q for p≥3, respectively, each with the
same q and exact order. At p=2 the separate published implicit
midpoint gives one stage at γ=1/2. The newer higher-budget real
splitting regimes used above expressly do not cover these prescribed
shallow diagonals: no numerical row below is inferred for it.
The published classical witnesses of 2 and 3 stages at p=3 and
p=4 occur at their own exceptional values, so the layer formulas
are not best bounds for every individual exceptional value.

| p | Published exceptional full-column | Published exceptional one-degree |
|---:|---:|---:|
| 2 | 1 | 1 |
| 3 | 3 | 3 |
| 4 | 5 | 5 |
| 5 | 10 | 9 |
| 6 | 13 | 12 |
| 7 | 20 | 18 |
| 8 | 24 | 22 |
| 9 | 33 | 30 |
| 10 | 38 | 35 |
| 11 | 49 | 45 |
| 12 | 55 | 51 |
| 13 | 68 | 63 |
| 14 | 75 | 70 |
| 15 | 90 | 84 |
| 16 | 98 | 92 |
| 17 | 115 | 108 |
| 18 | 124 | 117 |
| 19 | 143 | 135 |
| 20 | 153 | 145 |

At order 20 the published 145-stage proof specifically preserves
ten positive Gaussian contributing clocks, depth 18, and attainment
in the degree-72,960 minimal coefficient field at that simultaneous
endpoint. The new 130-stage count comes with depth 19 and a different
diagonal hypothesis and may enlarge the coefficient field. Neither
count is a physical stage minimum.

## Cross-check against particular published positive values

The archive gives exact rational witnesses of 3 and 4 stages at
orders 3 and 4 with γ=1/6, 5 at order 5 with γ=1, 7 at order 6
with γ=1/4, 11 at order 7 with γ=1/7, 15 at order 8 with γ=1/8,
23 at order 9 with γ=1/9, and 27 at order 10 with γ=1/9.
These are examples, not a completed table of fixed-value optima.
The first three have sharp nonexceptional depth p−1: the published
rational-diagonal tall obstruction applies and their stage count
equals p. The other counts here make no assertion about matched
depth. None would be improved by the higher-budget numbers even
if its particular positive parameter were certified, and the
higher-budget theorem does not establish all-rational coefficients.

The published order-20 radii/33 construction is an exact
117-stage rational witness with prescribed γ=1/66 and prescribed
19 positive sites; no depth comparison is inferred from that
source. If the higher-budget regime were proved at that specific
γ, retaining its actual 19 sites would give H+9=139 stages, not
130, and no improvement to that fixed-value/output-support upper
count. This observation is conditional, not a test of γ=1/66.

## Reproduction

`ANCESTOR-MOMENT-COUNTS.tsv` is a standalone portable ledger. With the published
snapshot available, check the pins from its root and replay the
integer comparison from this packet:

    (cd /path/to/snapshot && sha256sum -c /path/to/packet/PUBLISHED-SOURCES.sha256)
    python3 compare_sdirk_bounds.py /path/to/snapshot | diff -u ANCESTOR-MOMENT-COUNTS.tsv -

The script validates the two published table hashes, extracts all
twenty strict SDIRK rows without hand copying, recomputes every
layer count from its fibres, and checks the algebraic closed forms
independently. It runs no polynomial search, Lean, or proof replay.
