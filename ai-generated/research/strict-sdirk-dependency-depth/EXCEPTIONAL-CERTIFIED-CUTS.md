# Exceptional shallow layers certified by the all-power threshold

This uses the [positive Chebyshev threshold](POSITIVE-CHEBYSHEV-THRESHOLD.md)
and the [ancestor-hull transport](ANCESTOR-MOMENT-SPAN.md). The result is
an upper construction at a selected positive diagonal, not a stage
minimum, an unrestricted improvement, or a bound at a prescribed
coefficient field.

## A uniform selection and sufficient budget

For p≥3 let q=ceil(p/2), D=p−2, and choose γ to be the largest
reciprocal of a root of L_(p−1)^(1). This fixes a positive
real-algebraic diagonal at which the p-vertex shifted tall target
vanishes, and the previous and next shifted tall targets are nonzero
by the adjacent Laguerre recurrence. Put n=p−1. The first three
elementary symmetric coefficients of these positive reciprocals are

    e₁=n/2,  e₂=n(n−1)/12,  e₃=n(n−1)(n−2)/144.

They follow from the normalized associated Laguerre series. If
S_j denotes their j-th power sum, Newton identities give

    S₂=n(n+2)/12,    S₃=n(n+1)(n+2)/48.

Therefore the largest reciprocal is at least S₃/S₂=p/4. The
threshold τ_m from the linked theorem satisfies
`τ_m≤sqrt(m(m+1)/2)` by the squared sum of the ordinary Laguerre
reciprocals. The explicit, purely integer sufficient condition

    8 m(m+1) ≤ p²                                           (A)

therefore implies γ≥τ_m. No approximations of individual roots
or special-case rank searches enter (A).

At a positive nonterminal layer write d=D−h and s=p−d, so
s=h+2. Let r_old(s) be the published one-degree width, namely
s−1 for 3≤s≤q and q for s>q. Consider the generic matched-width
candidate

    r_*(s) = min(q, ceil((2s−1)/3)).

Use it where r_*(s)<r_old(s) and (A) holds for

    r=r_*(s),   b=s−1−r,   m=(d−b)_+,   ν=b+min(d,b).

Here b≥0 and r<q. In fact b≤d: otherwise 2s−1>p+r,
while 3r≥2s−1 would give 2r>p, impossible for r<ceil(p/2).
Then ν=2b and r≥ν+1 is exactly 3r≥2s−1. If m=0 the tests are
ordinary polynomial ones; this cannot occur on a genuine
below-q selected reduction with r≥ν+1 but is harmless. For
m>0 the above Chebyshev theorem gives a monic degree-r hull
with distinct roots in (0,1) orthogonal to its first r tests
`T^m(y^j/j!)`. In particular all ν+1 actual local ancestor
moments vanish. Keep every unselected layer with its already
proved one-degree or original terminal hull, and keep the
initial singleton and all q original Gaussian output clocks.

The existing all-tree proof applies to all such reductions
**simultaneously**, not only to the bush or word diagnostics:
its local ancestor-first telescope bounds the quotient and
sibling cost by b and removes the hull error just using
`T^m K[y]_{≤ν}`. All other cuts retain their own independent
receipts. The only omitted paid tree is still the appropriate
tall one, killed by the chosen Laguerre zero. The two nonzero
tall witnesses still certify exact depth D and exact order p.
All earlier weights are zero and the terminal weights are the
same positive Gaussian weights.

## Concrete arithmetic consequence at order 20

Here q=10, D=18, and the published one-degree count is 145.
The following four original plateau layers have width 10 and
satisfy the uniform test:

| s | d | new r | b | m | ν | 8m(m+1) |
|---:|---:|---:|---:|---:|---:|---:|
| 11 | 9 | 7 | 3 | 6 | 6 | 336 |
| 12 | 8 | 8 | 3 | 5 | 6 | 240 |
| 13 | 7 | 9 | 3 | 4 | 6 | 160 |
| 14 | 6 | 9 | 4 | 2 | 8 | 48 |

Each right entry is ≤400. Their savings are 3+2+1+1=7,
so the resulting upper count is **138** over a finite real-algebraic
extension, with depth 18 and the same ten positive contributing
Gaussian clocks. The [earlier 144-stage construction](EXCEPTIONAL-M2-COMPRESSION.md)
is weaker but applies assuming only an exceptional γ≥3. The
stronger conclusion here chooses the largest exceptional reciprocal
(or another satisfying the stated stronger certificates).

The new hull coefficients lie in Q(γ) and their roots are real
algebraic. Adjoining these roots to the field used by the earlier
construction requires at most a finite real-algebraic extension.
The proof does not assert that the smaller field is enough or that
an enlargement is necessary.
