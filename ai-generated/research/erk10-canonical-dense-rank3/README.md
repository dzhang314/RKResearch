# Rank three in the canonical dense order-five prefix: one restriction and one escape

This packet studies an **eight-stage prefix ingredient**, not a
sixteen-stage order-ten method. It gives a regular-chart restriction
and a different, literal rational prefix with three independent
size-six residuals. The latter uses only factorial-paid denominators.

## Regular canonical restriction

The explicit family is the seven rows in the symbolic replay,
with scalar clock order \(0,2/3,1,2,2,v,r\) and free parameters
\(f,v,r,g\). In particular the seventh row taps the sixth by \(g\).
This is one regular canonical branch of the
[Owren–Zennaro dense-order-five construction](https://doi.org/10.1090/S0025-5718-1991-1068811-2).
Work over a field paying \(10!\). Assume
\[
               f\,v\,(v-1)(v-2)(r-2)(r-v)\ne0 .
\]
Only this literal family, with these guards, is at issue.
Add a last row known to be a genuine order-five output at
a nonzero clock \(\theta\). Its derivative profile is then
ideal through size six. Suppose the grade-five decoder is exact
and its grade-at-most-five profile matrix has rank eight.

For a tree \(t\) subtract its ideal scalar value from every
stage profile to form its secondary defect vector. These
vectors vanish at both the old origin and the last pure row.
The rank of the actual profile table augmented by the six
ideal-grade columns is six plus the rank of the six remaining
secondary columns: each ordinary bush row has zero secondary
defect and separates its ideal-grade column. On the other
description using the exact decoder, the rank is eight plus
the rank of the size-six polynomial residuals; the residual
columns vanish through size five, where the eight actual
columns are already independent.

Three specific small secondary rows have a left \(3\times3\)
minor \(2/81\). Project the three chosen size-six rows onto
the kernel of these three small rows, keeping the last three
coordinates as the free coordinates. The exact projected
determinant is
\[
        -4fgv^3(r-v)(v-2)^3(v-1)^2/45 .
\]
The only variable inverse in this projection is \(r-2\).
Thus if \(g\ne0\), the secondary rank is six, and the size-six
residuals have rank four. Rank three in the regular chart
requires \(g=0\).

For \(g=0\), the replay verifies a constant linear relation
among six actual stage profiles in the first seven rows:
the coefficients on bush 3, tall 3, bush 4, tall 4, bush 5,
and the root with one leaf child and one tall-3 child are
\(-14/27,-8/27,1,-2,-1/3,1\), respectively. Applying the
order-five endpoint weights at \(\theta\) gives
\(-\theta^3(3\theta^2-15\theta+20)/90\).
A nonzero exact endpoint in this rank-three branch therefore
requires the discriminant \(-15\) to be a square. In particular
this branch cannot work over \(\mathbb Q\) or any ordered field.
The [prime-17 construction](../erk10-sixteen-f17/README.md)
uses precisely the other possibility: its quadratic splits there.
No conclusion is made about charts with collision \(r=v\) or about
other eight-stage continuous methods.

## Literal rational escape at the coincident donor clock

The [literal fixture](rational-prefix.json) takes
\(r=v=5/3,\ f=g=1,\ \theta=5/2\).
It has eight distinct physical rows despite the two repeated
scalar clock labels. This parameter choice is outside the
regular guard \(r-v\ne0\).
Its decoder has degree four and satisfies all 17 rooted profile
identities through size five. \(J\Pi(\theta)\), with \(J\)
integration from zero, equals the full last row with its own
zero coefficient appended. The size-six residuals vanish at
zero and \(\theta\) and have rank exactly three over \(\mathbb Q\).
The independent echelon receipt expresses every size-six
residual in the displayed three rows using only paid operations,
so their spanning statement also specializes to every ring
inverting \(10!\). The common matrix and decoder denominators
are 62208 and 1800.

This leaves a smaller three-test terminal payment problem
for an actual rational or factorial-localized ERK10 splice.
The prefix alone does not certify a successful splice.

    python3 -B audit.py
    sha256sum -c sha256.txt

The symbolic replay is exact; no inferences are based on
finite-field or floating-point rank tests.
