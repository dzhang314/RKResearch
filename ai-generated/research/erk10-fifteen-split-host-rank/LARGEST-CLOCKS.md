# The three largest split-host clock geometries close

In the [rational split-host chart](README.md), let \(m\)
be the number of distinct nonzero raw high clocks after
reclassification and, for a \(p\)-host, the word-budget
erasure of the old \(q\) axis. Then:

* \(m=11\) is impossible.
* \(m=10\) with one physical high zero is impossible.
* \(m=10\) with the only pair at the endpoint is impossible.
* \(m=10\) with an ordinary pair survives only if its
  grade-two aggregate leaks and the reverse physical
  head is \(0,1,b,c,c\) after scaling the first nonzero
  reverse ordinate to one. In particular the unscored
  forward host is **not** paired, and the dirt uses at
  least seven clock labels by the [support lemma](COLOUR-SUPPORT.md).

These are fixed-geometry conclusions, valid for both
old hosts. No global split-host exclusion is claimed.
The rank-two local route below is rational (modulo-seven
guards), even where the reverse scalar determinants are paid.

## Three annihilators independent off the early reverse head

Every forward prefix containing at least four distinct
nonzero forward clocks already detects all three
dimensions of \(V\). Indeed restrict the rows and the
vectors \(T(f),\boldsymbol d,C\boldsymbol d,B\boldsymbol d\)
to that prefix. Causality gives exactly the same
equations there because no future column enters the
restricted \(B\)-read. Two independent forward rows
already exclude prefix rank one. If the host vector
is monochromatic on this prefix, its pivot projection
leaves at least three distinct flagged nonzero labels:
only its own clock could lose a flag. The first two of
those flagged labels force two independent projected
residuals, not just one. If the host vector is
multicolored on the prefix, the [rank-two row proof](README.md#dimension-two-cannot-contain-a-multicolor-host-vector)
uses only the first four distinct nonzero labels and
all interposed repeats/zeros, and makes the fourth
row impossible. Both are local arguments; the
Hilbert support used in the global proof to guarantee
existence of those labels is not needed here.

Consequently a purported extra observer annihilator
supported on a reverse prefix whose complement has
four distinct nonzero forward labels is impossible.
In all cases below \(m\ge10\) and the constructed blind
coordinates and same-clock contrasts are within the
first five physical reverse rows, leaving at least
five such labels. The host score itself may be zero;
nothing in the first-forward witnesses requires it.

## Shared grade-reduction rules

The raw first primitive is already exact, and the
last physical raw row (first reverse row) is live at
\(x=1\). All positive-grade defects vanish in this
coordinate. The grade-two seed \(\boldsymbol u\ne0\)
by its literal value at the first live nonendpoint.
Its seven positive tests imply that any nonzero
visible aggregate is supported at at least eight
distinct nonzero forward labels, with a unique
endpoint omitted where applicable. Then
\(D_4=\boldsymbol u\odot{\cal P}_2(\boldsymbol y)\):
the first two marks and itself are independent.
Marking a genuine quadratic multiplier shows
\(D_3=\boldsymbol u\odot{\cal P}_1(\boldsymbol y)\).
These arguments need the minimum support, not exact
one-dimensional interpolation of the aggregate.

For the sole ordinary pair or sole high zero, if
\(\boldsymbol u\) has no visible aggregate, the
pure physical space \(S\) is a single coordinate
mode: the opposite pair or the high zero. The
true grade-three image in the aggregate space is
one-dimensional. It cannot be zero (pure plateau),
and dimension two would already saturate the
grade-four aggregate cap two because of the nonzero
pure \(\boldsymbol u\). This would make it invariant
under the clock mark inside the kernel of the
positive linear probe, impossible by Vandermonde.
The strict one-label argument in the
[ordinary-pair proof](../erk10-five-opening-nine-label-one-pair/README.md#if-the-grade-two-aggregate-is-zero)
shows \(\boldsymbol h=K\boldsymbol u\) leaks.
That proof uses \(K\boldsymbol u=0\) under purity
and the strict submatrix \(N\) of the active label
before the first different live ordinate. It applies
to one high zero as well (there \(N=0\)).
Hence \(D_4=\langle\boldsymbol u,\boldsymbol h,
Y\boldsymbol h\rangle\). This fixes the literal
seed formulas in the exact two-copy or one-ghost
head proofs with no assumption about whether a
cofactor multiplier has extra roots.

## Eleven nonzero distinct clocks, or just one high zero

If all raw clocks are distinct and nonzero, the
grade-two seed has nonzero aggregate since \(S=0\).
Apply the first four physical nonendpoint calculations
of the [distinct-clock proof](../erk10-five-opening-nine-label-one-pair/TEN-DISTINCT.md);
the only old dimension argument used there is the
one just proved, together with early blindness.
The fourth distinct row forces the half-strength
identity, which contradicts the scalar \(X\)-moment.
The zero-strength branch was already excluded by
its own causal identity.

If exactly one raw high clock is zero and all other
ones are distinct, the same leakage argument works:
the invisible \(x=0\) is a distinct physical nonzero
reverse ordinate and contributes zero to the final
\(X\)-pairing. With \(\boldsymbol u\) pure, use the
[sole high-zero ghost proof](../erk10-five-opening-zero-high-largest/README.md#nine-distinct-visible-high-labels-pure-ghost)
through its determinant \(9b(z-b)(z-c)^2\).
The pure mode and grade-three formulas have just
been re-established at width eleven. The determinant
makes the fourth nonendpoint coordinate blind,
contrary to our prefix witness. The proof does not
require a nonzero physical ghost score in advance;
that score is earned at the first live nonendpoint.

## Only the endpoint repeats

All positive defects vanish at the first reverse
endpoint. Thus \(S=0\) on such defect vectors even
with the second endpoint: a pure vector must have
zero summed endpoint component. Grade two leaks,
and all the multiplier/rank formulas above apply.
If the two endpoints are consecutive, both defect
entries vanish by strictness (no positive ordinate
is available); their two coordinates give an early
contrast on the nominal columns as well. If the
second follows one interior, use the
[exact separated-jump determinant](../erk10-five-opening-first-endpoint-jump/README.md#the-next-compatibility-determinant-and-the-only-remaining-head):
its next fourth/fifth physical rows must contain a
repeated interior or have early blindness, neither
available here. If two or three interiors precede
the jump, use the respective paid
[augmented determinant](../erk10-five-opening-nine-label-endpoint-repeat/README.md#all-other-kappa-are-incompatible-with-the-allowed-positions);
four or more earlier interiors instead give the
ordinary first-four determinant before the jump.
Together with the separate zero-strength transfer,
all these yield the same paid half-strength causal
contradiction even through the endpoint jump.
No late cardinal arithmetic is used.

## Only an ordinary pair repeats

If grade two is pure, the single active pair mode,
one-dimensional grade-three aggregate and actual
\(K\boldsymbol u\) leakage were proved above.
The [pure ordinary-pair head closure](../erk10-five-opening-nine-label-one-pair/README.md#if-the-grade-two-aggregate-is-zero)
requires exactly these profiles, no repeat at any
other nonendpoint ordinate, and no early contrast.
Its first-five calculations close this case.

If grade two leaks, its affine and quadratic
multiplier formulas again apply. The
[first-four paid calculations](../erk10-five-opening-nine-label-one-pair/README.md#fourth-physical-interior-exact-5-by-5-compatibility)
then force the early head \(0,1,b,c,c\), with
\(c(2\kappa-1)=4b\kappa\) and \(\kappa\ne0,1/2\).
But the old terminal proof had four singleton
rows after the first new \(d\). Here there are five,
so its degree-four blind interpolation cannot be
reused without an additional relation. In particular
the exact zero score at the last raw reverse host
does **not** imply a zero \(K\boldsymbol Z\) there:
that row could still read prior weighted defects.
The last host is a singleton distinct from \(c\),
since the only pair has closed in the head; the
monochromatic option would need a second copy
of the host and is therefore impossible by the
[directional support lemma](COLOUR-SUPPORT.md).
