# ERK8: the only possible ten-stage characteristic is 11

**Later result.** The [characteristic-11 lower proof](../erk-eight-char11/README.md), combined with the outside-11 result, makes eleven optimal over every nonzero commutative ring with 8! invertible.

**Result, mathematical lower proof:** a nontrivial commutative ring with
invertible \(8!\) and nonnilpotent \(11\cdot1_R\) has minimum ERK stage
count **11** at order eight. This covers every admissible
characteristic-zero ring and field and every paid positive-characteristic
field except characteristic \(11\). More generally the only possible
characteristics of a nontrivial ring carrying an order-eight ERK method
with at most ten stages are \(11^k\), \(k\ge1\). There is no existence
claim at those characteristics. The separate eleven-stage
factorial-localized method is an exact order-eight upper bound even there.

The tagged census, physical localization and raw clean-head identity in
this packet are native Lean theorems. The Newton closure of the four-off
case and the complete one-off result remain source proofs. This packet
does not advertise a native end-to-end stage floor.

Write \(A\) for the literal strict-lower tableau, \(\boldsymbol b\) for
its weights, \(\boldsymbol c=A\boldsymbol1\), and
\(\boldsymbol g=A\boldsymbol c-\boldsymbol c^2/2\). Powers of vectors
are componentwise. A clean tag is a clock together with \(g_i=0\);
an off tag has \(g_i\ne0\). Coincident clocks on different tags are
not identified. Write \(E_j,F_j\) for the reviewed tree and defect
spaces.

## 1. Paid census, with the source of the 11 guard made explicit

Assume \(K\) is a field and the literal Fin 10 tableau has HasOrder 8.
The bush conditions make the casts of \(1,\ldots,8\) units. The actual
even horizon, paid forward separation and backward rank conditions are
valid over this field before any further prime exclusions.

The Hermite gain proof makes only bounded polynomial derivative calls:
an \(r\)-node gain uses a primitive of degree at most \(2r\). At an
already failed node, that primitive has value and derivative zero;
one new simple zero lifts the multiplicity count to \(2r+1\).
ERK8PaidNodalGain uses the reviewed native primitive map and assumes
only the bounded casts up to \(2r\) are nonzero. In the two-/three-off
exclusions \(r=2\) and no cast beyond the actual order is requested.
The zero-off contradiction uses the explicit quadratic seed and paid
separation. The six-off case uses the anchored order-eight Cauchy
test and width.

The five-clean cubic decoder does not require characteristic zero.
For the coefficient vector \((q_0,q_1,q_2,q_3)\), the three differently
scaled consecutive beta moment rows are
\[
  (10,5,3,2),\qquad (35,21,14,10),\qquad (42,28,20,15).
\]
The combinations \((28,-16,7)\), \((-112,74,-35)\), \((14,-10,5)\)
give respectively \(14q_0+q_3=0,\ 14q_1-9q_3=0,\ 2q_2+3q_3=0\).
It follows that the cubic is a multiple of
\[
 L(X)=(X-\tfrac12)(X^2-X+\tfrac17).
\]
The five-off and high-off exclusions of the census reduce to a
quadratic factor of \(L\) and its first-clean primitive at the omitted
clock \(u\). Their two scalar polynomials are
\[
 r(u)=14u^3-21u^2+9u-1,\qquad s(u)=91u^2-105u+27 .
\]
They are both zero, while literally
\[
 (464-819u)\,r(u)+(126u^2-115u+18)\,s(u)=22.
\]
This is the only extra prime guard of the checked census. Therefore
if \(11\ne0\) there are one or four off tags, and four off implies
five clean tags. This is the literal-HO theorem
RKResearch.Certified.Graded.ERK8PaidField.order8_paid_tagged_census.

## 2. Audit of the one-off branch

The published mathematical proof in
[one-off.md](../erk-eight-stage-floor/one-off.md) can be used over any
field with the order-eight units. Here is the denominator/guard audit
of its actual dependencies, rather than an inference from characteristic
zero alone.

| Part of the cited source proof | Nonzero numerical factors, or paid substitute |
| --- | --- |
| Forward ranks, separation, origin_of_single_off, normalized \(mDef_j\), seed invariance | Even-horizon and separation use actual HasOrder. Integrating \(F_j\to F_{j+1}\) is mat_zeroSpace with the actual budget instead of its CharZero wrapper; \(mDef_j\) uses \(j+1\) with \(j\le4\) in this proof. All rank and clock arguments are over a field. |
| First \(A\boldsymbol g\) receiver and the three square-amplitude branches (OneOffDebut, FirstH, AmplitudeTools, DependentSquare, IndependentSquare, Sources, Residuals, both Case…Calibration/Scalars and ConstantAmplitude) | 2 and 3 and their products/powers only. The separate Case II/III resultants are \(9ad^2(2d-a)\) and \(9a^2d(2a-d)\), with the factors in \(a,d\) nonzero proved in the respective branches. Other divisions are by the actual nonzero origins, changed amplitude, clock differences, or indicated normalizers. No quotient by a possibly zero resultant coefficient is used. |
| Quadratic and cubic normal form (NormalHead, NormalClock, NormalDependent, NormalSources, NormalCalibration, NormalScalars, GlobalNormal, CleanClocks) | Numeric factors in the calibration and clean-clock resultants are products of 2 and 3 (in particular \(9,12,32,36\)); variable denominators are the proved nonzero \(a,d,e,e-d,3d-2e\) and the nonzero initial amplitude. Invariance uses the paid defect transport and strict causality. |
| Physical PrefixSelectors, row merge, and reverse invariant capacity | The dual selectors divide only by \(a,d\), their powers and 2. A proved raw duplicate contracts to width nine; the paid even width-nine exclusion already holds over any field. The reverse contrast contradiction is paid at \((j,n)=(5,1)\) and uses only order eight and field operations. |
| Low-top kernel, degree-four terminal profile | The degree-\(\le2\) beta kernel is the degree-\(\le3\) decoder in §1 with coefficient 3 zero. The terminal cubic uses that same paid decoder, and the other anchored test is the native paid Cauchy detector. The endpoint evaluation of \(L\) at 1 is \(1/14\). |
| Seventh-row comparison and root contradiction | The two literal source-interpolation identities and master residual use 2, 3, 4, 5 and the proved nonzero \(a,d\). Distinct roots \(d,D=2d,z\), nonzero \(d,D,z\), and the denominator \(14\) are earned as in the cited proof. The final no-double gate requires only 5 and 7 nonzero. |

For clarity, the exact width-ten bridge used by that proof is unchanged.
The weighted \(E_5\) map has a one-dimensional relation with nonzero
degree-five coefficient and forces \(\boldsymbol g\,(A\boldsymbol g)=0\).
The two physically distinct clean \(D\) rows yield \(L(D)=0\); the
seventh-row comparison yields a second physical copy of the clean
\(z\) clock with different \(A\boldsymbol g\). Those two \(z\) rows
annihilate the degree-one terminal defect profile and yield \(L(d)=0\).
The paid ring-polynomial no-double test in ERK8UnorderedScalarGates
excludes \(L(d)=L(2d)=0\). In particular no finite-field case is hidden
in that final scalar exclusion. The source proof uses comparisons
only of chronological indices, not coefficient ordering.

## 3. Four-off geometry holds in every paid field, conditionally on four off

The rank and repeat proofs from
[the unordered packet](../erk-eight-unordered/README.md) are paid over
any field. In this conditional branch they do not themselves invoke
the \(11\ne0\) part of the census. The five clean aggregates are
nonzero by the integer beta certificate with output \(3\); the
physical horizon yields the unique repeat at row 8, clean rows
6, 7, 9, and the first nonzero clean \(h\) at physical index 4 or 5.
The early four off clocks are chronologically \(a,b,d,e\); the later
interior clean clocks are \(x,z\). The five clean clocks are
\(0,h,x,z,1\), with \(h,x,z\) the three distinct roots of \(L\).

The paid theorem actual_raw_head_of_order8_four_off gives, with no
guard on these output scalars,
\[
\begin{split}
 P&=\Theta(X-x)(X-z)+\kappa(5X^2-(4x+3h)X+2hx),\\
 \Theta E&=\kappa(x/3-h/4),\qquad
 E=h/4-(x+z)/3+xz/(2h),\\
 Q(\boldsymbol c)+\boldsymbol g R_2(\boldsymbol c)
    &=Q(1)\boldsymbol e_9,\qquad Q=XL .
\end{split}
\]
Here \(P\) has degree at most two and fits the quadratic defect on off
rows, and \(R_2\) has degree at most two. The Lean ratio is cleared by
\(12h\). The raw identity follows from five Hermite roots of the paid
primitive of \(X(X-h)(P-\Theta(X-x)(X-z))\); no division by \(E\),
\(\kappa\), or the leading coefficient of \(P\) occurs in producing it.

For \(11\ne0\), the scalar \(E\) is nonzero. In the center orientation
it is \(-11/168\); if \(h=(1-\omega)/2\),
\(\omega^2=3/7\), it is \(5/12+7\omega/12\), of norm \(1/36\).
The switched sign covers the other root. Since \(P\ne0\), this also
proves \(\kappa\ne0\).

The following elementary repairs handle clean-root guards without
losing any paid prime. For clean receivers, the clean-sender action on
\(XP\) equals the primitive of \(XP\), since the off-sender input is
\(\boldsymbol c\boldsymbol g\) and this transported defect vanishes
there in \(F_4\).
* \(P(0)\ne0\) follows from the two primitive tests \(P,XP\) at
  the first nonzero clean row: if \(P(0)=0\), elimination gives
  \(h^4p_2=0\), then \(3h^2p_1=0\). This paid calculation is used in
  the native census.
* \(P(h)\ne0\): otherwise the primitive of \(XP\) has double roots
  at 0 and \(h\), and a root at \(x\), since the prior clean inputs
  at 0 and \(h\) vanish. A degree-at-most-four polynomial with this
  multiplicity is zero. Differentiating with the paid units gives
  \(XP=0\), a contradiction.
* \(P(x)=\kappa x(x-h)\ne0\).
* \(P(z)\ne0\): let \(\boldsymbol r=\boldsymbol e_8-\boldsymbol e_i\)
  be the actual repeat contrast and set
  \(\boldsymbol\Delta=A^{\mathsf T}\boldsymbol r\).
  The four off aggregates of \(\boldsymbol\Delta\) are nonzero.
  The clean aggregates weighted by \(P\) kill the three powers
  \(1,X,X^2\), by subtracting the paid off-band action from the pure
  \(P X^j\) tests on \(E_4\). The terminal component is zero by
  strictness. If \(P(z)=0\), the remaining three clean aggregates
  would vanish by Vandermonde on \(0,h,x\). The pure tests through
  degree four would then kill every combined aggregate on the union
  of the four off clocks and \(z\). At least three off clocks do not
  equal \(z\), contradicting their nonzero aggregates.

These arguments cover the clean-root guard losses in characteristics
17, 43 and 79. They rely on exact clean/off tag separation;
a coincident clock is allowed and does not invalidate the last step.

## 4. Four-off closure, including the two linear specializations

Let \(D\) be the monic four-off hull and \(N_3\) the hull of the first
three off clocks. For \(11\ne0\) the actual \(P\) is nonconstant:
a nonzero constant would make \(I(XP)(h)=P h^2/2\ne0\).
By the terminal profile,
\[
 Q+P R_2=\sigma D,\qquad \sigma\ne0.
\]
Indeed the left hand side has degree at most four and vanishes at all
four off roots. It cannot vanish identically, since \(P\) is
nonconstant and is nonzero at all four clean roots of \(Q\).

Let \(C_r\) be the top cubic coefficient of the interpolant of \(X^r/P\)
on the four clean nodes \(0,h,x,z\). The top coefficients on \(D,N_3\)
are \(L_{4,r}=\sigma C_r\) and \(L_{3,r}=\sigma(C_{r+1}-e C_r)\).
For a quadratic \(P\), this is the exact division proof in
[four-off-closure.md](../erk-eight-stage-floor/four-off-closure.md):
with \(U_D,U_Q\) the degree-at-most-three interpolants,
\(PU_D-X^r=DV_D\), \(PU_Q-X^r=QV_Q\) give \(V_D=\sigma V_Q\)
modulo \(P\) and hence literally, by coprimality and their degree
bound one. Compare coefficients of degree five. For a linear \(P\)
the quotients \(V_D,V_Q\) are constants for \(r\le4\); here
\(\sigma=1\) by the leading term. The same calculation and the
degree-four coefficient (including the same \(-1\) on both sides
when \(r=4\)) give the transfer, with no quadratic division.
In both cases deleting the last off summand gives the three-node
formula.

The actual strict off-only Newton action raises each \(N_j\) into the
next \(N_{j+1}\) line on the four off rows. This follows for the first
two powers from their paid bands; for \(N_2,N_3\) it is just the
chronological zeros in a four-node space. Comparing the top
coefficients of the actual pure primitive outputs gives
\[
 \delta(C_r-e C_{r-1})+T h^{r-1}=C_r/r,\qquad r=2,3,4.
\]
The single possible clean tap is absent, \(T=0\), if the first clean
row is at position 5. There is no need for \(\delta\ne0\).

* At position 4, the three first-clean equations give that
  \(C_r-eC_{r-1}\) is a fixed nonzero multiple of \(h^r/r\).
  Elimination gives \(C_4-2h C_3+h^2 C_2=0\). The explicit raw
  \(P\) identity makes it equal to \(-(4z-2h)/P(z)\). This residue
  identity uses only \(P(x),P(z),\kappa\ne0\), not \(p_2\ne0\).
  Thus \(h=2z\), contradicting the paid no-double gate.
* At position 5, for a quadratic \(P\), the augmented determinant
  (multiplied by 12) is
  \((C_1C_3-C_2^2)(C_4-2(p_0/p_2) C_2)\).
  The recurrence \(p_0 C_j+p_1 C_{j+1}+p_2 C_{j+2}=0\),
  \(j=1,2\), gives the factorization. Both factors are nonzero
  in every admissible quadratic chart, as certified below.
* At position 5 with \(P(X)=p_1(X-\xi)\), \(p_1,\xi\ne0\)
  (the latter by \(P(0)\ne0\)), the same top residue gives
  \(C_0=-1/(p_1 Q(\xi))\ne0\). Indeed, evaluate
  \(P U_Q-1=Q V_Q\) at \(\xi\), with \(V_Q=p_1 C_0\).
  For \(j=0,1,2\), \(C_{j+1}=\xi C_j\) by the vanishing top
  pure polynomial moments on the four clean nodes. The \(r=2\)
  equation multiplied by \(\xi\) and the \(r=3\) equation therefore
  yield \(C_3/2=C_3/3\), impossible as \(C_3\ne0\). This repairs
  the linear charts in characteristics 37 and 41.

The script paid_four_off_scalar_guards.py certifies the exact scalar
checking scope. In the quadratic rational algebra
\(\mathbb Q[\omega]/(\omega^2-3/7)\) it computes the three clean
orientations and their conjugates using the literal barycentric
residues. It records prime factors in the norms of **all inverted
quantities** and of both final nonzero determinants. Thus the report
of possible scalar-guard changes is exact for this computation:
\(11,17,37,41,43,79\), excluding the factorial primes. Away from
these primes the calculation specializes via the actual
\(\omega=1-2u\) for one of the two quadratic clean roots \(u\) in the
coefficient field. At each of \(17,37,41,43,79\) the quadratic already
splits in the prime field; in an extension there are no other roots.
The script rechecks all six orders of those actual roots
without using any divided rational-pair formulas. The only degenerate
orientations are the three clean-root kinds repaired above and the
two linear kinds. All remaining quadratic determinant checks pass.
Thus the four-off closure never uses coefficient ordering or an
assumption that the coefficient field is itself prime.

## 5. Padding and the precise ring domain

The verified StagePadding.strict_stages_gt_of_exact_exclusion
pads every strict-lower \(s\le10\) tableau to width ten with literal
zero rows, columns and weights. This preserves all rooted order
conditions. Hence the two exhausted branches rule out every
\(s\le10\) over a field with \(11\ne0\). A nontrivial ring lacking
\(8!\) as a unit admits no order-eight method, by the bush equations
through order eight. There is no estimate of a finite minimum there.

For any nontrivial ring in which \(11\) is not nilpotent, localize
at its powers. This localization is nonzero: \(1=0\) in it would mean
\(11^j\cdot1_R=0\) for some \(j\). Take a maximal residue field; 11
remains a unit, hence the residue field has characteristic different
from 11. The unital coefficient map preserves the actual strict
lower property and literal rooted HasOrder. This proves the lower
over the original ring, irrespective of zero divisors or whether 11
was already a unit. If a smaller-width method existed with 11
nilpotent, \(11^j\cdot1_R=0\) forces its positive characteristic
to divide a power of 11; nontriviality rules out characteristic 1.
The independent factorial-localized tableau attains exact eight
with eleven stages whenever \(8!\) is a unit. This settles the
claimed exact domain; it leaves all \(11\)-primary rings and
characteristic-11 extensions as potential exceptions, not as
verified smaller methods.

## Verification and separate characteristic-11 diagnostics

Lean 4.36.0 + matching mathlib checked the native paid sources under
lean/RKCert/ReviewedNative. Dependency order:
ERK8PaidNodalGain, ERK8PaidPrimitiveTools, ERK8PaidLobatto,
ERK8PaidCensus, the four physical Rank/Repeat/Rows/Placement modules,
ERK8PaidCleanShape, ERK8FourOffCleanPrimitive,
ERK8FourOffCleanPlacementAdapter, ERK8FourOffTerminalProfile,
ERK8PaidPhysicalBridge. The earlier ERK8UnorderedScalarGates supplies
the nontrivial-ring four-site test. The native census and raw head
print their axiom receipts; they do not include a whole-floor
theorem.

Run the exact scalar guard certificate with:

    python3 paid_four_off_scalar_guards.py

A **separate** diagnostic, char11_high.py, tests the conditional
7-off high chart over \(\mathbb F_{11}\), with clean clocks
\(0,1/2,1\), quadratic \(P\) proportional to \(X^2-X+1/7\), and
the paid rank/primitive/reverse inputs. For its 330 possible
seven-clock supports, exactly 28 pass the weight moments;
114 ordered prefixes reach the joint linear system and none
passes. Reproduce with:

    python3 char11_high.py

The prior conditional \(\mathbb F_{121}\) four-off diagnostic is a
different chart. Neither diagnostic proves a full characteristic-11
census, a finite-field stage floor, or a positive result in an
extension field.
