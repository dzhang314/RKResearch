# Native physical head and weight adapters for ERK8 in characteristic 11

These additive Lean sources target the actual strictly explicit width-ten
tableau over a field with \(11=0\). They do not modify the published paid
census or literal order condition. They do **not** purport to establish the
entire ERK8 lower bound in Lean. The complete mathematical proof remains
in [the exceptional characteristic packet](../erk-eight-char11/README.md).

## What the new declarations assert

- **ERK8CharElevenOmittedHead.** The actual five- and seven-off arguments
  produce a quadratic fitted head before using the numerical resultant.
  The two paid omitted-factor scalars force the omitted clean clock
  \(6\), and hence \(P=\theta q\), \(\theta\ne0\),
  \(q=X^2-X+8\). The terminal is clean, at clock 1, with no other clean
  clock-1 stage. The literal earliest nonzero clean has clock 6 and
  at least three distinct off clocks precede it. At full tag count
  every same-tag representative is physically unique. As a consequence,
  five-off tagwise mass cancellation means every actual off weight is zero.
- **ERK8CharElevenFourHead.** The literal physical raw head splits by
  whether the first nonzero clean is 6 or a root of \(q\). If it is 6,
  the correction scale is zero, \(P=\theta q\) with \(\theta\ne0\), and
  the two later clean clocks have sum 1 and product 8. If \(q\) has no
  root in the whole coefficient field, the four- and five-off cases
  are excluded; the one- and seven-off cases remain.
- **ERK8CharElevenHighWeights.** In the actual seven-off case,
  \(b_i=\lambda /(q(c_i)D'(c_i))\) for every off row, with
  \(\lambda\ne0\) and \(D\) the hull of the seven off clocks. Lean
  expresses \(D'(c_i)\) as the equivalent nonzero erase-one cofactor.
  Removing any two off clocks creates a degree-five polynomial test.
  Its paid defect probe exposes exactly those two terms and equates
  the cofactor products. The scale cannot vanish: otherwise the
  quadrature would be supported on \(0,6,1\), contradicting its fixed
  nonzero paid integral of \(X^2(X-6)(X-1)\).

The original tableaux, weights \(\boldsymbol b\), clocks \(\boldsymbol c\),
and quadratic defects \(\boldsymbol g\) are never replaced by a merged
tableau. The argument allows a clock to occur under both tags.

## Separate paid one-off closing adapter

Over any field where the order-eight conditions are defined and paid,
**ERK8PaidOneOffClosing** pins the pure terminal polynomial to \(14XL\)
from its four equal paid probes, and closes once two distinct clean
clocks each have an observed repeated state with differing scaled
quadratic-defect values. Indeed the linear defect coefficient then has
two distinct roots, so vanishes. The first clean clock and its double
would both be roots of \(L\), impossible with just the order-eight
units. The paid forward and seventh-physical-row one-off chart is not
constructed here.

## Reproduction

From the certificate package, build only the new module targets:

    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.ERK8PaidOneOffClosing \
      +RKCert.ReviewedNative.ERK8CharElevenOmittedHead \
      +RKCert.ReviewedNative.ERK8CharElevenFourHead \
      +RKCert.ReviewedNative.ERK8CharElevenHighWeights

The four files passed an isolated serial replay on Lean 4.36.0 with
Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842 and the published review
branch prerequisites. See [the Lean log](lean-4.36-audit.txt) and the
[exact source digests](source-sha256.txt). All 11 audited declarations
depend only on the standard axioms propext, Classical.choice, and
Quot.sound. This is not an all-width lower bound, a complete paid
one-off proof, a final tail closure, or a full four-release matrix.

The mathematical tail branches are still separate: the four-off
terminal contradiction and the five- and seven-off reflected
chronology and scalar contradictions have not been connected to these
interfaces in Lean. The original mathematical minimum is unchanged.
