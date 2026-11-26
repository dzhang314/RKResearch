# Checked rational first-bank quiet gain

The [native body](../../RKCert/ReviewedNative/RationalFirstBankQuietGain.lean)
uses the actual chronological one-zero-seed donor matrix \(A\) with
rational samples \(z_j=j\). Width \(n\ge3\) suffices, at every depth.
The physical seed is rank zero. Each first-bank row at rank \(1+j\)
reads only that seed, with coefficient \(j\).

Put \(c\coloneqq A\mathbf1\). At the three first-bank sites with clocks
\(0,1,2\), \(Ac\) vanishes since the seed clock is zero. Thus David's
denominator-cleared two-node defect
\(q\coloneqq\mathbf Q([\bullet])=2Ac-c^2\) has entries \(0,-1,-4\)
there. The actual singleton row taps \(1,-2,1\) at those sites have
zero constant and clock actions and exactly \(-2\) action on \(q\).
The native leaf and two-node normalized columns are exactly the
constant and clock, and exhaust the actual trees through order two.
The native endpoint states both Quiet through two and exact gain
on rootStageResidual and monomialStageDefect.

The [unchanged typed audit](../../AuditReviewedNativeRationalFirstBankQuietGain.lean)
checks the literal \(2Ac-c^2\) formula and the live leaf/two-node
equalities and gain on the actual rational matrix and row. Its
[exact log](typed-audit-output.txt) reports two names,
twoNode_residual_formula and contrast_quiet_gain, each with only
propext, Classical.choice, and Quot.sound.

The original body stopped at two adjacent graft-order proof goals.
The measured repair is one localized proof hunk exposing native
natural order and cancelling the two natural additions. The repaired
body and separate no-output audit both exited zero. Eleven original
nonfatal body warnings are unchanged apart from the declared line
shift; the typed audit emits no warning or object. The
[acceptance record](acceptance.json) records all three attempts and
the exact measured project/stock pins. These are bounded warm
measurements, not a cold package build.

The result is a local contrast, not a terminal weight construction,
a whole-tableau HasOrder claim, or a stage minimum.
