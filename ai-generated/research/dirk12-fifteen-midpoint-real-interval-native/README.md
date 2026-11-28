# Native real root boxes and first unpaid bush for the midpoint construction

Lean verifies that the archived degree-36 equation has a real root \(x\)
in the named \(10^{-100}\)-width bracket. For every \(x\) in the bracket,
the recovered cubic in \(f\) changes sign across its separate
\(10^{-45}\)-width bracket. The intermediate value theorem gives a
simultaneous pair of real roots. The three moving support denominators
and the orientation discriminant are positive; hence both distinct
real quadratic orientations exist.

The directed rational evaluator rounds every arithmetic result outward
to the \(10^{-130}\) grid. Its soundness is proved over ordered fields,
independently of the particular data. Lean verifies the six enclosures
through the actual seven-factor moment recurrence
\(M_j((Y-r)P)=M_{j+1}(P)-rM_j(P)\) and checks all endpoint signs in the
kernel. No native compiler oracle or floating-point step is used.

For each \(x,f\) in the boxes the scaled order-thirteen star expression
is strictly between \(85680969483153/10^{20}\) and
\(85680969483154/10^{20}\), and is positive. The separate polynomial
bridge identifies this range with the actual reviewed rooted
size-thirteen bush **when** the literal weighted support and the
already-paid scalar degree-eleven quadrature hypotheses are supplied.
The kernel result does not yet build the whole real tableau or prove
its low forward/reverse flags; it is not a native proof of the full
real order-twelve endpoint.

Reproduce the inputs with the two Python generators, each taking
ai-generated/research and its destination Lean module. The first
copies the archived exact polynomials and boxes. The second proposes
convenient outer moment boxes; Lean recalculates and verifies them.

Compile modules in this order under RKCert/ReviewedNative:
DirectedRatBox, DIRK12MidpointRealIntervalData, DIRK12MidpointRealRoots,
DIRK12MidpointMomentBounds, DIRK12MidpointRealMomentInterval,
DIRKOrderTwelveMidpointStar, DIRK12MidpointRealStarBridge. Then check
AuditDIRK12MidpointRealInterval.lean. The included typed replay is
Lean 4.36.0 with its matched Mathlib; the audited theorems depend only
on propext, Classical.choice and Quot.sound.
