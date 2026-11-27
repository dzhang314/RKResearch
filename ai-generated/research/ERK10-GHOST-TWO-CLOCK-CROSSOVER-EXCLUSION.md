# A grade-seven crossover excludes two outgoing clocks at the single invisible ERK10 ghost

Work over any characteristic-zero field. Assume a strict fourteen-stage
order-ten tableau with one zero output coefficient and an entirely
invisible quadratic defect. The
[single-ghost ledger](ERK10-SINGLE-INVISIBLE-GHOST.md) shows that the
ghost is physical row 2, its indicator \(e_2\) is pure of grade two,
and the actual outgoing column \(r=Ae_2\) is pure of grade three.
**There cannot be exactly two numerical clocks on the nonzero support
of \(r\).** This does not claim a lower bound of 15 for unrestricted
ERK10, or exclude the one-clock and three-or-more-clock ghost charts.

Suppose those two clocks are \(\alpha,\beta\). Write
\(u=B_I^{-1}h_2/2\) for the actual quadratic defect of the live
reversed tableau, with \(I\) its live sites. The base ledger proves
the following facts by paid low-degree tests, not by an assumption
of full reversed order:
- On each active label \(x\), \(u_i=a_x r_i\); both localized rows
  \(b r{\bf1}_{c=x}\), \(x=\alpha,\beta\), annihilate \(E_6\).
- With a genuine \(z\in F_4\) complementary to
  \(\langle e_2,r,Cr\rangle\), set
  \(Q_x=\sum_{i:c_i=x} b_i r_i^2 z_i\). At least one of
  \(a_\alpha Q_\alpha,\ a_\beta Q_\beta\) is nonzero. This was
  forced by the actual reverse square escaping the linear
  grade-four reverse room, using the two tests \(z,Cz\).
- The true row \(h_2=2bYA-bY^2\) annihilates **all** of \(E_7\).

The new crossover is the **actual coordinatewise product** \(r z\).
As \(r\in F_3\) and \(z\in F_4\), it is a pure rooted vector of grade
seven; this product needs no grade-eight extension or division by a
ghost weight. Thus
\[
       0=\tfrac12 h_2(r z) = a_\alpha Q_\alpha+a_\beta Q_\beta .
\]
Both terms are consequently nonzero. If the nonzero amplitudes of \(r\)
were constant, say \(\rho\), within either label, then there
\(Q_x=\rho\sum_{i:c_i=x}b_i r_i z_i=0\), by the localized annihilator
tested on the actual \(z\in F_4\subset E_6\). So each label is nonuniform.

The same localized rows tested on \(1,r,r^2\) give
\(\sum_{i:c_i=x} b_i r_i^j=0\) for \(j=1,2,3\) separately.
For at most three distinct nonzero amplitudes Vandermonde in the
amplitude variable forces each amplitude's pooled weight to be zero.
With all physical weights live on these rows, a nonuniform label
therefore needs at least four physical occurrences.
The two-clock chart would have **at least eight** outgoing nonzero
taps.

This contradicts the
[fixed-quartic and small-clean-count exits](ERK10-SINGLE-GHOST-TWO-CLOCK-CLOSURES.md).
Indeed at most five of the thirteen live physical rows would then
be clean. Four distinct clean clocks are required by the anchored
\(G\)-weighted moment matrix, and the exact fixed-quartic exit excludes
that case even with a repeated clean row. The only other possibility
is five distinct clean physical rows, excluded by the paired linear
grade-five contact calculation. The longer seven-active-tap modular
census is not required for this final contradiction.

[ERK10GhostCrossoverGate.lean](../lean/RKCert/Research/ERK10GhostCrossoverGate.lean) checks
the sign-free scalar crossover, the uniform-amplitude cancellation,
and the final physical count. The stage-profile and paid row bridges
are the above mathematical reductions using the already verified
base packet.
