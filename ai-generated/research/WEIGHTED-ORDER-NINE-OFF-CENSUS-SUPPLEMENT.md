# Small off populations and the seven-off boundary at weighted order nine

Supplement to [the 12-stage four-tap classification](WEIGHTED-ORDER-NINE-FOUR-TAP.md)
and [the shifted off gates](WEIGHTED-ORDER-NINE-OFF-GATES.md). The names
\(N,M\) count distinct off and clean **states**, respectively; a clock may
appear both clean and off. These short deductions are over paid fields
\((m+9)!\ne0\), without any order on the field. No new Lean bridge is asserted.

There are no \(N=0,2,3,7\) cases. The first two-curve arguments here are
forward arguments already used for ordinary order nine; only the weighted
moment and new endpoint bridge is needed.

* **\(N=0\).** There is a nonzero clock, since \(\beta c=\ell_m(X)\ne0\).
  At the first physical nonzero clock \(c_i\), all earlier clocks are
  zero; hence \(d_i=-c_i^2/2\ne0\).

* **\(N=2\).** The two independent vectors \(d,Cd\) span \(F_3\)
  in the exact midpoint ranks \(\dim F_3=2,\dim F_4=3\). Their span
  is \(C\)-invariant because the binary off clock polynomial kills \(d\).
  But a \(C\)-invariant \(F_3\) with separation through degree three
  and only one upward pure increment is impossible. Use the
  \(j=3\) proof in [the paid grade-five surplus](../lower-bounds/paid-beta/01-PAID-GRADE-FIVE-SURPLUS.md),
  specifically the paragraph excluding \(C\)-invariance of \(F_3,F_4\):
  compress \(E_3\) chronologically, decompose its defect annihilator
  by clocks, and test the first two nonzero clean completion rows
  against \((X^2(X-u)^2)'\). Separation is needed only through degree
  three and the pure increment only through degree four. The native
  algebraic pattern is the ordinary helper
  `RKCert.Paired.no_two_off_nodes` in
  `RKCert.ERKLowCurves`; its library's characteristic-zero signatures
  are not invoked as theorems over positive characteristic.

* **\(N=3\).** The saturated two-curve description
  \(F_4=d P_{\le2}(C)\) follows from \(d,Cd,C^2d\); the product \(d^2\)
  fixes its nonzero amplitude \(G(x)\) for each off clock \(x\).
  At every clean row \(i\), the fourth-degree pure directions vanish.
  In particular the incoming off charges
  \(r_i(x)=\sum_{j:\,c_j=x,\ d_j\ne0}A_{i,j}d_j\)
  have zero moments against \(1,X\), and the incoming ordinary
  clock powers satisfy \(A_i c^k=c_i^{k+1}/(k+1)\), \(1\le k\le3\).
  With three off clocks the two zero moments leave only one row direction.
  If \(h\) is the first nonzero clean clock, its off charge is nonzero:
  earlier clean clocks are zero, and if its off charge were zero then
  its \(A_i c=h^2/2\) equation would vanish as well (divide each off
  charge by its fixed nonzero \(G(x)\)). For each subsequent clean row
  whose predecessors have clean clocks only \(0,h\), its incoming
  off charges are proportional to this first row. Test its incoming
  coefficients on \(P'=(X^2(X-h)^2)'\). The off contribution equals
  that same multiple of the first row, where the primitive value is
  zero. The earlier clean contribution is zero since \(P'(0)=P'(h)=0\).
  The exact primitive \(P(c_i)=0\) forces \(c_i=0,h\), proving by
  induction that there are at most two clean labels. This is precisely
  the forward argument in `RKCert.ERKLowThreeOff.three_off_forces_two_on`;
  only the small divisions \(2,3,4\) matter in the argument above.
  Finally the weighted \(\beta C^k d=0\) moments cancel all three
  off aggregates, so its degree-eight quadrature needs at least
  five clean labels by the degree-four paid Gram. Contradiction.

* **\(N=7\).** Again \(F_4=dP_{\le2}(C)\) and \(G(x)\ne0\) is fixed
  on every off clock. All seven \(\beta C^k d=0\) moments
  \(0\le k\le6\) cancel the seven off aggregates. The same Gram
  forces \(M\ge5\), so \(N+M=12\): every state occurs on exactly one
  physical row. By the four-tap classification the active terminal
  row has clock 1. If that row is clean, the five-label clean
  quadrature has both origin 0 and endpoint 1. Divide its vanishing
  nodal polynomial by \(X(1-X)\); the resulting degree-three
  polynomial contradicts the nonsingular weighted Gram for
  \(X(1-X)^{m+1}\) against degrees zero through three. So the terminal
  row is off. Its state is unique, making its output zero by off
  aggregate cancellation, another contradiction.

Together with the four-off exclusion, the remaining off population is 1,
5, 6, or at least 8. For five off labels, five clean labels are excluded
at shift two outside the stated exceptional characteristic and seven
clean labels are excluded for all paid shifts. Six clean labels remain.
