# Three-clock completion of later ordinary forward reads

A standalone conditional adapter for the physical real midpoint DIRK12 construction. It does not define the grouped reverse taps or assert that their unproved primitive/annihilation checks hold.

After the five opening live rows are paid, a difference vector \(\mathbf w\) between the desired and actual forward live profile contributes nothing before zero-based row 10. Ghosts are allowed to have arbitrary \(\mathbf w\) because their actual output weights vanish. The late reflected labels are \(u,d,v,d,0\) in physical rows \(10,\dots,14\). The repeated label uses its literal aggregate mass \(b_{11}+b_{13}\), not separately positive or nonzero signed summands.

If \(w_{11}=w_{13}\), the three paid probes \(\mathbf b\odot\mathbf y^k\), \(k=1,2,3\), give
\[
 b_{10} w_{10}u^k+(b_{11}+b_{13}) w_{11}d^k+b_{12}w_{12}v^k=0.
\]
The literal terminal disappears because its reflected clock is zero. The three distinct nonzero clocks give a small exact Vandermonde test. For example, the degree-three mask \(Y(Y-d)(Y-v)\) isolates \(b_{10}w_{10}\), which is then zero. The actual real clock dictionary and nonzero live cardinal masses discharge the geometric guards; this is not a positive-weight proof. All four late nonterminal coordinates of \(\mathbf w\) must vanish.

## What supplies these hypotheses

The actual nonzero pair vector \(\mathbf G\) has opposite amplitudes just at stages 11 and 13. Native Lean proves the equality of the repeated-label forward reads from the literal identity \(A^{\mathsf T}\mathbf G=\lambda\mathbf G+\mathbf H\), orthogonality of \(\mathbf H\) to the entering scalar input, and the equal physical clocks on the pair. It does not assume an artificial equality of the two physical rows of \(A\).

For a scalar monomial entering at degree \(m\), any true reverse defect \((j+1)A^{\mathsf T}(\mathbf b\odot\mathbf y^j)-\mathbf b\odot\mathbf y^{j+1}\) that annihilates \(\mathbf c^m\) pays the forward pairing against \(\mathbf b\odot\mathbf y^j\), provided \(j+m+1<12\). This follows from the already proven scalar integration by parts, with no extra moment. The actual specialized conditional primitive theorem uses \(j=1,2,3\) and \(m\le7\). When all nonterminal coordinates are zero or have zero output weight, the terminal's value follows from the actual zeroth output pairing and \(b_{14}\ne0\).

For a nonzero desired profile subtract its ordinary nonterminal values before applying the three-clock test. In the quintic case the profile is a uniform multiple of \(X L_6'(X)\); its three scalar pairings vanish by the paid degree range and shifted Legendre orthogonality. The same elementary test applies to the compensated degree-six nodal input once the proposed profile's three pairings are paid. This avoids any need to form a degree-eight interpolating polynomial or prove a Hankel rank uniqueness lemma.

**Still required:** the fifth opening row, the actual grouped reverse tails, their true three reverse pairings, and the pair transfer and further reverse/grade-six proof. Neither the adapter nor its actual real specialization claims more. Build `DIRK12MidpointLateCompletion`, then `DIRK12MidpointRealLateCompletion`, and run `AuditDIRK12MidpointLateCompletion.lean` with the repository-matched Lean/Mathlib 4.36.
