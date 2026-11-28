# A singleton-end S,D,D opener cannot face a doubled-end D,D,D opener

Let a strict ten-stage SDIRK tableau have ordinary order at least eight over a characteristic-zero field, with all ten physical quadratic defects nonzero, exactly seven distinct clocks, and exactly one singleton physical endpoint. Read the method from that singleton using the actual orientation (weighted mirror if needed). If its opening types are S,D,D, then the opposite opening **cannot** be D,D,D. Both literal star and arithmetic third-row phases are covered in each orientation. No sign, ordering, splitting, or non-Hermite assumption is used. This does not exclude rear D,D,S, D,S,D, or D,S,S, other single-end prefixes, or ten stages overall.

## Actual overlapping physical pairs

Use the [seven-clock geometry](../sdirk-eight-all-dirty-seven-clock/README.md). Let \(m=1/(2\gamma)\), \(H=2(m-1)\), \(y=x-1\) after normalizing the diagonal to one, and \(t=y-H/2\). The first physical singleton is at \(y=0\). Number the three D labels in their actual reverse order. The terminal is \(D_1=H\). With reverse gap \(v\), the other two labels in original \(y\)-coordinates are
\[
 (D_2,D_3)=(H-v,H-2v)\quad\text{in arithmetic},\qquad
 (D_2,D_3)=(H-v,H+v-2)\quad\text{in a star}.
\]
These are distinct from each other and the first singleton. The actual forward later labels are some ordered pair \((D_i,D_j)\), \(i\ne j\). Its gap is \(u=D_i\). Arithmetic requires \(D_j=2D_i\); a star requires \(D_i+D_j=2\). Either gives an exact affine line in \(H,v\); its coefficient of \(H\) is \(-1\) or \(2\), so eliminating \(H\) has no hidden field pivot.

The [single-end parity and clock census](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/PARITY.md) rejects two of the twenty-four ordered patterns by ordinary clock guards and six by centered or antipodal projection zeros. Its proof uses the characteristic-zero coprimality of \(L_3,L_4\) and the first singleton’s nonzero graph value. This leaves sixteen ordered lines. In the replay the same ordinary and parity removals are regenerated independently by checking the clock expressions that vanish identically on a phase line. All residual guards are kept, including \(u\ne2\) at a physical singleton first clock by the actual first-departure lemma. The reverse first clock is doubled, so reverse arithmetic \(v=2\) is **not** ruled out solely as a gap.

The forward defects at \(D_i,D_j\) are \(f_i,f_j\). At each of \(D_k\) the reverse defects in its normalized orientation are \(\rho_k\), with \(\rho_1=1/2\). In either orientation the later values for a gap \(z\) are
\[
  \tfrac12\kappa(z),\quad
  \begin{cases}
  \tfrac12\kappa(z)&\text{star},\\
  N(z)/(2D(z))&\text{arithmetic},
  \end{cases}
  \qquad
  \kappa(z)=1+2z-z^2,\quad D(z)=-2+z+4z^2-z^3,\quad
  N(z)=(1+4z-4z^2)D(z)+4z^2(3z-2).
\]
The star has distinct labels with \(z,z-1,z-2,\kappa(z)\ne0\), and arithmetic uses actual nonzero \(z,\kappa(z),D(z),N(z),3z-2\). Let \(\lambda\ne0\) be the true common conversion from reverse to original normalized defects. The two D labels \(D_i,D_j\) each occur in both prefixes, so at each of those labels the two distinct residual roots are precisely the front root \(f_k\) and the reverse root \(\lambda\rho_k\).

## Two necessary exact polynomials on every line

Let \(t_k=D_k-H/2\) and
\[
 L_3(t)=t^3-\tfrac35m^2t,\qquad
 L_4(t)=t^4-\tfrac67m^2t^2+\tfrac3{35}m^4 .
\]
The affine projection coefficient \(F_*\) satisfies \(L_3(t_k)=F_*(t_k)L_4(t_k)\) at all three D labels. Consecutive Legendre coprimality implies \(L_4(t_k)\ne0\). Thus the three actual scalar values \(J_k=L_3(t_k)/L_4(t_k)\) are collinear:
\[
                (J_2-J_1)(D_3-D_1)-(J_3-J_1)(D_2-D_1)=0.
\]
No division by the two clock differences is needed. This condition is valid also if the projection quintic or its singleton graph has a repeated root, or if a doubled clock happens to be a graph root.

At any D label the true two roots in \(g\) satisfy \(L_4(t_k)-g(A_2(t_k)+Bg)=0\), \(B\ne0\). Hence at both consumed double labels the actual stages, not a residual chosen arbitrarily from a quadratic, yield
\[
       L_4(t_i)=-B\lambda f_i\rho_i,\qquad
       L_4(t_j)=-B\lambda f_j\rho_j.
\]
Eliminating the common scale gives the second necessary polynomial:
\[
                  L_4(t_i)f_j\rho_j-L_4(t_j)f_i\rho_i=0.
\]
This elimination does not need the square roots of any residual quadratic, \(\lambda=1\), knowledge of the remaining D residual, or a division by the graph at a D clock.

Substitute each phase line and clear denominators only after checking that every nonconstant denominator factor divides the product of explicitly known nonzero guards. The two primitive rational-function numerators can then be checked by exact univariate gcd. The collinearity numerator has degree 12 in every surviving line. The third column below records the **raw monic gcd**, before excluding genuine reverse phase collisions; the fourth column is the overlap numerator’s degree. Reversed star pairs are listed as ordered occurrences, not obtained by claiming a permutation of rows preserves order.

| Forward/rear phase | Forward later D positions | Raw gcd | Overlap degree |
| --- | --- | --- | ---: |
| A/A | (1,2) | \(v^2\) | 11 |
| A/A | (1,3) | \(v^2\) | 14 |
| A/S | (1,2) | \(v\) | 11 |
| A/S | (1,3) | \(v-2\) | 11 |
| A/S | (2,3), (3,2) | \(v-1\) | 11 |
| S/A | (1,2), (2,1) | \(v\) | 8 |
| S/A | (1,3), (3,1), (2,3), (3,2) | \(v\) | 11 |
| S/S | (1,2), (2,1), (1,3), (3,1) | \(v(v-2)\) | 8 |

Every root in the table violates a literal reverse phase guard: \(v=0\) violates distinctness in either phase, and \(v=1\) or \(v=2\) is pruned only in genuine reverse star. Therefore the gcd is a unit on every actual branch. The proof uses only paid endpoint equations and true D products; normalized trace, fourth reads, Hermite resolution, or a special field extension are unnecessary. Its exact rational identities transfer to every characteristic-zero field, but the packet does not claim a finite-characteristic result.

## Replay and native scope

Run `SYMPY_GROUND_TYPES=flint python check_overlaps.py` (SymPy 1.14 and python-flint 0.8). The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticSddDdd.lean) checks the two denominator-free scalar identities. The rooted-order ingress and sixteen exact gcds are a mathematical proof with exact replay, not an end-to-end Lean theorem.
