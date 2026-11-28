# Native low reverse primitives of the real midpoint tableau

This is the independently auditable completion of the low adjoint hypotheses
in [the physical reverse assembly](../dirk12-fifteen-midpoint-native-reverse/README.md).
The exact grouped extension is now connected to the verified five-head
function, so it can directly use the existing actual forward row theorems.
No free tail entry or uninstantiated grouped-return premise remains here.

For the actual real physical tableau \(\mathit{A}\) and actual
\(\mathbf W(Y^j)=\mathbf b\odot\mathbf y^j\), put
\[
 \mathbf E_j=\mathit{A}^{\mathsf T}\mathbf W(Y^{j-1})
                       -\mathbf W(Y^j)/j,\qquad j\ge1.
\]
The following are Lean vector equalities on all fifteen physical coordinates:
\[
 \mathbf E_1=0,\qquad
 \mathbf E_2=0,\qquad
 \mathbf E_3=\mathbf G,\qquad
 \mathbf E_4=(3d/2)\mathbf G+\lambda\mathbf H.
\]
The typed audit uses the existing integer-scaled form of these same errors.
The geometric box hypotheses select the two actual roots and orientation; the
two polynomials are assumed zero. All signed weights and three clocks are
the previously verified actual ones. The degree bounds refer to true
positive entering powers, not a projected tableau.

## Actual hidden and origin rows

For every physical ghost column \(g\), the true \(\mathit{A}^{\mathsf T}\)
read at entering reflected power \(j=1,2,3,4\) is zero. The literal origin
row is zero, all four physical ghost weights are zero, and the literal
terminal has reflected clock zero, so these positions do not contribute.
The nonterminal ordinary entries are exactly the known ghost taps
\[
  \ell_g\left[\alpha X L'_5(X)+(\mu+\nu c_g)X L'_6(X)
                             +\gamma X L'_7(X)\right].
\]
The three terms are paid by exact scalar quadrature: the largest product
degree is \(4+7=11\), and every positive-power probe in this range vanishes.
No unstated root comparison or numerical test is needed.

The reverse origin coordinate is forced by zero total from the actual
row sums and mixed scalar integration; it is not specified independently.
The full reverse errors at entering powers \(1,2,3\) annihilate all
ordinary powers through degree seven. These are exactly the silent
tests for the three-clock late forward adapter.

## Scope and remaining native conditions

The fourth positive entering power is checked on physical ghosts in this
packet, **not** on all ordinary live rows. No complete order-twelve theorem
or new stage number is claimed by this native step. A short route to the
remaining native tests avoids the five expanded local quartic comparisons:

1. Use the actual pair identity, the three paid reverse probes just
   checked, and the five actual opening rows to finish the late
   elementary forward cuts (including the quintic profile).
2. Apply the same three-clock uniqueness to the reflected degree-six
   nodal input \(Q^\#\) whose roots are the opening labels and origin.
   The candidate nonterminal defect is
   \(\Lambda(u-Y)Q^\#-\int_Y^1 Q^\#+\text{the literal ghost feed}\),
   a polynomial of degree at most seven. Its first five live reads have no
   remaining non-ghost tap term because \(Q^\#\) vanishes at their donors.
3. The fourth paid pairing of this profile is a native-sized target:
   degree \(4+7=11\), and its ordinary part is the denominator-free
   paid-pair-three moment equation from the exact \(Q_{36}\) relations.
   Adjoint integration then shows \(\mathbf E_5\) annihilates degree
   at most six (monomials through five and the monic nodal input).
4. The space of those annihilators supported away from the ghosts and
   terminal has generators \(\mathbf G,\mathbf H,Y\mathbf H\): first
   collapse the physical pair; subtract a two-label fit to the
   barycentric amplitudes; then the seven remaining distinct labels
   are separated by degree-six cardinal polynomials. The same space
   contains \(\mathit{A}^{\mathsf T}\mathbf H\), since every degree-six
   scalar input has a degree-at-most-seven nonterminal image and the
   physical ghost taps are degree-at-most-seven. These latter steps
   still need their native certificates.

Build the three modules with common prefix **DIRK12MidpointReverse**
in order Ghost, ActualLow, LowAudit after the physical reverse packet.
Verified against matched Lean/Mathlib 4.36.0 with standard logical
axioms. A cross-release Mathlib sweep is not asserted.
