# Native certificate for the characteristic-17 cubic DIRK tableau

The literal width-15 method has exact order twelve over
\(\mathbb F_{17}[z]/(z^3+7z^2+3z+10)\). The modulus has no root in
\(\mathbb F_{17}\) and is irreducible; Lean verifies the quotient field
has dimension three over the prime field. This tableau is lower
triangular and its first two diagonal entries differ. Thus it is not
explicit and not of common diagonal. Its scaled order-thirteen bush
defect is \(11+7z+12z^2\), and its inverse is checked literally.

The proof replays the two complementary three-vector low bases, not a
large tree table. Every span coefficient is checked coordinatewise;
the proof does not rely on the generator's basis solve. Modular
three-coordinate arithmetic is reflected via evaluation at a true
cubic root, and the generic order theorem uses the repository's
actual \(\Phi\) and \(\mathrm{HasOrder}\). The same exact-order statement
works in any nontrivial commutative ring of characteristic 17
containing a root of the named cubic. This does not certify the real
degree-216 formula or Hensel lifts.

Run the generator with the previously archived
dirk12-fifteen-f17-cubic-midpoint-upper/tableau.json and a destination
Lean source path; its output should match DIRK12F17CubicData.lean
byte-for-byte. Kernel build order, under RKCert/ReviewedNative, is
DualSupport12, DIRK12F17CubicArithmetic, DIRK12F17CubicData,
DIRK12F17CubicCore, DIRK12F17CubicChecks and DIRK12F17Cubic. Then check
AuditDIRK12F17Cubic.lean. The included replay is Lean 4.36.0 with
matched Mathlib; the endpoint and unit witness use only the standard
propositional, choice, and quotient axioms.
