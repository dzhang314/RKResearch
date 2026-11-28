# Native degree-36 moment gates for the real midpoint scalar quadrature

From the archived exact equations for the real \(x,f\) branch, Lean
proves both actual support moment relations
\[
  B n_3-2(n_1n_2)n_2=0,\qquad
  A n_4-5(n_1n_2)n_3=0.
\]
Here \(n_j\) are the unit-interval polynomial moments of the seven
fixed reflected nodes, not independently defined field elements.
The sampled points and the root enclosures are not used to infer
equality.

Each \(n_j\) is affine in the physical fifth clock \(f\), so each
equation is cubic in \(f\). Its three lower coefficients, after
multiplying by a common rational denominator, agree with the
archived monic cubic coefficient ratios modulo the exact primitive
degree-36 polynomial. The six polynomial comparisons use signed
integer packing at \(2^{3840}\). Each kernel check is one exact
integer Horner equality and an independently verified bound on the sum
of the absolute polynomial coefficients. These force the underlying
integer coefficient identity, since a polynomial with smaller
coefficient norm cannot vanish at that base unless all coefficients
are zero. The proof does not perform costly dense reductions in Lean.

The ten packed affine coefficient arrays for the \(n_j\) are also
checked by the same polynomial identity test against the normalized
six-node moment recurrence. Shared denominator casts then connect
them to the actual real moments and to the allowed \(x,f\) equations.

The resulting native endpoint gives scalar interpolation quadrature
through degree eleven on ten distinct sites listing the prescribed
hull. It uses generic Lagrange quadrature with two annihilated hull
moments. This packet does not certify the remaining physical forward
and reverse low-band conditions of the width-fifteen RK tableau;
there is no full native real Runge–Kutta order theorem here.

Rebuild the seven generated data files using generate-packed.py with
the archived field.json and a destination directory. It uses
python-flint for exact integer polynomial quotient candidates; the
Lean proofs verify those candidates independently. Compile the
previous real interval and moment-transfer modules first, then:
IntegerPolyRootReplay, IntegerPolyPacking, IntegerPolyClearDen,
PaidNodalQuadrature, DIRK12MidpointScalarQuadrature, DIRK12Q36MomentData,
DIRK12Q36PackedGatesCore, the six DIRK12Q36PackedGate modules,
DIRK12Q36MomentReflect, DIRK12Q36RealMomentDataBridge,
DIRK12Q36RealMomentChecks, and DIRK12Q36RealScalar.
The independent imported audit and full source checks use Lean 4.36.0
with matched Mathlib; the printed dependencies are all standard axioms.
