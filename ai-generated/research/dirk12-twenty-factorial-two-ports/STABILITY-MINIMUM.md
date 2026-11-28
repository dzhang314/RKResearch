# The literal DIRK12 stability function needs twenty stages

No Runge–Kutta tableau with at most nineteen stages, even a fully
implicit one, has the same scalar stability function as this particular
[twenty-stage tableau](tableau20.json). This is a lower bound for exact
realization of a **fixed scalar function**, not for arbitrary order-twelve
methods. Another nineteen-stage method may have a different stability
function.

For an \(s\)-stage Runge–Kutta tableau with coefficient matrix \(A\)
and weight vector \(\mathbf b\), applying the method to the scalar
linear test equation gives
\[
 R(z)=1+z\mathbf b^{\mathsf T}(I-zA)^{-1}\mathbf 1
     =\frac{P(z)}{Q(z)},\qquad
 Q(z)=\det(I-zA),\qquad
 P(z)=\det(I-zA+z\mathbf1\mathbf b^{\mathsf T}).
\]
The second equality is the rank-one determinant identity over the
rational function field. Both determinants have degree at most \(s\),
and \(P(0)=Q(0)=1\). In the literal twenty-stage tableau, lower
triangularity and its two zero diagonals bound the degree of \(Q\)
by eighteen.

The coefficients belong to \(\mathbb Z[1/D]\), where
\(D=830216051280000\). The [independent replay](check-stability-minimum.py)
checks degree **20** for \(P\), degree **18** for \(Q\), and coprimality
after reduction at both 19 and 29, which do not divide \(D\).
The degree bounds show that these reductions preserve both degrees, so
the zero-versus-nonzero Sylvester resultant test also proves that
\(P,Q\) are coprime over \(\mathbb Q\). This remains true after
extension to any characteristic-zero field. A representation of the
same \(R\) must therefore have numerator divisible by \(P\), forcing
at least twenty stages. The same fixed-function lower bound holds
directly for the reduced tableau over any extension of either
\(\mathbb F_{19}\) or \(\mathbb F_{29}\).

In characteristic zero, matching this particular scalar series
through degree 39 would already force equality of the complete
function for a candidate with at most nineteen stages. Indeed, on
cross-multiplying, the difference has degree at most 39 and would
vanish to order at least 40 at zero. Merely attaining order twelve
does not require that stronger agreement.

## Replay

Run `python3 -B check-stability-minimum.py` in this directory.
The script reconstructs \(Q\) from the diagonal factors and \(P\)
from the first 23 scalar series coefficients, including the constant
one. It independently checks both determinants at 21 distinct points
over \(\mathbb F_{29}\), identifying both degree-at-most-20
polynomials. The 19 evaluations over \(\mathbb F_{19}\) are an
additional cross-check; the formal series recovery does not require
interpolation there. The [portable arithmetic transcript](stability-minimum-replay.txt)
gives all ascending polynomial coefficients. This addendum has no
separate Lean theorem; the literal order-twelve construction has an
[independent end-to-end Lean proof](NATIVE.md).
