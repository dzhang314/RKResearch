# Structural results for even-order DIRK at the stage-count boundary

The setting is a diagonally implicit tableau over a characteristic-zero field satisfying the order conditions through order \(2m\), with \(3m-3\) stages. The general structural arguments use \(m\ge 7\).

The forward tree spaces and the reverse spaces reach the dimensions of their mutual annihilators in the range specified by the theorems. For \(m=7,8,9,10\), the last stage has weight \(1/(m(m+1))\). Its coordinate vector lies in the \(m\)-th tree-weight space. The polynomial part of that vector is a scalar multiple of the product of \(x\) and the derivative of the shifted Legendre polynomial of degree \(m\). Consequently, the abscissa at every nonterminal stage where all vectors of the \((m-1)\)-st residual space vanish is a root of that fixed polynomial.

At order sixteen, the physical grid can be combined with the reflected quartic obstruction. The resulting theorem excludes a nonzero quartic under the stated clean-stage and primitive-evaluation hypotheses; it does not assert that a candidate tableau necessarily satisfies those hypotheses.

These results retain the original physical stages, without assuming ordering, positivity, or the removal of zero-weight stages. They do not improve a numerical stage lower bound on their own.

Lean entry points: [`DirkFixedEvenBoundary.lean`](RKCert/DirkFixedEvenBoundary.lean), [`DirkEvenDual.lean`](RKCert/DirkEvenDual.lean), and [`DirkReflected16.lean`](RKCert/DirkReflected16.lean). Audit: [`AuditDIRKEven.lean`](AuditDIRKEven.lean).
