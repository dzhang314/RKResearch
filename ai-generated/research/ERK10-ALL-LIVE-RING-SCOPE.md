# Ring scope of the all-live ERK10 equality exclusion

The [all-live ledger](ERK10-ALL-LIVE-COMPLETENESS.md) proves that
a strict 14-stage order-ten explicit RK tableau cannot have all
output weights nonzero over a characteristic-zero field.

* **Any characteristic-zero integral domain:** pass to its
  fraction field. If all coefficients \(b_i\) were nonzero,
  they stay nonzero there, and the ordinary rooted tests still
  hold. Thus a fourteen-stage tableau over the original domain
  has some \(b_i=0\). The ring need not be a \(\mathbf Q\)-algebra.
* **Any nonzero commutative \(\mathbf Q\)-algebra:** the product
  \(P=\prod_{i=1}^{14} b_i\) must be nilpotent in a fourteen-stage
  tableau. Otherwise the localization at \(P\) is nonzero;
  reducing at a maximal ideal then gives a characteristic-zero
  field with every \(b_i\) a unit. This is the excluded all-live
  case. In a reduced \(\mathbf Q\)-algebra the product is
  therefore zero. This argument does not force an individual
  weight to vanish in a reduced ring with zero divisors. In particular all weights cannot
  be units in any nonzero commutative \(\mathbf Q\)-algebra.

Localizing and reducing preserve strict triangularity and every
denominator-cleared rooted order equation. These are algebraic
reductions to the existing characteristic-zero field theorem,
not an unconditional numerical lower bound of fifteen and not
a bound asserted for arbitrary positive characteristics.
