# Generic polynomial origin-moment differential criterion

Import [RKCert.ReviewedNative.OriginMomentDifferential](../../RKCert/ReviewedNative/OriginMomentDifferential.lean).
Its pure polynomial window combines a degree cap n+2, a double origin,
and the first n ordinary formal moments. The lower cap n+1 has zero
kernel by a finite Cauchy system. A polynomial differential operator
preserves the moment window, yielding a second-order identity for any
nonzero member. An independent regular-ODE criterion uses the drop of
root multiplicity under differentiation. Together they rule out
simultaneous roots of the polynomial and its derivative away from 0
and 1, over characteristic-zero fields. No Jacobi family, Runge–Kutta
order, tableau, clock placement or order-specific adapter is assumed.

The principal reusable interfaces in the
RKResearch.Certified.Graded.OriginMomentDifferential namespace are
Window.of_power, Window.eq_zero_of_lower_degree,
Window.exists_differential_scalar, derivative_eval_ne_zero_of_regular_eq,
Window.derivative_eval_ne_zero and its complementary implication
Window.eval_ne_zero_of_derivative_zero. The first only converts testing
bases; the root and differential assertions have the characteristic-zero
hypothesis present in the checked module.

## Measured stock checks

Stock Lean 4.36.0 with Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The initial body 83759 stopped on two proof lines. The
[repair ledger](measured-repair-chain.tsv) pins the actual cast and explicit
power-exponent diagnostics; precisely these two lines changed, with
identical declaration statements and provider path. Exact repaired body
39567 compiled, with [five lint warnings](body-diagnostics.txt). Its
portable diagnostic log changes only the original path prefix.

The [standalone typed audit](../../AuditOriginMomentDifferential.lean)
41851 elaborated five literal typed clients, emitted no object, and
[reported](typed-audit-output.txt) only propext, Classical.choice and
Quot.sound for the six named endpoints above. Its successful stock
transcript is byte-unchanged. Both measured successes used the already
accepted [generic native providers](generic-providers.tsv); the audit
merged the eight exact providers and measured body in one coherent
project projection. The [acceptance](acceptance.tsv) and
[fragment](stock-fragments.tsv) ledgers distinguish all three
measurements. No compiled objects or local execution paths are included.

Integration base checked: 6eb440cb3b8c138b84d807a166ab32dca0969bae.
No package configuration is changed. This is warm serial body and
typed no-output evidence, not a cold rebuild or separate leanchecker
run. For optional replay with pinned tools and dependencies installed,
from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-origin-moment-differential-20261125/added-sources.sha256
    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.OriginMomentDifferential
    lake env lean -j1 -M3000 AuditOriginMomentDifferential.lean
