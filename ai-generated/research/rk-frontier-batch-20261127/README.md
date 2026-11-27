# RK frontier work, 27 November 2026

These are new supporting claims and exact witnesses, not a replacement for
the unrestricted stage table. The separate Mathlib-free/core and native
certificates target the reviewed rooted-tree definitions where applicable.

## Weighted explicit order nine

For the order-eleven detector's derived weight `L₂(P) = ∫(1−x)²P(x)dx/2`
on [0,1], the moments are 1/[(k+1)(k+2)(k+3)]. The
[Lean moment certificate](../../lean/RKCert/Research/WeightedOrderNineGram.lean)
checks all entries of the fixed Gram factorization over the rationals.
[The positivity proof](../../lean/RKCert/Research/WeightedOrderNineGramPositive.lean)
transports this certificate to any ordered field, writes the quadratic form
as positive weighted squares, and recovers a nonzero input coordinate by
back substitution. This proves the positive polynomial component needed in
the signed-support argument, not the support argument itself and not an
order-eleven exclusion.

## Strict explicit order eight in characteristic 41

The [reviewed-tree certificate](../../lean/RKCert/ReviewedNative/ERK8Characteristic41.lean)
uses the 11-stage Cooper–Verner tableau reduced at the square root 12
of 21 in Z/41. It checks the strict triangular shape, all reviewed order
conditions through order eight, and a failed ninth-order bush.
This file is a direct check of the literal exceptional-characteristic
tableau, independent of the characteristic-cover argument using Shanks.

## Rational strict SDIRK at orders nine and eleven

The [literal tableaux](../fixed-one-newton/) are exact
rational constructions with common diagonal 1 and 18 and 26 stages,
respectively. These improve the prior rational upper witnesses of 19 and 28
stages; the real-algebraic endpoints stay unchanged. A second
[exact checker](../fixed-one-newton/check-independent.py), independent of tableau generation,
uses integer stage numerators and the ordinary unordered rooted-tree
recursion. It checks all 486 and 3,047 order conditions respectively and
checks that the next bush fails. Run it from the `fixed-one-newton` directory:

```sh
python3 check-independent.py tableau-9.json tableau-11.json
```

The JSON format uses one common denominator for the stage matrix and one
for the output weights. The independent replay alone is not a Lean proof. The separate [integer
Gram certificate](../rooted-tree-gram/README.md) kernel-checks the
18-stage order-nine and 26-stage order-eleven witnesses in Lean 4.36. See
its reproduction receipts for
which exact files and versions were tested.

## Other coefficient-domain endpoints

- [Eleven or twelve stages for explicit order eight](../erk-eight-finite-characteristic/README.md):
  the formal characteristic cover includes all factorial-admissible fields
  and all factorial-admissible positive-characteristic commutative rings.
- [Strict SDIRK order six in characteristics 11, 17, and 187](../sdirk6/characteristics-11-17.md)
  and [three more prime characteristics](../strict-sdirk-endpoints/README.md):
  exact native Lean witnesses supplement the existing six-stage lower bound.
- The [quadratic-field example in characteristic 3533](../strict-sdirk-endpoints/quadratic3533.json)
  gives an exact six-stage method over the degree-two extension. The new
  [lower certificate](../sdirk6/small-characteristic-exclusions.md) makes this
  sharp: the minimum is seven over the prime field, and over any field of
  characteristic 3533 it is six exactly when 2077 is a square. The same lower
  certificate makes seven sharp in characteristic 7.

## Supporting lower-bound arguments

The [four-word weighted ERK restriction](../WEIGHTED-ORDER-NINE-FOUR-TAP.md)
and the [DIRK Volterra restriction](../causal-profile-reduction/zero-diagonal-volterra-bridges.md)
narrow equality cases without changing the unrestricted lower bounds. Their
local Lean modules are separate from the mathematical bridge arguments.

The follow-up [weighted ERK support census](../WEIGHTED-ORDER-NINE-OFF-GATES.md)
and [DIRK crossed-pivot restrictions](../causal-profile-reduction/dirk-order10-crossed-cubic-pivots.md)
further constrain the surviving equality cases. The mathematical bridges
and locally formalized lemmas have distinct scopes. Neither research lane
has proved a new unrestricted stage floor.

The [high-off branch](../WEIGHTED-ORDER-NINE-HIGH-OFF.md) excludes at
least eight distinct off clocks for shift-two weighted order nine with
twelve explicit rows and an active final output, over any characteristic-zero
field. It does not need an ordering. Its [scalar Lean certificate and
replay logs](../../lean/evidence/weighted-order-nine-high-off-20261127/)
are separate from the mathematical rooted-order argument. Remaining branches
still prevent an unrestricted ERK order-eleven stage improvement.

The six-off cases with [five clean clocks](../WEIGHTED-ORDER-NINE-SIX-OFF-FIVE-CLEAN.md)
or [six clean clocks](../WEIGHTED-ORDER-NINE-SIX-OFF-SIX-CLEAN.md) are also
excluded for the same shift-two problem in characteristic zero. The
[core Lean replays](../../lean/evidence/weighted-order-nine-six-off-20261127/)
check the new arithmetic and terminal-state gates, not the entire
weighted rooted-order reduction. The last [one-off](../WEIGHTED-ORDER-NINE-SINGLE-OFF.md) and
[five-off/six-clean](../WEIGHTED-ORDER-NINE-FIVE-OFF-SIX-CLEAN.md)
branches have now been excluded. This gives a mathematical lower bound of
13 stages for shift-two weighted order nine in characteristic zero. The
[core Lean replays](../../lean/evidence/weighted-order-nine-shift-two-20261127/)
verify separate gates. These are not end-to-end weighted order certificates.
The ordinary order-eleven lower bound has not changed.

## Algebraic coefficient verification and a strict SDIRK7 obstruction

The [coordinate-trace Gram verifier](../coordinate-rooted-tree-gram/README.md)
proves the reviewed tree-order tests using integer coordinates in an
integral multiplication basis. It verifies exact Gauss order four over a
real quadratic algebra and detects a failure over the imaginary quadratic
algebra even when the two field-valued residual squares cancel. This is a
Lean-checked verifier extension, not a stage-bound change.

The [six-tail scalar obstruction](../strict-sdirk7-six-tail/README.md)
excludes two specific rational compression routes at order seven and
separates the mathematical reductions from the Lean arithmetic. It does
not exclude arbitrary nine-stage rational tableaux or eight-stage tableaux
over ordered fields.
