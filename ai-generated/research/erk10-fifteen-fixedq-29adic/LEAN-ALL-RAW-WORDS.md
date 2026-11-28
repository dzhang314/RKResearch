# All eight actual word columns on all eleven physical raw rows

The Lean 4.36 theorem
`RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_complete`
proves the strictly chronological actual \(K\), its action
on all eight physical raw input words at **every** row,
and the three fixed chronological ports of the actual
host. It applies to a commutative coefficient ring with a
local map to \(\mathbb F_{29}\) and the exact displayed
decic/head-root and residue hypotheses, not merely to its
modulo-29 reduction.

The new proof has four modules. `ZTailActual` binds the
portable ring readout to the actual head, decic, cardinal
and tail values, and obtains the degree-six polynomial
identity via seven paid evaluations. `ZTailPhysicalAlign`
identifies the normalized quadratic with the actual
three-node interpolation used by the cubic target.
`ZTailPhysicalRows` pays the actual scale and obtains
the exact zero \(Z\)-targets at the physical \(e,f\)
rows. Its `actualK_e` and `actualK_f` then pay all omitted
coordinates with the already checked strict support and
observer zeros. `WordAll` assembles the eleven actual
rows and the three ports.

The 11 reported kernel theorems use only standard axioms.
They passed in a combined direct-import document with the
portable solver already compiled and the existing `WordD`
chain imported. The canonical import target, from the
Lean package root, is:

    lake build RKCert.ReviewedNative.ERK10FixedQ29AdicWordAll

The checked endpoint is **physical word action**, not yet
the full rooted-order statement for the infinite lift.
The mathematical remaining filtered-grade, forward-decoder,
and rooted-tree steps are in `WORD-FILTER-TO-ORDER.md`.
