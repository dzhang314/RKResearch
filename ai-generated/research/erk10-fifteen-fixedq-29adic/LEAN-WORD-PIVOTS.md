# Native strict chronological word solver and first complete prefix

The fixed-q reverse word input matrix uses the eight columns
\(\boldsymbol w,Y\boldsymbol w,Y^2\boldsymbol w,Y^3\boldsymbol w,\boldsymbol u,
Y\boldsymbol u,\boldsymbol G,\boldsymbol Z\), in this order. The last
two columns are swapped relative to the algebraic builder so that every
cut uses the same leading-column convention.

* `actual_word_input_mod` proves the reduction of the actual \(11\times8\)
  matrix, including the repeated physical center rows.
* `actual_lead_paid` pays all the leading \(k\times k\) determinants,
  \(0\le k\le8\), over the actual commutative local coefficient ring.
  The kernel checks explicit residue inverses. The independent replay
  gives nonempty determinants \(2,4,24,20,20,16,18,16\bmod29\).
* `chronologicalK_selected` makes the strict row solve from these paid
  cuts. `actualK_late` closes all **eight** actual word identities on the
  final three reverse rows. `actualK_ports` proves the real three fixed
  forward seed taps are preserved in the strict reverse chronology.
* `actualK_first` and `actualK_second` close all eight identities at
  the endpoint and first live node \(a\). The latter uses the exact
  first physical cofactor ratio, not a residue-only check.

The same strict \(K\) pays each earlier selected cut. The remaining
overdetermined columns of the reverse rows at \(b,c,c,d,e,f\) and the
rooted-order endpoint need further native checks. This packet alone
does not certify the unbounded order-ten tableau.

Replay:
- From `ai-generated/lean`, run
  `lake build +RKCert.ReviewedNative.ERK10FixedQ29AdicWordTarget:olean`.
- From the repository root, run
  `python3 ai-generated/research/erk10-fifteen-fixedq-29adic/word-pivots.py ai-generated/research`.
