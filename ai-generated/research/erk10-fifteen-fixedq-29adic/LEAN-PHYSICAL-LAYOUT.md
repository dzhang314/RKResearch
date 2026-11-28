# Native weighted physical rows and fifteen-stage layout

This extends the separate cardinal and repeated-center/decoder modules.
The asserted physical vectors are the literal eleven raw rows in the
order \(0,a,b,c,c,26,e,f,6,h,15\), plus a scalar output weight at the
external origin ordinate 1.

* `Physical.raw_cardinal` proves actual quadrature for all polynomials
  of degree at most nine.
* `raw_u_marks`, `raw_weighted_eta`, and `raw_mixed_eta_u` prove the
  clock marks of \(\boldsymbol u\), \(\boldsymbol w\boldsymbol\eta\),
  and \(\boldsymbol u\boldsymbol\eta\) through degrees seven, five,
  and three, respectively.
* `raw_contact` proves the physical pointwise quadratic identity
  \(\boldsymbol w\boldsymbol\eta=Q(Y)\boldsymbol u\), including
  both center copies, the zero-score host, and the endpoint.
* `forward_host_nodes` links the same physical vectors to the first
  three forward raw rows via \(x=1-y\) and reverse indexing.
  `actual_forward_host_eta` proves the host dirt is exactly 1.
* `tableau15` turns the decoder into a matrix indexed by `Fin 15`.
  `tableau15_strict` uses the strict reverse word matrix;
  `tableau15_fifth` gives the exact physical fifth opening row.
  `tableau15_shared_tap` identifies the existing host tap from a raw
  quadratic-model receipt, rather than introducing a duplicate host
  stage. `tableauWeights` wires the same output scores.

The raw coefficient matrix is still an input of these tableau lemmas.
They do not certify existence of its eight-column action or a rooted-order
endpoint. This packet advances the unbounded characteristic-29 lift
formalization but does not change any stage bound or claim a Lean
certificate of the full \(29\)-adic witness.

Replay from `ai-generated/lean`:
`lake build +RKCert.ReviewedNative.ERK10FixedQ29AdicPhysicalLayout:olean`.
The accompanying log reports the actual Lean 4.36.0 kernel dependencies.
