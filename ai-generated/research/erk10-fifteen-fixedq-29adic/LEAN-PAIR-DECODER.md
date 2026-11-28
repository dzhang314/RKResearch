# Native repeated-center split and strict 4 + 11 decoder

The coefficient ring is any commutative ring with a local homomorphism
to \(\mathbb F_{29}\). The scalar inputs are the actual fixed-q decic
root and head values reducing to \(c=2,a=11,b=20\). The geometric archive
attached to `exact_nonlinear_limit` supplies these inputs.

* `Physical.actual_scale_unit` and
  `actual_head_denominator_units` check the exact cofactor scale and
  the opening denominators. `actual_eta_residue` reduces the exact
  quartic at all eight noncentral nodes; `actual_lambda_residue` reads
  the actual mixed moment used to split the center.
* `Physical.PairInput.split_equations` proves the exact pointwise
  \(\boldsymbol w\boldsymbol\eta=Q(Y)\boldsymbol u\) contacts of both
  physical center copies and the exact pooled weight, cofactor, and
  mixed contact. At the actual inputs the residues of
  \((W,U,L,Q(c),\Lambda)\) are \((18,25,8,8,11)\).
  The Möbius denominator reduces to 14, and the two rows have
  \((w,u,\eta)=(5,26,1),(13,28,15)\) modulo 29.
  `physicalPair_guards` and `physical_pair_independent` lift the units,
  not just nonzero field values.
* `Physical.actual_host_guards` pays all fourteen actual scalar host
  and opening guards, which include the early incidence and retained
  quadratic decoder determinants (residues 2 and 27).
  `actual_host_taps` reads the three actual forward seed taps
  \((6,3,13)\) modulo 29. `actual_host_contact` proves the exact
  quadratic and cubic model identities at those first raw rows.
* `Physical.HostInput.decode_reads` proves the exact three-coordinate
  retained quadratic decoder. `Physical.actual_physical_fifth` verifies
  the physical fifth row of the actual opening, when its raw clock is
  the true host. `physicalDecoder_strict` proves strict causality of
  the ordinal 4 + 11 block, given a strict raw block;
  `HostInput.shared_column` proves that an exact raw quadratic-model
  receipt makes the reconstructed host tap agree with the existing raw
  tap. There is no extra host row.

The eight raw word equations and whole-tableau rooted order still need
a native proof. The algebraic lift therefore is not yet a native
unbounded exact-order-ten tableau theorem.

Rebuild from `ai-generated/lean` after the nonlinear and cardinal modules:
`lake build +RKCert.ReviewedNative.ERK10FixedQ29AdicPairSplit:olean +RKCert.ReviewedNative.ERK10FixedQ29AdicDecoder:olean`.
The accompanying Lean 4.36.0 log records actual kernel axiom reports.
