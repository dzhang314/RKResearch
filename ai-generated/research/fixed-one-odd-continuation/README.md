# Exact rational order thirteen in 35 strict SDIRK stages

The fixed-diagonal-one family now has a native Lean witness of
**exact order 13 in 35 physical stages**, versus the previous
37-stage rational upper bound. The smaller unrestricted real-algebraic
upper bound and all lower bounds are unchanged. Exactness is the
nonzero 14-vertex bush defect. The same method is available as the
canonical integer-scaled literal [tableau-13.json](tableau-13.json).
The [proof receipt](../../lean/evidence/fixed-one-symbolic-order13-20261127/README.md)
records the exact source closure and replay procedure.

## What is verified

1. Keep the previously certified 26-stage order-eleven matrix \(A_0\)
   and weights \(\boldsymbol{b}_0\) unchanged. On the actual physical
   indices 18, 19, and 20 (zero-based), local covariances certify the
   normalized derivative column \(\boldsymbol{N}_t=F(t)\boldsymbol{\Phi}_t(A_0)\)
   is exactly the scalar monomial through size seven. This uses the
   existing order-eleven Gram trace with three different signed
   readout functionals. It does not rebuild or amend the witness.
2. Append a 12-site ordered block with old-to-new feed \(U\), new
   stage block \(B\), and quadrature weights \(\boldsymbol{w}\). The
   first three virtual rows are literal copies of the donor strict
   predecessor rows. The other three head sites are (-1301),
   (-1303), and the solved rational \(z\); the final six sites are
   (-10,-8,-6,-4,-2,0). The five paid weighted moments and two
   actual point observations give an invertible 7-by-7 mixed
   observation matrix. The third donor's strict predecessor is
   checked independently. These three whole predecessor rows are
   not inferred from coincident clock sites.
3. The finite matrix tests verify all new integrations through the
   six low monomials, both reverse adjoint identities, the old/new
   degree caps, and the scalar moments. For all normalized native
   rooted columns through target size plus decoration, a symbolic
   structural induction pays the output moment. For a low child
   it shifts the moment index on the strictly smaller base. For a
   high child the base is necessarily low, and the adjoint reads
   only proved smaller-child moments and paid old moments. In
   particular no tree of size thirteen is individually replayed.
4. The ordinary order and the next bush failure hold on the virtual
   matrix. Lean verifies literal equality of the strict predecessor
   rows with the intended original donors after removing the two
   self taps, and a causal redirection deletes only virtual rows
   26, 27, and 28. The folded tableau has (26+12-3=35) actual
   stages, lower triangular structure and every diagonal entry
   equal to 1. All actual rooted outputs, not merely their first
   thirteen layers, are invariant under this quotient.

The [generator](gen_symbolic13.py) consumes the unchanged order-eleven
literal. It computes the rational output of a block linear solve and
independently checks the finite symbolic conditions before writing the
physical literal and the Lean data. It needs Python with SymPy; the
proof of its outputs is in Lean, not dependent on trusting the Python
calculation. Its last-bush defect is the nonzero rational printed in
the receipt. No positivity of output weights or stability is claimed.

## Remaining native tasks at higher odd orders

The analytic continuation counts **46, 58, 72** at 15, 17, 19
are separate from this native order-thirteen proof. The small
[clock-pair inverse receipts](higher-mixed-inverses/) are separately
kernel-checked and are not dependencies of the order-thirteen proof.
They remove one linear-algebra obligation without assuming purity.

| Target | Old physical stages | Copied head donors | Retained fresh rows | Result |
|---:|---:|---:|---:|---:|
| 15 | 35 | 3 | 11 | 46 |
| 17 | 46 | 4 | 12 | 58 |
| 19 | 58 | 4 | 14 | 72 |

For each target (p=2q+1), a native application needs the previous
`HasOrder (2*q-1)` witness, `PureAt` through size (q+1) for
each retained bank donor, explicit block data, an exact feed
factorization through the old observation/predecessor rows, the low
integrated-column and two reverse-adjoint checks, the scalar
quadrature and next-bush check, and the literal causal quotient.
To continue again, pay the first unused grade on the protected new
head rows and transport their purity through that quotient. These
checks are scalar or matrix obligations, not an exhaustive
tree-enumeration requirement. Those applications are now checked separately in the [higher-order receipt](../fixed-one-higher-odd/README.md); they are not dependencies of the order-thirteen proof.
