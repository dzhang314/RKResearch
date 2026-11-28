# Native exact-order assembly on the actual width-15 tableau

The checked Lean 4.36 theorem
`RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_exact10_of_three_edges`
has the actual 15-stage `tableau15` and actual physical
weights in its conclusion. In any commutative ring with
the given local residue map and decic/head root premises,
it proves strict explicitness, `HasOrder 10`, and the
negation of `HasOrder 11` **provided**
`MinimalEdgeReceipts` holds for these actual parameters.

That hypothesis comprises precisely three **linear or
early physical edge fields**, with actual tree sizes:

- For a child of size at most 3, if its raw stage defect
  is already zero, its true unary-edge defect is zero.
- For a size-4 child whose raw stage defect is zero, its
  true unary-edge defect lies on the actual host line.
- For sizes \(m=5,\ldots,9\), an actual stage defect in
  \(N_{10-m}\) yields an actual unary-edge defect in
  \(N_{9-m}\).

These are **not yet discharged** by this packet.
The first two will come from the projected low old-stage
decoder and the two global forward host laws. The third
needs the paid adjoint transport and residual pairing of
`WORD-FILTER-TO-ORDER.md`. In particular proof of the
eight actual words alone does not certify rooted order.

Everything else in the assembly is checked. `OrderSlots`
joins the four retained and eleven reverse-indexed actual
slots and the exact raw block action. `OrderAnn` proves
the forward mark shifts and all three actual nonlinear
product fields from the literal weighted host contact.
`OrderAttach` uses the actual `RKCert.Tree` with its exact
matrix stage-weight recursion, not a modeled tree shape.
`OrderOutput` pays the actual cardinal/scalar density
normalization. `OrderMinimal` derives the true size-4
purity and size-5 line from the first two edge fields,
without separately assuming stage purity. `OrderBush`
then proves the usual order-eleven bush defect is a unit
by reading its value \(10\) modulo 29 from the actual
clock and weight data. Its proof needs only the leaf
case of the early field for that clock identification,
not a map to a separate 15-stage coefficient table.

The packet reports 20 standard-axiom kernel results from
canonical standalone 4.36 builds. From the Lean package
root, the canonical build target is:

    lake build RKCert.ReviewedNative.ERK10FixedQ29AdicOrderBush

The unconditional lifted `HasOrder` endpoint and its
all-power corollary remain separate goals.
