# Native retained decoder and first two physical edge adapters

These files work over a commutative coefficient ring with a local residue map to
F_29, a root of the fixed decic reducing to 2, and the two prescribed head
residues 11 and 20. They use the actual four retained rows of the literal
fifteen-stage tableau, not a hypothetical pure opening.

1. ERK10FixedQ29AdicRetainedRows: genuine four-row action on the retained linear
   primitive, quadratic primitive, and dropped axis, plus its actual tree
   recursion.
2. ERK10FixedQ29AdicRetainedLow: genuine projected old stage output for every
   rooted tree of sizes one through four. This includes both successive unary
   attachments, not just the bush and one-quadratic branches.
3. ERK10FixedQ29AdicRetainedDecode: paid q/s host projection and three-read
   uniqueness; exact actual retained quadratic evaluation and primitive.
4. ERK10FixedQ29AdicFirstEdges: actual first-edge formula
   e_t = -gamma J(P)(r) eta when the raw defect is zero and the two host
   laws hold. Its low-size
   zero and size-four host-line corollaries currently assume ForwardHostLaws.
   This predicate states precisely the full raw B E F2 and B E P gaps
   required (zero and the eta line, respectively). The packet does not
   yet discharge these two global forward hosts laws.

After building baseline AllWords and OrderSlots / OrderAnn / OrderAttach,
compile the files above in order with their objects on LEAN_PATH, e.g.
from ai-generated/lean using Lean 4.36.0:
    for m in RetainedRows RetainedLow RetainedDecode FirstEdges; do
      file=RKCert/ReviewedNative/ERK10FixedQ29Adic$m
      lean --threads=1 -o "$file.olean" "$file.lean" || exit
    done

The attached transcript reports only standard Lean axioms. No Hensel root
creation, late edge filtration, or unconditional exact order is asserted here.
