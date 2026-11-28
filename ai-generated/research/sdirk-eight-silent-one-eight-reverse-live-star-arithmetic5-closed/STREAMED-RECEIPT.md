# Separate exact streamed coefficient check

The [streamed replay receipt](streamed-product-receipt.log) checks the
complete outer resultant against the covered factor product on 616
whole prime images. The product modulus has 36,961 bits, above the
proved 36,942-bit coefficient difference bound, so this is a full
integer coefficient identity, not sampling. The published checker
in the main note independently reconstructs the outer polynomial
from scratch; this receipt checks the same identity without forming
the high-power product over the integers at once. The [small
guards](independent-guarded-replay.log) and [generic quotient
fibres](independent-generic-replay.log) were replayed independently
against the exact coefficient archive.
