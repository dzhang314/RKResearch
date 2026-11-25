# The terminal row of a hypothetical 19-stage method of order 13

The Lean certificates here use the reviewed `HasOrder 13 A b` for a strictly lower triangular matrix over a field of characteristic zero.

[The terminal coordinate must occur by degree seven](../../lean/RKCert/ReviewedNative/ERK13NativeLateWidth19.lean). In particular, the late case has no 19-stage solution. The proof derives the possible radii from the original tree spaces and excludes radius two and radius three separately. It does not assume that the marked and unmarked tree spaces agree.

[The last row gives an 18-stage method of order at least six](../../lean/RKCert/ReviewedNative/ERK13NativeWidth19EndpointOrder.lean). Its coefficients are precisely the leading 18-by-18 block and the first 18 entries of the last row. The proof uses a [general row-order criterion](../../lean/RKCert/ReviewedNative/NativeRowOrderDefects.lean): if a row sum is one, the row satisfies the reviewed order conditions through order `q` exactly when every vector of the degree-`q) defect space vanishes at that row. The forward implication does not require the row sum to be one and is valid over commutative rings.

[Order seven forces radius two](../../lean/RKCert/ReviewedNative/ERK13NativeWidth19EndpointRadius.lean). For any other radius the certificate produces an original rooted tree of order seven on which the last row fails the order condition. These results constrain a hypothetical 19-stage method. They are not an unconditional Lean proof of the [20-stage lower bound](order-thirteen-twenty-stages.md).
