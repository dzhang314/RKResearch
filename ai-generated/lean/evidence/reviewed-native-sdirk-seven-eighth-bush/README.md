# Exact order-seven follow-on for the nine-stage strict SDIRK

This additive module uses the same tableau and parameter bracket as the
existing native nine-stage order-seven seal. It checks two cached stage
products for the seventh/eighth bush and one weighted numerator identity.
The order-eight residual, after removing its positive integer factor, is
the exact rational Horner polynomial already proved positive on the
selected bracket. The module proves that this particular tableau fails
the reviewed order-eight condition, over both the reals and their real
algebraic subfield. It says nothing about ruling out an eight-stage method
of order seven.

Import `RKCert.ReviewedNative.SDIRKNineExactSeven` alongside the previous
reviewed-native staged sources. After rebuilding the single module with
Lean/Mathlib 4.36.0, run the consumer/axiom audit. No prior source or
object is modified. The predecessor zip and current proof source
fingerprints are recorded in the result manifest.
