# Native ERK order-12 rank-(2,3) exclusion

The cubic packet has reduced a strict reviewed order-12 tableau of width
at most 17 to head length two and dim F4 in {3,4}. In the rank-three case,
F3 has rank two, lies in the rank-three core, and cannot be clock-stable:
the native outgoing two-direction Hermite gain would make F4 too large.
The unit clock step therefore fills that same core at F4. Native
grade-eight payment makes the core closed under coordinatewise products.

The previously checked `no_rank_three_clock_core_at_order_ten` then
applies unchanged. Its live core contributes at most three clock values;
off-core chronology contributes at most two, contradicting separation
at order ten. No new clock counting or scalar certificate was needed.

The independent consumer uses only strictness, native HasOrder 12 and
the original width cap. It forces width 17 and dim F4=4. The final
rank-(2,4) case and the 18-stage endpoint are not asserted here.

Pinned Lean/Mathlib 4.36.0. Exact human snapshot
91f4ab1bac096ddf81781ca1b81ab5afbb3c55a5. Consumed p12 cubic packet
SHA-256 b4ce7a8883a4abfc4286ad613fa03ebdd3fb3488340999a3f6bb96e2d59b6038.
The already checked NativeLiveCore and ERKGradeEightOffCore source
and object hashes were verified against their published receipt.
Their objects and all other prerequisites were reused without replay.
The additive new source and independent consumer compiled warning-free;
the public conclusions depend only on standard Lean axioms.

