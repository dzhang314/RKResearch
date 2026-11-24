# Nonzero first reverse seed at order 19

Over an ordered field there is no strictly explicit tableau of order at least 19 on 29 stages with a nonzero first reverse seed. This is the Lean theorem
`RKResearch.Certified.ERK19.width29_nonzero_first_seed_impossible`, stated using the reviewed order conditions.

After reducing the first seed to one or two reflected clocks, the proof excludes hidden rank four. Rank five forces equality in the support count, so each physical stage lies in one of the specified groups. The count uses the original rows even when a clock is repeated or a weight is zero. The resulting degree-four tests give the contradiction. The support-count lemma uses finite-dimensional linear algebra over a field and does not require an order on the labels.

The complementary [zero-first-seed exclusion](../../../lower-bounds/conditional/erk_order19_zero_first_seed_opposed_windows_20261124.md) is available as a mathematical proof, not as part of this Lean certificate. The unconditional 30-stage bound is not yet a single checked theorem in this packet.

`rebuild-order.txt` lists the checked files in order. Build the [shared paid-window modules](../reviewed-native-er16-strong-weak-20261124/README.md) first. There are 27 individually kernel-replayed modules, two typed consumer checks, and ten standard-axiom audits.
