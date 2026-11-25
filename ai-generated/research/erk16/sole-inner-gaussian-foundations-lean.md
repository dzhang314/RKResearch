# Checked Gaussian corner witnesses for the order-16 SoleInner branch

Lean verifies the 30 original sextic corner witnesses with
denominator-cleared orthogonality and opposite signs at each of the six
rational cage endpoint pairs.
The source uses the actual normalized density and proves Gram uniqueness
over the supplied ordered field. It also proves monotonicity of the six
ordered nodes as the two density parameters increase, without a
continuity or real-closure assumption.

Three modules compiled and independently kernel-replayed on Lean 4.36.0.
The typed audit reports only standard axioms. These are foundations for
the SoleInner exclusion, not a proof of that exclusion: the transport
from the actual packet, the cap inequalities and the final phase
contradiction must still be checked in Lean.
