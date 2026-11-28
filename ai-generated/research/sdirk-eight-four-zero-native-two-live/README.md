# Native characteristic projection for two active off-zero clocks

This supplement gives Lean proofs of the **complete scalar characteristic projection** in the [two-active-clock exclusion](../sdirk-eight-four-zero-low-support-active-clock/README.md). The actual rooted flag/chronology reduction and the finite-fiber exclusions remain the linked mathematical and exact replay proofs. This is not a native end-to-end `HasOrder` theorem.

Use the two-rank rear coordinates from that proof. Let $v$ be its actual normalized second reverse gap, $y=1-2c_8$, $z=1-2c_7$, and $t=(1-c_7)/\gamma$. Both $y,z$ are distinct roots of the centered Gaussian quartic, $4v^3-12v^2+3v+2=0$, and
$$
(1+z)(1+2v)=t(1+y).
$$
The two genuine supported reverse reads give $\Psi(t)=0$. The Lean theorem uses the integral polynomial $6\Psi(t)$, computed from the two profiles $(X-1)(X-1-v)$ and $1+(2-v)(X-1)$ and their exact primitives. It checks the gate reduction using the cubic, the homogenization, and the distinction between $z=-y$ and $7(z^2+y^2)-6=0$ for the nonmirror case. No inverse of a scalar coordinate or of an output weight is used on the Lean side.

Two exact Bézout identities force these respective integers to vanish:
$$
546756048=2^4\,3^3\,1265639,\qquad
1071212373482742144=2^7\,3^3\,1174307\,263949107.
$$
Their nonpaid prime support is exactly the same as in the (larger) resultant certificates. The identities are valid over arbitrary commutative rings. The typed scalar implication uses an integral domain and $2,5\ne0$ to cancel the displayed factors; the native characteristic-zero corollary needs no ordering or field-specific operation. The excluded finite geometric fibers are exactly the ones in the linked packet.

The source is `RKCert.Research.SDIRKEightFourZeroNativeTwoLive`. The optional `generate_identities.py` uses SymPy 1.14 to invert multiplication by the homogenized gate in a 12- or 24-dimensional quotient of a rational polynomial ring. It clears every coefficient denominator and checks the literal expanded integer identities. Lean independently verifies them by ring normalization using the supplied stock Lean/Mathlib 4.36.0 proof audit. No numerical stage bound changes.
