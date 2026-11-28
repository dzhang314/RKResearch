# Fifteen stages for exact DIRK order twelve over the unramified cubic rings at 17

The [exact real-algebraic midpoint constructor](../dirk12-fifteen-midpoint-real-upper/README.md) also gives a compatible family of exact order-twelve DIRK tableaux over
\[
\mathcal O=\mathbb Z_{17}[z]/(z^3+7z^2+3z+10),\qquad
\mathcal O/17^k\mathcal O\quad(k\ge1)
\]
and over the fraction field of \(\mathcal O\). Fifteen is optimal in all these rings and in every nonzero commutative algebra over any of them: the [paid lower bound](../../lower-bounds/paid-beta/DIRK-PAID-GRADE-SIX.md) applies, and the order-thirteen failure is a unit. This is not a construction over the prime-power rings alone, over \(\mathbb Q_{17}\) alone, or for strict SDIRK.

## Proof

The displayed monic cubic has no root in \(\mathbb F_{17}\) and is therefore irreducible modulo 17. Its quotient over \(\mathbb Z_{17}\) is a free rank-three complete local ring with residue field \(\mathbb F_{17^3}\), uniformizer 17, and is an integral domain. For example, a nonzero element has a smallest finite 17-adic valuation among its three coordinates; dividing by that power of 17 leaves a nonzero residue, hence a unit by completeness.

Start from the [literal selected residue](../dirk12-fifteen-f17-cubic-midpoint-upper/tableau.json). Keep the first ordinary live clock **exactly \(a=1/2\)**, not its integer residue representative 9. First lift \(x\) as a root of the primitive degree-36 polynomial. Recover \(y,t\) by the two rational polynomials in \(x\). Lift the physical \(f\) as a root of its monic cubic with these coefficients, using residue \(a f_{\mathrm{norm}}\). Finally lift the literal orientation \(d\) as a root of the quadratic \(d^2-sd+p\) from the rational support formulas. In the basis \(1,z,z^2\), the three successive derivative residues are
\[
                 (8,14,5),\quad(16,4,10),\quad(12,5,4).
\]
They are all units. Hensel's lemma gives a unique compatible lift of each root. Every other scalar construction denominator and each pivot used by the chosen literal formula is a unit by the prior residue check. Distinct labels, the physical repeated label, and the stage layout are retained. The lower triangular shape has both explicit endpoints as before.

The roots define a characteristic-zero field embedding of the degree-216 coefficient tower into \(\operatorname{Frac}(\mathcal O)\): its irreducible equations and nonzero guards hold successively, and any field homomorphism taking 1 to 1 is injective. Applying this embedding to the characteristic-zero rooted identities proves them in the fraction field. The lifted entries lie in \(\mathcal O\), so the identities hold already there and survive reduction and base change. The scaled thirteenth-bush defect has nonzero residue \((11,7,12)\), hence is a unit in \(\mathcal O\), each quotient, and every nonzero algebra. This proves exactness of the order and the claimed optimality.

## Independent finite replay

Run `python3 -B replay.py` from this directory, or pass the absolute research directory and a comma-separated exponent list, for example `python3 -B replay.py /path/to/ai-generated/research 2,8,20`. The script uses standard-library cubic-ring arithmetic and Newton iteration, compares the residue of every entry to the old literal, and independently verifies all 7,813 rooted order conditions and the unit failure at the stated sample exponents. The proof covers every exponent. This transfer and replay are mathematical, not a full native Lean proof.
