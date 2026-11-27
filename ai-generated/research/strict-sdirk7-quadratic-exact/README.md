# The quadratic nine-stage order-seven tableau no longer needs a norm guard

This strengthens the coefficient-domain scope of the same
[published quadratic tableau](../strict-sdirk7-quadratic/README.md).
It does not produce a rational nine-stage tableau or establish new
lower bounds.

Let $\rho^2=432969$. The two exact factorial-scaled eighth-tree
residuals (payment minus one) are

$$
 \delta_{\rm bush}=\frac{-26022475375+71656598\rho}{13671482834240},\qquad
 \delta_{\rm tall}=\frac{-566828049+156338\rho}{957274560}.
$$

The first was the original check. The second is the literal order-eight
tall tree. Both can be used after reduction in their *cleared* form,
without separately inverting the two displayed residual denominators.
If both trees paid, their integer numerators would vanish after
cancelling only the already available unit total normalization scale
$b_{\rm Den}a_{\rm Den}^7$. The integer norms of the two numerators are
$-1545982860640624199651$ and $310711594906171965$. They obey

$$
 2861460114013366\,(1545982860640624199651)
    -14237538492914339107\,(310711594906171965)=11.
$$

Since 11 divides $a_{\rm Den}$, it is a unit wherever the stage
scale is a unit. Consequently the two tree payments cannot both be
one in any nonzero ring satisfying the root and scale hypotheses.
The tableau has exact order seven there. The new native source
uses the same logic by distinguishing whether the original bush
norm remains nonzero.

Two concrete newly covered coefficient rings are $\mathbb F_{4217}$
and $\mathbb F_{27367649}$. At the simple roots 1262 and 9030753,
respectively, the bush numerator is zero and the tall numerator is
2000 and 15478482. The inverse derivatives $1/(2\rho)$ in the
residue fields are 680 and 7225113; neither prime divides either
published scale. The explicit simple-root induction lifts each to
every positive power of the prime; a unital map from that power ring
then gives the same upper over **every nonzero commutative ring in
which the relevant prime is nilpotent**. In particular these are
upper bounds of nine strict stages, not matching minima at the
new primes. The earlier matching result at the prime 19 stays
separate.

The improvement locus can also be described exactly. The absolute
bushy norm is $11\cdot13^2\cdot29\cdot248477\cdot4217\cdot27367649$;
the product of the first four factors divides the square of the
product of the two scales and hence maps to a unit. Thus the old
norm vanishes on the allowed scale locus exactly when
$m=4217\cdot27367649=115409375833$ vanishes. The CRT seed
$\rho=100201993742$ has derivative inverse $94261408269$ modulo $m$.
The generic digit argument gives the same exact nine-stage upper
in **every nonzero ring where the product $m$ is nilpotent**,
including mixtures of the two primary characteristics.

The native source is
[SDIRKNineStageOrderSevenQuadraticExact.lean](../../lean/RKCert/Research/SDIRKNineStageOrderSevenQuadraticExact.lean).
Its new theorems are exists_exact_of_root, exists_exact_of_4217_nilpotent,
exists_exact_of_27367649_nilpotent, and exists_exact_of_mixed_primary_nilpotent.
The source replayed on stock Lean 4.36.0 with only standard axioms. Run **python3 check-two-defects.py**
from this directory to replay the literal tree residuals, norm Bézout
identity, and every rooted condition through seven for the first
four powers of both primes and of their product. A different location of the published
JSON can be supplied as its first argument. The mathematical
induction, not that finite replay, covers every positive power.
