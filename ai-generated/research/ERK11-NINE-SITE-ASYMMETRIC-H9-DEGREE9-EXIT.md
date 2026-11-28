# Canonical asymmetric half-at-9: eliminate the bidegree-(9,12) width component

**Scope.** This continues the genuinely distinct nine-site chart with
left extras ({e,t}), right extras ({t,s}), and physical
clocks (c_8=z) dormant, (c_9=h,c_{10}=s). The
[paid marked determinant](ERK11-NINE-SITE-ASYMMETRIC-H9-SMALL3-EXIT.md)
gives three possible irreducible width components. This excludes
the entire bidegree-((9,12)) component and its actual reflection
over any characteristic-zero field once those chart premises hold.
The bidegree-((31,35)) component is outside this proof.

## Actual polynomial conditions

All polynomial definitions and normalizations are reconstructed
exactly, as in the preceding
[finite-width](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H9-FINITE.md),
[pivot exclusion](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H9-PIVOTS.md)
and marked-determinant notes. The unknowns here are the widths (a,b)
and physical dormant (z). The affine slope (E(z)) and shifted
quadrature pivots have already been earned live. Let (C_9(b,a))
be the unique factor of (operatorname{Res}_z(M,G)) of
bidegree ((9,12)) after the stated live factors are removed.
On this chart (C_9=0).

The actual polynomials (F,G,R,L,Q,S,M,K) all vanish. Here (F,G,Q,S)
are the first derivative, dormant, free-quadratic, and dormant-support
conditions from the finite-width proof; (R) is the right direct
repeated port at physical 10, (L) the weighted left half mark at
physical 9, and (M,K) are the two stated marked compatibilities.
The univariate eliminants in (a) are
[
  r_U(a)=operatorname{Res}_b(C_9,W_U),qquad
  Uin{MQ,MF,GQ,GF},
]
where the (W_U) are the earlier true width resultants. We additionally
use (W_{MS}=0) in the (b) fiber. The receipt uses primitive integral
representatives before projecting or reducing. It never reduces an
unknown tableau or assumes a pivot already live merely because an
irrelevant smaller coefficient is live modulo a prime.

## A finite integral residue tower at 103

1. Scaling the (65)-row Sylvester matrix for (r_{MQ}) gives an
   exact degree upper bound 1230. Reverse at infinity with those
   integral row/column scalings. Exact constant pivot eliminations,
   followed by division of the zero-constant rows by the local
   variable, give three successive nullities 9, 6, 3. Thus its
   degree is at most (1230-18=1212). Its residue modulo 103 has
   degree 1212, so its actual leading coefficient is a 103-adic
   unit. The three remaining residue resultant degrees are
   1596, 1536, and 1830. Their exact degrees are not needed.
2. Suppose an actual characteristic-zero tuple exists. Its (a)
   is algebraic by (r_{MQ}). Embed (mathbb Q(a)) in an algebraic
   closure of (mathbb Q_{103}). The integral coefficients and
   leading unit force (a) integral at this place: at negative
   valuation the leading term would have strictly the smallest
   valuation and could not cancel. Consequently its residue is a
   root of the common four residue projections. Over
   (mathbb F_{103}) their gcd has simple irreducible factors of
   degrees (2,3,4,24), covering every residue embedding.
3. In each of those four finite fields (C_9) still has full
   degree nine in (b), so its leading coefficient evaluated at
   the actual (a) is a unit. It follows that (b) is algebraic
   over (mathbb Q(a)); extend the embedding and use the same
   leading-unit argument to force (b) integral. The common
   (b)-gcd of (C_9,W_{MQ},W_{MF},W_{MS},W_{GQ},W_{GF}) is linear
   in each of the four residue fields, so the possible residue
   of (b) is fixed, also over their algebraic closures.
4. At those four possible ((a,b)) residues the actual dormant
   polynomial (G) still has full degree five in (z). Thus
   (z) is algebraic in the next tower step and, after extending
   the embedding again, integral by the same argument. But the
   gcd of the reduced actual dormant equations is the unit at
   each residue width pair. This is a contradiction over the
   algebraic closure, not just a failure to find rational or
   prime-field sample roots.

Only the leading degree of the first projection is used to force
integrality. The other projections hold at every finite
characteristic-zero width, even if their specialized leading
coefficients vanish. Likewise every previous width normalization
removes only a known-live divisor in characteristic zero;
those guards are not presumed live after reduction. In the last
two steps the required leading pivots are separately checked at
every retained residue, including possible collision residues.
Thus no exceptional place, width fiber, or dormant pole is discarded.

Run `python replay_n12_asymmetric_h9_degree9_exit.py` with SymPy,
python-flint, NumPy and SciPy. SciPy proposes integer Sylvester
scalings, and the receipt verifies their inequalities and all
subsequent row operations in exact arithmetic. This receipt is not
a full native Lean proof of the finite-place or tableau arguments.

The [standalone exact source and independent replay log](erk11-nine-site-asymmetric-h9-degree9-exit/) are included.
