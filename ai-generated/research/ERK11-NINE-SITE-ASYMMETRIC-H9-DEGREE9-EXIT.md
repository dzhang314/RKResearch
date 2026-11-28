# Canonical asymmetric half-at-9: exclude the bidegree-(9,12) width component

**Scope.** This continues the genuinely distinct nine-site chart with
left extras $\{e,t\}$, right extras $\{t,s\}$, and actual physical
clocks $c_8=z$ dormant, $c_9=h,c_{10}=s$. The
[paid marked determinant](ERK11-NINE-SITE-ASYMMETRIC-H9-SMALL3-EXIT.md)
gives three irreducible width components. This excludes the entire
bidegree-$(9,12)$ component and its actual reflection over any
characteristic-zero field once those chart premises hold.
The bidegree-$(31,35)$ component is outside this proof.

## Actual polynomial conditions

The exact definitions and normalizations come from the
[finite-width](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H9-FINITE.md),
[pivot exclusion](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H9-PIVOTS.md)
and marked-determinant notes. The unknowns are the widths $a,b$ and
physical dormant $z$. The affine slope $E(z)$ and shifted pivots
have already been earned live. Let $C_9(b,a)$ be the unique factor
of $\operatorname{Res}_z(M,G)$ of bidegree $(9,12)$ after the
listed live factors are removed. On this component $C_9=0$.

The actual polynomials $F,G,R,L,Q,S,M,K$ all vanish: $F,G,Q,S$
are the first derivative, dormant, free-quadratic, and dormant-support
conditions; $R$ is the direct right repeated port at physical 10,
$L$ the weighted left half mark at physical 9, and $M,K$ the
marked compatibilities. Use the univariate eliminants
$$
 r_U(a)=\operatorname{Res}_b(C_9,W_U),\qquad
 U\in\{MQ,MF,GQ,GF\},
$$
where the $W_U$ are the earlier width resultants. We also use
$W_{MS}=0$ in the $b$ fiber. Use primitive integral representatives
before projecting and reducing.

## An integral residue tower at 103

1. Scaling the $65$-row Sylvester matrix for $r_{MQ}$ gives an
   exact degree upper bound 1230. Reverse at infinity with those
   integral row and column scalings. Exact constant pivot operations
   and divisions of the zero-constant rows give successive nullities
   9, 6, 3. Thus the degree is at most $1230-18=1212$. Its residue
   modulo 103 has degree 1212, so the actual leading coefficient is
   a 103-adic unit. The other residue degrees are 1596, 1536, 1830;
   their exact characteristic-zero degrees are not needed.
2. Suppose an actual characteristic-zero tuple exists. The nonzero
   eliminant proves that $a$ is algebraic. Embed $\mathbb Q(a)$ in
   an algebraic closure of $\mathbb Q_{103}$. The integral coefficients
   and leading unit force $a$ to be integral at this place: at negative
   valuation the leading term would have strictly smallest valuation.
   Its residue lies in a root field of the common four projections.
   Their gcd has simple irreducible factors of degrees $2,3,4,24$,
   accounting for every residue embedding.
3. In each of those fields $C_9$ retains degree nine in $b$. Thus the
   leading coefficient evaluated at the actual $a$ is a unit, so $b$
   is algebraic over $\mathbb Q(a)$. Extend the embedding and apply
   the same leading-term argument to force $b$ integral. The common
   $b$-gcd of $C_9,W_{MQ},W_{MF},W_{MS},W_{GQ},W_{GF}$ is linear in
   each field, fixing the possible residue of $b$ even over their
   algebraic closures.
4. At those width residues the actual $G$ retains degree five in $z$.
   Thus $z$ is algebraic and, after extending the embedding again,
   integral. Yet the gcd of the actual reduced dormant equations is
   the unit at each residue width. This contradicts existence over
   the algebraic closure, not just rational or prime-field existence.

Only the leading degree of the first projection is used to force
integrality. The other projections apply at every finite width even
at specialized degree drops. Exact width normalization removes only
actual live characteristic-zero divisors, not purported residue
guards. The two remaining leading pivots are checked separately at
every retained residue.

Run the standalone Python replay with SymPy, python-flint, NumPy and
SciPy. SciPy proposes integral Sylvester scalings; the receipt
checks the inequalities and subsequent row operations exactly.
This is not a native Lean proof of the full finite-place argument.

The [standalone exact source and independent replay log](erk11-nine-site-asymmetric-h9-degree9-exit/) are included.
