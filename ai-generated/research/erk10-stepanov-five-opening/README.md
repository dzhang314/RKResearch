# A five-opening Stepanov reconstruction, and its exact three-generator order-ten obstruction

The real-algebraic strict ERK order-ten interval remains **14–15**. The authenticated 15-stage witness is Stepanov's published [ETNA §5, Eq. (5.10)](https://etna.ricam.oeaw.ac.at/vol.63.2025/pp609-626.dir/pp609-626.pdf#page=8), with the exact [Zenodo 15429897 coefficient file](https://zenodo.org/records/15429897). The concrete method is independently verified on all 1,205 rooted conditions in the [archived exact replay](../erk-gathered-seed-rank/archive/stepanov15_exact_marked_fixture.md). This new packet finds a real **14-row exact order-nine reconstruction**, not an order-ten upper improvement. It gives an exact obstruction to reaching ten with the same paid high-profile data and five opening rows, even after releasing the canonical final reverse identity.

## Published witness and the saved opening row

The paper's final seven-parameter family uses $c_2,c_4,c_5$ and four splits of the interior Lobatto weights. Its opening comprises the origin, a strong stage-order-one row, a strong stage-order-two row, and three low stage-order-three carriers. All nine remaining rows are strong stage order four. Their clocks are the six-point Lobatto interior nodes with multiplicity two, followed by 1; the origin carries the other endpoint mass. The actual node chronology of the nine high rows is
$$
 \boldsymbol x=(\theta_4,\theta_5,\theta_2,\theta_2,\theta_3,\theta_3,\theta_4,\theta_5,1).
$$
A high stage's primitive is exact on all trees through size four; thus its derivative profile is locally pure through size five. The paper also gives a different parameterization and a predicted larger-dimensional family, which are not identified with this fixed gate.

Let $B$ be the literal nine-by-nine strict high block of the official method; $E f$ is evaluation on $\boldsymbol x$ and $J$ integration from zero. The degree-three gate $(EJ-BE)|_{X\mathcal P_2}$ has exact rank two, not three. Its monic kernel polynomial is
$$
 P(X)=X(X-p)(X-q),
 \qquad P(X)/X\approx X^2-0.7601172752611644X+0.1191647197596218.
$$
The two nonzero roots lie rigorously in $(0.22,0.23)$ and $(0.53,0.54)$. They are different from the original three stage-order-three clocks. This is checked over $\mathbb Q(\sqrt3,\sqrt7,\sqrt{147+42\sqrt7})$, not inferred from small singular values. The file is the author's exact numeric data (MD5 be9e5e3ba1ff8ed21124ad285d7d2fd5), used with attribution; no paper figures or prose are reprinted.

Use only five opening stages with clocks $(0,e,2p/3,p,q)$ for nonzero $e$ (the replay takes $e=2/15$). Stage two uses the origin, stage three is quadratically exact on its two predecessors for inputs $1,X$, stage four uses $0,2p/3$ with interpolation moments through degree two, and stage five uses $0,2p/3,p$ with the same moments. In particular both of the last opening rows have zero tap to stage two and truly reproduce rooted derivatives through size four. Let $\Pi$ interpolate the actual derivatives on $0,p,q$ into $\mathcal P_2$. At each high row apply the literal old-to-high cross feed $(EJ-BE)\Pi$; it uses only the origin and those two opening carriers. There is no missing cubic because the three opening-supported evaluations kill exactly the span of $P$, which is also killed by the actual high operator. This pays every primitive on a tree of size at most four, and so all high derivatives are pure through size five. Keep the actual high weights and put the published endpoint weight on the old origin.

## Exact ordinary order and independent sources of every remaining residual

Write $C=\operatorname{diag}(\boldsymbol x)$, $\mathbf b$ for the high output row in row-coordinate notation, and
$$
 \mathbf d_j=\mathbf b C^j B-\mathbf b(I-C^{j+1})/(j+1).
$$
The exact high identities inherited from the official data are $\mathbf d_0=0$, $\mathbf d_1$ an opposed difference on all four interior pairs, and
$$
 \begin{aligned}
 \mathbf d_2,\ \mathbf d_1B &\in\langle \mathbf d_1,\mathbf d_1C\rangle,\\
 \mathbf d_3,\ (\mathbf d_1 C)B&\in\langle\mathbf d_1,\mathbf d_1C,\mathbf d_1C^2\rangle,\\
 \mathbf d_4&\in \langle\mathbf d_1,\mathbf d_1C,\mathbf d_1C^2,\mathbf d_1C^3\rangle
       +\eta(\mathbf d_1C^2)B.
 \end{aligned}
$$
These are actual row equalities on all nine columns, all independently checked over the exact coefficient field. They are not simplifying assumptions of an unsupported low-stage redesign.

For a high reverse word $W$, let $f_W$ be its exact scalar density, starting at 1 and using multiplication by $X$ and the upper primitive $J^*$. Let its raw error row $\boldsymbol\varepsilon_W$ be $\mathbf b W-(\mathbf b\odot f_W(\boldsymbol x))$. A clock multiplies the error by $C$; a primitive gives
$$
 \boldsymbol\varepsilon_{WB}
   =\boldsymbol\varepsilon_W B+\sum_j [X^j]f_W\,\mathbf d_j .
$$
The displayed identities imply that through length four each such row is a difference supported oppositely on equal-clock pairs. At length five, modulo those paired differences, every error is a scalar multiple of $\boldsymbol\lambda=(\mathbf d_1 C^2)B$. Integration by parts and quadrature are paid from the six Lobatto sites; the origin contributes neither to $H_t$ nor to $JH_t$, since $\Pi$ includes the actual origin. Here $H_t=|t|X^{|t|-1}/t!-\Pi\boldsymbol\Phi_t^{\rm old}$ is the source polynomial. All terms through order ten have at most one imperfect incoming primitive child, since such a child has size at least five and two would cost eleven. Each root error is consequently a sum of these actual inhomogeneous sources along unary and clock contexts. Through order nine every reverse row required for that sum has length at most four; it kills the site polynomials exactly. This is an exact ordinary-order proof for the 14-row control, not the inference that interval residuals contain zero.

At order ten the only possibly unpaid terms have a size-five source and four exterior letters, followed by the last primitive. Their scalar error is a multiple of
$$
 \Lambda(H_t),\qquad \Lambda(f)=\boldsymbol\lambda E f.
$$
The cubic whole-column equality and opposed pair weights imply $\Lambda(P)=0$. The quotient of degree-at-most-four polynomials vanishing at 0 by $P$ has dimension three. Its tests can be taken as $X,X^2,X^4$. They really are independent: the two pure donor defects below furnish the two cardinal directions on $p,q$; the bush of size five supplies the remaining degree-four nominal direction.

At the fixed published high block the exact reverse replay gives a nonzero coefficient for **each of the sixteen** four-letter contexts. All nine actual size-five source values $\Lambda(H_t)$ are nonzero for both donor orientations, by their exact quadratic norms over the coefficient field. There are exactly 35 order-ten trees per size-five source with the required spine, counted by the rooted recursion. These sets are disjoint, since two size-five sources cannot fit disjointly below a common root at order ten. Thus **exactly 315 of the 719 size-ten conditions fail**, 35 per source. This classifies the failures independently of numerical fitting or a tolerance.

## A rigorous one-row obstruction with fairly relaxed high retuning

This obstruction allows arbitrary usable donor clocks $p,q$ in the five-opening chart, not just the two roots of the official kernel. They must be nonzero and distinct for the claimed decoder. It retains the nine literal high clocks, published weight split, and the *actual high restrictions* of $\mathbf d_0,\mathbf d_1,\mathbf d_2,\mathbf d_3,\mathbf d_1B,(\mathbf d_1 C)B$. All high coefficients may otherwise move. In particular the final canonical $\mathbf d_4$ relation is not assumed. The statement is scoped to this high conditional architecture, not the full seven-parameter family or unrestricted ERK.

For necessity, in any order-ten tableau the actual $\mathbf d_1$ annihilates every derivative column through size eight by the two rooted identities for primitive and clock. Hence $\mathbf d_1 C^2 A$ annihilates every derivative through size five. On the clean opening carriers $p,q$, the two genuine pure size-five vectors
$$
 A\mathbf c^3-\mathbf c^4/4,\qquad A^2(A\mathbf c-\mathbf c^2/2)
$$
are independent. Indeed the second is a nonzero multiple of the actual third opening column on these two rows. Its restriction is proportional to $(3p/4,\,3q^2(3p-2q)/(4p^2))$. The determinant with the first pure vector is, up to order and its nonzero common multiple, $-3p q^2(p-q)^2/16$. On the high block both vectors vanish by the actual stage-order-four payment; at the origin they vanish too. The high rows do not tap either rough opening row, so their test forces the two low coefficients of $\mathbf d_1 C^2 A$ at $p,q$ to vanish. The two opening moment columns $X,X^2$, transferred via the literal feed identity, now require $\Lambda(X)=\Lambda(X^2)=0$. Testing the genuine size-five bush then requires $\Lambda(X^4)=0$. These are necessary actual ordinary equations even without assuming the final high relation.

Differences in the six retained high rows are homogeneous constraints, column by column, in the remaining high coefficients. The six row multipliers are $\mathbf b,\mathbf bC,\mathbf bC^2,\mathbf bC^3,\mathbf d_1,\mathbf d_1 C$. Their restriction to the final six physical high stages is invertible (exact residue determinant in the arithmetic replay). By strict triangularity all allowed variations are therefore supported in only the first two **columns**. They can change $\Lambda(f)$ only by a linear combination of $f(\theta_4)$ and $f(\theta_5)$. On $(X,X^2,X^4)$ the three columns consisting of the original moment values and these two evaluations have determinant $178\bmod227$, hence are independent over the actual coefficient field. No such variation can satisfy the three equations.

If the paper's $\mathbf d_4$ identity with its original coefficient $\eta$ is also fixed, the seventh row multiplier is $\mathbf bC^4-\eta\mathbf d_1 C^2$. Its restriction to the final seven high stages has determinant $159\bmod227$. All high columns except the first are then fixed, and the first is uniquely affine in its earliest tap $a_{87}$. Even the two affine tests $\Lambda(X)=\Lambda(X^2)=0$ have an incompatible coefficient determinant $3\bmod227$. The exact replay also verifies this canonical pencil preserves the high gate's rank-at-most-two condition identically: the variation column belongs to the published gate image. Changing $a_{87}$ alone is thus an actual free high-block direction, but cannot make the 14-stage method order ten.

The modular map is the known integral basis reduction $\sqrt3\mapsto177$, $\sqrt7\mapsto190$, $\sqrt{147+42\sqrt7}\mapsto149$ at 227. All coefficient denominators and the normalizing divisor for $\eta$ are units. The official radicals generate the degree-eight field, as established in the archived exact replay. Nonzero reductions certify the indicated characteristic-zero linear determinants; they are not taken as proofs of the entire rooted equality.

The [reordered-pair follow-up](../erk10-stepanov-reordered-coorder/README.md) removes the fixed high-block coefficients assumption while retaining the stated low interface, four interior pairs, and per-site co-order conditions.

## Replay

    sha256sum -c sources.sha256
    python3 exact_local.py stepanov15-source.txt
    python3 defect_gates.py stepanov15-source.txt
    python3 emit_lean.py /tmp/ERK10StepanovFiveOpeningMod227.lean
    lean /tmp/ERK10StepanovFiveOpeningMod227.lean

The exact radical and quadratic norm checks require SymPy. The modular arithmetic witness is independent and uses only the Python standard library. The Lean Core theorem statements verify four full determinants from the exact emitted matrices; the algebraic-source recovery and the mathematical rooted reduction are separate.
