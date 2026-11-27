# The order-independent one-dirty high obstruction

This excludes an exact order-ten, fourteen-stage tableau throughout the **specified** five-opening/one-dirty/four-pair Lobatto architecture, regardless of the placement of the dirty stage or its weighted partner. It does not raise the unrestricted real-algebraic lower bound 14. In particular this proof does not hold fixed the original Stepanov high ordering, any high tap, or any individual real high weight split. It assumes neither $D(1)$ nor high co-order.

The hypotheses are exactly those of the [one-dirty packet](../erk10-one-dirty-high/README.md): strictly explicit canonical five-opening block with two nonzero distinct clean donor clocks $p,q$; four interior Lobatto pairs in the nine high rows and their unique final endpoint 1; exactly one genuinely dirty zero-weight high row (pure derivative through size four, not through five) at a clock $a\ne p,q$; other high rows pure through size five; all weights supported on the origin and high rows. In particular the pair at $a$ has a nonzero weighted clean partner. The formula that controls one genuinely dirty row uses only its possible rough stage-three feed and cubic primitive error as explained there.

## True rooted consequences and exact scalar sieves

The earlier proof derives, using only actual marked order tests, that $d_{j,d}=0$ for $j=0,1,2,3$ at the dirty coordinate $d$, and that each $\mathbf d_j$ has aggregate zero at every high site, including $a$. Thus the weighted partner at $a$ individually pays the four upper moments through degree three. The new exact scalar check covers every support containing 1 and at most two other distinct Lobatto interiors: if $S$ is any such support, then
$$
              \int_a^1 \prod_{u\in S}(X-u)\,dX\ne0 .
$$
All 28 values have nonzero reduction mod 227. Hence the weighted partner at $a$ must have a weighted occurrence of **each other interior** after it, as well as the terminal 1.

Let $H$ vary over the actual early-null model space $X\mathcal P_3$. Its physical high value is the tilted response
$$
 \widetilde E H=E H+\mathbf e_d\psi(H).
$$
Write $\varphi$ for the one resulting nonnodal coordinate at $d$. It is not assumed to be an evaluation at any clock. The true length-$j+1$ context with $j$ marks and one unary attachment, $j=0,\ldots,4$, now gives the actual weighted group mean of $B\widetilde E H$ **exactly $JH$ at each high site**. Indeed all these contexts fit order ten, and their nominal clock moments equal those of $JH$ by exact quadrature through degree nine; invert the five distinct-site Vandermonde. This is a statement on the *tilted* physical input. In particular the weighted partner at $a$, its group's only contributor, has actual read $J_a$ on this input space.

If the dirty row came after its weighted partner, the latter's earlier high inputs would be at most the three other interior evaluations (the endpoint is last). The [sixty support hull tests](../erk10-stepanov-reordered-coorder/README.md) show that $J_a$ cannot act from such a support on $X\mathcal P_3$. Therefore the dirty row precedes the weighted partner. Before the partner there is at most one occurrence of each other site, since every other site must have a contributing occurrence **later** than it.

For distinct interior $x,y,z$ the following 24 ordered determinants are nonzero:
$$
 \det(J_x,E_x,E_y,J_z)|_{X\mathcal P_3}\ne0 .
$$
Here $J_xf=(Jf)(x)$ and $E_xf=f(x)$. It follows also that $J_z$ cannot lie in $\langle J_x,E_x\rangle$, or that two distinct $J$ rows cannot be proportional. The modular fixture checks all 24. These finite determinants and the 28 upper support values are calculated with the authentic coefficient field and unit denominators; all four Lean Core versions verify the emitted scalar tests.

## At most one of the other first occurrences can match its mean

Call a normal paired site's first occurrence *exact* in this paragraph if its high row acts as $J$ on the whole tilted input $X\mathcal P_3$. Let $m\in\{0,1,2,3\}$ be the number of the other distinct interiors seen before the weighted partner at $a$. At the partner its earlier inputs can use just $\varphi$ plus those $m$ ordinary evaluations; at every normal first occurrence we may overallow $\varphi$ even if the actual dirty stage is not yet present.

- **$m=0$.** Necessarily $\varphi$ is proportional to $J_a$. The first other site $y$ sees at most $J_a,E_a$, so is not exact. The next distinct site $z$ sees at most $J_a,E_a,E_y$, so is not exact by the determinant. Only the last other pair can be exact.
- **$m=1$.** If $y$ occurs before the partner, then $J_a\in\langle\varphi,E_y\rangle$ and $J_a$ is not a multiple of $E_y$. Thus $\varphi\in\langle J_a,E_y\rangle$. At $y$ the actual earlier functional set is contained in $\langle\varphi\rangle$; $J_y$ is not in $\langle J_a,E_y\rangle$. The next new $z$ after the partner has earlier space contained in $\langle J_a,E_y,E_a\rangle$, also insufficient. Again only the final other site can be exact.
- **$m=2$.** If $y,z$ occur before the partner, its $J_a$ condition forces $\varphi\in\langle J_a,E_y,E_z\rangle$ (the $J_a$ row is not in the two evaluation span). Neither $J_y$ nor $J_z$ is in this larger space by the determinants, so only the final site can be exact.
- **$m=3$.** Let the first occurrences in order be $y,z,t$. Their earlier spaces are contained in $\langle\varphi\rangle$, $\langle\varphi,E_y\rangle$, $\langle\varphi,E_y,E_z\rangle$. If $y$ is exact, $\varphi$ is proportional to $J_y$ and the determinants rule out exactness of both $z,t$. If $z$ is exact, $\varphi\in\langle J_z,E_y\rangle$ (since $J_z$ is not a multiple of $E_y$); then $J_t$ is not in $\langle J_z,E_y,E_z\rangle$. Thus at most one is exact also in this case.

Intermediate repeats never enlarge these predecessor spaces; they have the same ordinary evaluation at a clean site. The case analysis does not permute the actual first five rows or invoke reflection of their rooted profiles.

## True dual differences require two exact groups

For $j=0,\ldots,3$ the full $\mathbf d_j$ has no opening support. The two original rough pure columns force their two coefficients zero, the pointwise donor argument forces zero on $p,q$, and the true constant moment with high aggregate zero kills the origin coefficient. Their remaining high rows are opposed on at most the three **non-dirty** pairs. At those pairs write $\Delta_y$ for the difference of the two actual high rows acting on $\widetilde E(X\mathcal P_3)$; thus $\Delta_y=0$ means each equals its known exact group mean, including the first occurrence.

For $j=0,1$, the true annihilators $\mathbf d_j C^kA$ for $k=0,1,2$ kill every actual size-five early-null source, by attaching a unary parent and $k$ marks. The low physical source is zero. On the remaining high pair coordinates the three distinct-clock Vandermonde rows therefore force $\Delta_y=0$ at each active $\mathbf d_0$ or $\mathbf d_1$ pair. At most one pair can be active by the earlier case analysis. At least one must be active: at the last nonzero interior output there is only a later weighted endpoint 1, and at that coordinate
$$
                         d_1-d_0=b_i(1-c_i)^2/2\ne0 .
$$
The dirty partner cannot be that last weighted interior by its upper support requirement. Let $t$ denote the uniquely possible active group, with $\Delta_t=0$.

Consider the last contributing occurrence at a normal group different from $t$. Such an occurrence exists after the dirty partner since all three other sites have later weighted occurrences. After it the only distinct weighted sites are $t,1$. Its $\mathbf d_0,\mathbf d_1$ vanish as it is outside $t$. Its $\mathbf d_2$ cannot vanish: degree-two upper quadrature on that two-point support would integrate the hull $(X-t)(X-1)$, one of the nonzero exact upper tests. Thus $\mathbf d_2$ is active at a second group. Its two true marks $\mathbf d_2A$ and $\mathbf d_2CA$ annihilate every size-five early-null source. If it is active on at most two groups, these two equations isolate both differences by the distinct clocks and require a second exact first occurrence, already impossible. It must therefore be active on **all three**. But $\Delta_t=0$ from the lower defects; the two equations now isolate the other two differences and again require them to vanish. This is the contradiction.

Hence merely reordering the dirty row and its weighted partner cannot give a fourteen-stage order-ten method within the one-dirty chart. The exact rational low port in the earlier six-opening packet really does give a valid adjacent dirty/weighted-partner prefix at a scaled clock; the obstruction is in completing the other three physical pairs, not in that local construction. Multiple dirty rows, changed scalar support, a different early donor geometry, or another high shape are not covered.

## Replay and scope

    sha256sum -c sources.sha256
    python3 checks.py
    python3 prepartner_support.py
    lean ../../lean/RKCert/Research/ERK10OneDirtyReorderedMod227.lean

The additional 60 earlier-support values are independently replayed here from the neighboring public coefficient fixture and already have their own [Lean receipt](../erk10-stepanov-reordered-coorder/README.md). The new Core arithmetic proves the 24 predecessor and 28 successor tests; the rooted-to-site reduction and characteristic-zero transfer above are mathematical, not asserted as native all-tableau theorems.
