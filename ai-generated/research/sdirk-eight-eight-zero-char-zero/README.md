# Exactly eight quadratic-zero rows are impossible over characteristic-zero fields

Let \(A,\mathbf b\) be a strict ten-stage SDIRK tableau of ordinary order at least eight, with common nonzero diagonal \(\gamma\) over a characteristic-zero field. Put \(\mathbf c=A\mathbf1\) and \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). **There cannot be exactly eight physical zero coordinates of \(\mathbf g\).** A clock label groups physical rows; it is not counted as a physical zero. This is a fully scoped branch exclusion, not a change to the general stage interval 10–11.

## 1. Common entrance and genuine rear phases

The [low-label census](../sdirk-eight-eight-zero-low-labels/README.md) gives two **distinct, individually silent** off rows at physical positions 1, 2 and at least seven distinct labels among the other eight rows. It independently handles equal and unequal one-clock off pairs, including active canceling weights. Use the normalized \(D=1/\gamma\) and the literal rear second ratio \(\kappa_R\).

* If \(\kappa_R=0\), there are exactly seven labels with a repeated terminal clock, and the [zero-ratio chart](../sdirk-eight-eight-zero-zero-ratio/README.md) excludes them in all its placements.
* Otherwise the last two rows are live and their labels are different. The literal third-phase gate makes row 8 either silent in the ghost phase, live in arithmetic, or live in star; in every case the three rear labels are distinct and their physical pure coordinates \(z_8,z_9,z_{10}\) are nonzero. The [paid rear nonvanishing](../sdirk-eight-eight-zero-low-labels/README.md#2-a-paid-rear-nonvanishing-and-exact-multiplicities) includes the potentially zero third arithmetic residual, so that missing pure case is not silently dropped.

The remaining count is therefore **seven or eight distinct zero labels**, with nonzero \(\kappa_R\).

## 2. Seven labels: exactly one repeated label

The one repeated label either joins two of physical rows 3–7 or joins one such row to one of rows 8–10; it cannot join two rear rows by their literal distinctness. The grouped pure numerator is a nonzero constant here: its first six moments vanish, and at least one of rows 9, 10 is a singleton with nonzero pure coordinate.

| Placement / phase | Complete exclusion |
|---|---|
| Both copies early, any rear phase | [Early repeat](../sdirk-eight-eight-zero-early-repeat/README.md) |
| Early–rear, ghost or live arithmetic, any rear mate | [Early mate 3–5](../sdirk-eight-eight-zero-early-rear/README.md), [early mate 6–7](../sdirk-eight-eight-zero-late-mate/README.md) |
| Early–rear, live star and terminal mate 10 | The same [early mate 3–5](../sdirk-eight-eight-zero-early-rear/README.md) and [early mate 6–7](../sdirk-eight-eight-zero-late-mate/README.md) proofs, with the gap-free terminal-star masks |
| Early–rear, live star and mate 8 or 9 | Let \(q\) be the doubled label, \(p\) the other rear pair singleton. If the **grouped** ordinary cardinals are equal \(B(q)=B(p)\), use [equal cardinal](../sdirk-eight-eight-zero-star-equal-cardinal/README.md). If unequal, use [early mate 3–5](../sdirk-eight-eight-zero-star-unequal-front/README.md) or [early mate 6–7](../sdirk-eight-eight-zero-star-unequal-late/README.md). |

No literal weight at the early duplicate is presumed nonzero, or identified with its grouped ordinary weight. The two live-star pair orientations are in the same equations. This exhausts seven labels.

## 3. Eight labels: affine numerator, then location of its root

There are eight distinct zero labels. The reverse pure row has first six ordinary moments zero, so on those eight labels its barycentric numerator is affine. It is not the identically zero affine polynomial because of the actual nonzero terminal pure coordinate.

* **Constant nonzero numerator.** All three rear phases are excluded by the [constant-numerator two-mode proof](../sdirk-eight-eight-zero-constant-barycentric/README.md).
* **Nonconstant numerator, root at a zero label.** There is exactly one root in the coefficient field. It cannot be at rows 8, 9, 10 by the literal nonzero pure coordinates already proved. For an actual root at one of rows 3–7, if its ordinary weight is zero, the [silent pure-root exclusion](../sdirk-eight-eight-zero-silent-pure-root/README.md) handles every phase. If its ordinary weight is nonzero, use [early root 3–5, live star](../sdirk-eight-eight-zero-affine-early-star/README.md), [early root 3–5, ghost/arithmetic](../sdirk-eight-eight-zero-affine-early-finite/README.md), [late root 6–7, live star](../sdirk-eight-eight-zero-affine-late-star/README.md), or [late root 6–7, ghost/arithmetic](../sdirk-eight-eight-zero-affine-late-finite/README.md).
* **Nonconstant numerator, root outside the eight zero labels.** The Cauchy-functional description does not require the root distinct from an off clock. The [external live-star proof](../sdirk-eight-eight-zero-external-star/README.md) and [external ghost/arithmetic proof](../sdirk-eight-eight-zero-external-finite/README.md) exclude all three literal rear phases. Neither requires a generic signed mean or ordinary recovery rank; the exact late-label pivot and \(C_3\) leading-drop branches are included.

These cases exhaust eight labels and therefore the exactly-eight physical-zero chart. In particular this argument neither assumes signed weights are absent nor turns a grouped algebraic zero into a physical silent row. It uses no real ordering and makes no assertion in positive characteristic or over arbitrary commutative rings.

## 4. Verification boundary

The exact Python replays and polynomial identities are documented at each arithmetic exit. The latest external-star replay uses exact characteristic-zero gcds; the latest finite external replays use full degree-preserving polynomial coprimality at fixed simple primitive residues, not finite tableau scans. The Lean files linked by the component packets contain **scalar** checks. Some earlier packets record their tested Lean/Mathlib pins; the latest external scalar sources are staged, not freshly compiled in the long arithmetic run. Neither the table above nor any new scalar theorem is a turnkey native `HasOrder` theorem proving the entire classification.

The [independent replay](independent-external-replay.log) repeats all three external-root exclusions.
