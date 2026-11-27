# One exceptional clock is also impossible with a constant active cubic mask

> **Proof status (2026-11-27):** This note contains an invalid use of a degree-five donor polynomial. A row satisfying `C(5)` integrates input degrees at most four. The claimed consequences of the degree-five step, including its finite tests as applied to actual tableaux, are suspended. See the [scope correction](dirk-order10-one-clock-grade-erratum.md).

Work with a genuine eleven-stage order-ten DIRK tableau over a characteristic-zero field. Suppose the physical dirty rows (`g_i≠0` for `g=Ac²−c³/3`) all have one clock ξ, every nonzero g equals `γ=ξ³/6`, at least one dirty weight is active, and there is exactly one numerical physical off-Lobatto label q. **This case is impossible.** Combined with the separate nonconstant branch and the earlier all-Lobatto exclusion, an active one-physical-dirty-clock tableau, if one exists, needs at least two off-Lobatto labels. The all-ghost branches and the unrestricted 11–12 interval are not changed.

## 1. The three exterior heads must be q, 1, τ

Call any physical row with g=0 exterior, including a possible clean row at numerical clock ξ. Use the actual one-clock flag and terminal identity

```
h=(A−ξ/2)g,       Ah=(m+nC)h,
F₄=⟨g,h⟩,        F₅=⟨g,h,Ch⟩,
U=F₆∩{v_t=0}=⟨g,h,Ch,C²h⟩,
e_t=H(c)+δg+L(c)h,       H(X)=42XJ₄(X),
b_t=1/30,        deg L≤1.
```

Here `C=diag(c)`, `c=A1`, and `J₄` is the fixed shifted Jacobi quartic. The earlier literal three-debut cut applies to the first three distinct nonzero exterior clocks `a,b,u`. The first two have nonzero h; the physical diagonal at u is zero. Its primitive read for `P=X(X−a)(X−b)` makes `I P/h` constant at the first two and gives `I P(u)=0` if `h_u=0`. The signed paired scalar is

```
u(4ab−a²−b²)−ab(a+b)=0.                              (1)
```

The three labels cannot all be fixed Lobatto by the fixed triple certificate. If q=u, the terminal identity forces `h_u≠0` because `H(q)≠0` at this exterior nonterminal row. Otherwise q is one of a,b; denote the other by v. If `h_u=0`, the primitive test reads `3u²−4(v+q)u+6vq=0`, so

```
q=u(4v−3u)/(6v−4u).
```

The denominator is nonzero at all distinct fixed pairs v,u by exact mod-419 reduction; (1) with this value of q fails at all such pairs. Thus **all three exterior debuts have nonzero h**. At a fixed nonzero exterior label other than 1, `H(c)=0`, so a nonzero h requires `L(c)=0`. At q itself `L(q)≠0`, as follows from its exterior row and `H(q)≠0`. Since L has degree at most one, the three observed labels must be exactly `{q,1,τ}` where τ is a fixed interior root of both H and L. There are no other exterior h-supported labels, not even zero (because `L(0)≠0`).

## 2. Literal block census including the ξ collisions

The actual ordinary output is the fixed Lobatto functional ν: the difference from ν is supported on those six fixed labels and q, and kills ordinary degrees through nine, so it is zero by Vandermonde. In particular all fixed ordinary aggregate masses are nonzero and the total at q is zero. The terminal at 1 has weight exactly ν(1)=1/30.

The actual `E₆` has rank ten; the genuine marked cubic `G` generates its annihilator and is proportional to paid `βg≠0`. Hence ξ cannot be clock 1 (the true latest active nonunit pivot has `G_j=b_j(1−c_j)^3/6≠0`). The entire h vector is supported on `{q,1,τ}`: on a fixed core ξ distinct from τ, its earliest h is zero and the common g-value plus `L(ξ)≠0` makes h=0 on every dirty row; at ξ=q this is also true on the dirty rows by the same argument. If ξ=τ the full h vector on that fiber is allowed. The h column splits into its three fiber projections via a degree-two clock polynomial, and g supplies a fourth independent localized direction because any head sharing ξ has an exterior row with h nonzero. Thus U is clock invariant. The full off-q indicator lies in U: on exterior q rows h has a common nonzero value (by the terminal identity); if ξ=q, add the disjoint dirty indicator `g/γ` to obtain the full indicator. Interpolation on the six fixed labels and subtracting the off-q contribution puts all clock indicators in `E₆`; any such fixed indicator is not in U because its known ordinary ν mass is nonzero whereas `βU=0`. Consequently E₆ is exactly the full clock profile plus U, and in all blocks except ξ its local dimension is exactly its physical row count. At ξ there is one extra, because G is supported there and the global codimension is one.

It follows that clock 0 is the single actual origin, and the clock-one head is a single ghost with h nonzero besides the clean terminal. The other block counts are:

- **ξ distinct from q,τ.** The fixed ξ block has three rows (indicator, g, and the one slack row). The cubic payment `βg=0` makes the dirty aggregate zero. There must be a clean row for the nonzero ν mass, and at least two active dirty rows, so precisely two opposite equal-g dirty weights and one ordinary clean row. The off q head is a singleton ghost. At τ there are two rows. The τ fiber's h and h² weighted sums are zero because its only other head fibers q and 1 are ghosts, and h at ξ is zero. With two rows and nonzero ν mass, at least one h must be zero (test the quadratic vanishing on their two h-values), and then the nonzero h row is a ghost. The remaining τ row is ordinary clean.
- **ξ=q.** The off core/head block has three rows (dirty and exterior indicator directions, then slack). At least two active dirty rows and at least one exterior head row are present, so again exactly the same opposite dirty pair and one exterior ghost (its mass is zero because both total q and dirty q mass are zero). The τ argument from the distinct case is unchanged: h is zero on both dirty rows, and the other heads are ghosts, so exactly one h-ghost and one ordinary clean τ row.
- **ξ=τ.** The block now has four rows (its ordinary indicator and independent g,h, then slack). The other two heads are ghosts. The paid `βgh=0` says the dirty h-weighted sum is zero, because all dirty g equal the same nonzero γ. Hence the clean ξ h mean also vanishes since `βh=0`. There must be two clean rows: at least one clean ξ h value is nonzero by the exterior head, and the clean mass is nonzero by ordinary ν and `βg=0`. There must also be two dirty rows to support a cancelling active pair, so these counts are exact. The two dirty h-values are equal from their cancelling nonzero weights and `βgh=0`, and equal zero from the earliest dirty row. The clean h² weighted sum is therefore also zero. The two clean rows consist of exactly one h-ghost and one ordinary clean fixed-mass row, as in the other cases.

Thus without using positive weights there are exactly two physical dirty rows, both active with opposite weights, one ghost h-head at each of q,1,τ, and every regular nonzero interior clock carries its fixed mass on one clean row. There are no extra zero-clock or unit-clock rows.

## 3. The first regular row has too small an effective donor set

Let x be the first physical nonzero regular row, where g=h=0. There are active regular interior nodes, so x is not the terminal; x is fixed interior and has nonzero weight. There is exactly one physical dirty row before x: the earliest nonzero clock is the first dirty row, and the latest active nonunit row is the other dirty row, because the genuine G is supported on the two active dirties. The latter must follow x. At x, `Ag=0` since both g,h vanish, so the single earlier dirty tap is zero (its g value is nonzero); this remains true if that dirty row shares x or a head's numerical clock. The effective inclusive donor set at x is therefore contained in `{0,1,τ,q,x}`: every earlier nonzero row not removed is one of the three h-ghost heads by the definition of x. If `x=τ`, the anchored quartic and its X multiple impose the two-donor conditions for labels 1 and q, in particular `5(x−1)=x²`, impossible on the fixed pair (1,x) modulo 419.

Thus x is a fixed interior root different from τ. `C(5)` at this regular row forces the anchored nodal quintic to have zero primitive. Exactly as in the nonconstant one-off branch, it gives

```
q=x[2x²−3(τ+1)x+5τ]/[3x²−5(τ+1)x+10τ].
```

For each of the three candidate donor head labels, apply its degree-four nodal cardinal polynomial on the five effective clocks. Its primitive is nonzero by the finite test, so the aggregate tap from that head into x is nonzero. Thus all three ghost head stages precede x. They are exactly the first three distinct nonzero exterior debuts, in some order, since no regular nonzero exterior clock has yet occurred. Their paired cubic (1) must now hold for some ordering of `{q,1,τ}`. For each of the 12 distinct fixed `(τ,x)` pairs, all six orders give nonzero residue modulo 419. This contradicts (1).

## 4. Scope of the exact verification

`DIRKOrderTenConstantOneOffScalar.lean` checks the fixed roots `[67,141,279,353]` modulo 419, the 60 fixed triples, the 20 fixed-pair guards for the zero third head and the smaller donor set, and all 72 candidate ghost-head orders together with the divisor and nonzero-tap guards. The independent Python replay works by expanded primitive coefficients. Modulo 227 alone there happen to be two vanishing residues for the final permutation test, so the proof deliberately uses 419.

Only the splitting field of the fixed quartic is reduced: monic normalization of `42J₄` is integral over `ℤ_(419)`, and its four distinct residues give an injective reduction of the fixed labels including zero and one. Every subsequently evaluated clock or tap value is a guarded rational expression in those roots. No weight, unknown tableau coefficient, or defect amplitude is reduced. The Lean test is Init-only and typed; the actual tableau derivations above are mathematical. They are not claimed as a fully native `HasOrder` theorem or as a positive-characteristic tableau exclusion. The all-ghost one-local branch, and active one-local cases with at least two off-Lobatto labels, remain open.
