# Invisible nonconstant DIRK10/11: fully distinct fixed-interior slack

For an actual eleven-stage lower triangular rooted-order-ten tableau over a characteristic-zero field, let `g=Ac²−c³/3`. Assume the nonzero physical cubic defects are nonconstant, occur at one clock ξ, and all such physical weights are zero. Use the one-local terminal profile with L nonzero. This note excludes both remaining fully distinct fixed-interior E₆-slack charts:

- a fixed exterior h-head slack with three distinct h values;
- the fixed cubic core ξ as slack, with one clean row and three distinct nonzero g values.

The exact scalar obstructions are the already verified fixed-interior duplicate DA gates. The new step is a **literal marked column** carrying a nonzero ordinary-mass debit. When several earlier slack rows sit late, their contributions to DA fit a single compensated row identity, so none is lost by treating the clock as an aggregate.

## 1. Physical support, genuine G, and nonzero local debits

Keep the established exact one-local band: `h=(A−ξ/2)g`, `γ=ξ³/6≠0`, `F₄=⟨g,h⟩`, `F₅=⟨g,h,Ch⟩`, `dim E₅=9`, `dim E₆=10`, and `g²=γg+Q(C)h` with Q(ξ)≠0. The two exterior head labels are distinct from each other and ξ. This yields clock-invariant E₆ and exact Lobatto ordinary aggregate ν; the proof needs only βU₆=0, not a nonzero βg. The complementary one-dimensional reflected row `G=βY²A−βY³/3`, `Y=1−C`, is supported on the numerical slack label ζ. The actual latest active nonunit row j satisfies `G_j=b_j(1−ζ)³/6≠0` and all G coordinates strictly after j vanish. The true terminal is last, of clock one, with zero A column.

In either chart under consideration, let B be the entire physical block at ζ, put `V=1−ζ≠0`, `κ=V³/6`, and define actual rows by

```
η=G/κ,        D=ηA,
m_s=b_s−η_s for s in B; otherwise set m_s=0.
```

In particular η_j=b_j and m_j=0. The needed **nonzero debit** is `m_s≠0` for every s in B other than j. There are two justifications.

### Distinct exterior h at a fixed slack

The three physical h values in B are distinct, with g=0. At each other fixed exterior head Vandermonde separation of the paid h,h² and Ch,Ch² moments yields a clean ordinary row and a zero-weight h ghost. At ξ all dirty weights vanish and any regular row there has h=0. Therefore the three B weights satisfy `Σb_s=ν(ζ)≠0, Σb_s h_s=Σb_s h_s²=0`. Since E₆ restricts to affine h on B, G spans the annihilator of the two columns 1,h there; all of its three entries are nonzero from the distinct h values.

If one h value is zero, the weight at that row equals ν(ζ) and the other two weights vanish, by the two h moments. That row is j, and for every other s, m_s=−η_s≠0. If no h value is zero, the weights are the Lagrange coefficients for evaluation at zero times ν(ζ): for the other indices r,t,
`b_s=ν(ζ)h_r h_t/[(h_s−h_r)(h_s−h_t)]`.
All three weights are nonzero. The row `b_s h_s` annihilates 1,h, hence is proportional to G on B. The latest true pivot calibrates `η_s=b_s h_s/h_j`, so `m_s=b_s(1−h_s/h_j)≠0` for s≠j. This need not be an opposite-weight pair.

### Distinct nonzero g in the fixed core slack

Here ζ=ξ, the three nonzero g values and the clean value zero are all distinct, and the B profiles restrict to the span of 1,g,g² (use Q(ξ)≠0 to replace h). Thus G is the four-site Vandermonde contrast and all its entries in B are nonzero. The only active row there is the clean j of weight ν(ζ); all other local weights are invisible. Hence m_s=−η_s≠0 for s≠j.

In both cases every row of B precedes or equals j, because all their G coordinates are nonzero. Off B the origin, terminal, and three other fixed interior labels have singleton ordinary g=h=0 representatives, and all remaining physical rows off B are ghosts. In the head slack case they are the two dirty values at ξ (one γ with h=0, one g′ with h′≠0) and the other exterior head. In the core slack case there are the two exterior h ghosts. A ghost and a singleton ordinary row can share a numerical head label, but are distinct physical donors.

## 2. Genuine latest U and live external D

Let U,W,R denote the latest three **singleton ordinary interior** labels, reflected and in reverse physical order. Thus U,W,R,V are the four distinct fixed interior roots. No earlier B row can be strictly after U. If any such s existed, its active nonzero reflected donor labels would be only V. The genuine first and compensated second moments then force `G_s=b_s V³/6`, or m_s=0: the actual total weighted V tap from the first moment is b_s V/2, and its V² moment leaves exactly b_s V³/6 above the cubic target. This contradicts the nonzero debit.

At column U all earlier B rows are therefore out of its suffix, and `D_U=b_j A_(j,U)`. The standard genuine first/second two-node read at U gives

```
d_U=D_U/b_U=−U³/[6V(V−U)]≠0.
```

Thus D is not proportional to G, a fact proved **without** trying to fold fully distinct slack profiles.

Every ghost off B has a nonzero D coordinate. In the head slack case Dg first ties the two external ξ reads. Then Dh and DCh give two Vandermonde moments of the three numbers at distinct labels ξ,ζ,χ: `h′D_(alternate ξ), Σ_(s in B)h_s D_s, h_χ D_χ`. A zero at any external ghost forces these and both core entries to vanish. In the core slack case Dh,DCh use the three labels ζ and the two exterior heads; a zero at an exterior ghost kills all three contributions. In either case, with the exterior ghosts gone, D's polynomial moments through degree five kill its fixed-label aggregates. The remaining D on B would annihilate 1,h in the head chart, or 1,g,h in the core chart (Dg=0 was paid). It would be proportional to G, contradicting D_U≠0. Thus all external ghosts precede j by D support, and j is physical stage 10.

The terminal-out annihilator of E₄ has dimension three. In the head chart, use the five other actual clean, fixed ordinary profiles: a degree≤4 polynomial in a zero combination of polynomials,g,h vanishes on all five, hence is zero, and g,h are independent. For a putative representation of e_t, the polynomial vanishes at the four earlier clean fixed labels. The three distinct h readings on ζ force its h coefficient zero and require the polynomial also vanish at ζ. It is therefore zero, failing the terminal read. In the core chart the six clean fixed labels give this directly. The independent G,D,DY span the terminal-out annihilator: D annihilates E₅, DY annihilates E₄ by clock multiplication, and two distinct external D-live ghost labels where G=0 give independence. Hence the **actual** paid rows have

```
B₄=βY³A−βY⁴/4=θ G+K D,
B₅=βY⁴A−βY⁵/5=θ′G+M(Y)D,
DA=θ″G+F(Y)D,          deg M,deg F≤1.
```

Here DA is paid because A E₄⊂E₅, and the terminal coordinate vanishes because Ae_t=0. From the pure U active support for B₄ and B₅,

```
K=V(V−U)(V−U/2),       M_U=V(U−V)(4U²−5UV−5V²)/5.
```

All fixed denominators below are the already checked ones. At j, the true first reflected moment gives `A_jj=V/2` and `D_j=b_jV/2`.

## 3. A literal marked V receiver

Let k be the last row of B strictly before j. As proved, k precedes U. Define, for any s of B other than j,

```
v_s=e_s−(η_s/b_j)e_j,
β v_s=m_s≠0,    G v_s=0,    Y v_s=V v_s.
```

This is a linear combination of actual tableau columns. In particular its paid reflected moments are the ordinary V moments with nonzero mass m_s, and its B₄,B₅,DA values have no G term. Its derivative D(v_s), when normalized by m_s, will be the same d_V as in the interior-duplicate check. This notation never treats the marked receiver as a new stage.

There are only three cases: one, two, or three singleton interiors follow k.

### Three later singleton interiors

All earlier B rows are before R. Any external ghost after R sees only the active labels U,W,V, with ordinary V donor contribution exactly its D read. The true compensated polynomial `Y(Y−U)(Y−W)` therefore gives the nonzero multiplier `V(V−U)(U/2−W)` times that D read, impossible. Hence the last three singleton ordinary columns are literally 7,8,9, with only their ordinary donors and j. The already paid uniform DA determinant applies unchanged.

### Two later singleton interiors

Here k is after R and before W,U. No external ghost follows k: otherwise its only possible active ordinary donors are U,W and the single late row j, and the same cubic polynomial forces D to vanish. Thus the true suffix reads at W,U give the known d_W, M′, q_W and q_U of the two-later interior-duplicate calculation.

In the marked column v_k only the two B rows k,j can donate (all other B rows precede k). Let `T=Σ_(r in B)b_r(A v_k)_r` be the ordinary V tap before normalization and put `D_v=D(v_k)`. If `ℓ=η_k/b_j`, then

```
T=b_k A_kk+b_j(A_jk−ℓ A_jj),
D_v=η_k A_kk+b_j(A_jk−ℓ A_jj),
T−D_v=m_k A_kk.
```

The two B donors' contributions to the actual DA mark similarly sum to exactly `D_v(A_kk+V/2)`: use `D_j=b_jV/2` and `D_k−ℓ D_j=D_v`. No external ghost is later, and the only ordinary D donors are U,W and terminal D_t=0. Divide the ordinary weighted taps by m_k. The three-node fourth remainder on U,W,V, together with the affine M determined at U,W, then gives precisely the same checked d_V and q_V as the two-later duplicate chart:

```
den=M_U+M′(V−U)−(U+W+V)K,
d_V=D_v/m_k=V³[3V²−5(U+W)V+10UW]/(60 den),
q_V=V/2+(a_V−d_V)+(d_U a_U+d_W a_W)/d_V,
```

where a_U,a_W,a_V are the cardinal taps for moments `V²/2,V³/3,V⁴/4+Kd_V`. Forced DA affinity at U,W,V contradicts the existing two-later finite gate. The nonzero m_k, d_V and fixed guards justify these divisions.

### One later singleton interior: all earlier slack donors accounted for

Here W precedes k and k precedes U. No **external** ghost follows W. At an external ghost there, the actual nonzero active donor labels can be only V,U, possibly with several physical V rows. Its first and second reflected moments are zero because its weight and G entry are zero. These two labels force each total weighted contribution to vanish. Then B₄ would require K D_ghost=0, impossible.

At every s∈B with W<s<j, only U,V are nonzero weighted donor labels for its marked column v_s. There may be more than two physical V donors. Its ordinary weighted U tap divided by m_s is

```
s_U=−V³/[6U(U−V)],
a_V=V/2−U s_U/V.
```

The B₄ and B₅ reads of v_s (G cancels) give, with the same fixed values for **every** such s,

```
d_V=D(v_s)/m_s=V³(V−2U)/(12K),
M_V=V³(4V²−5UV−5U²)/(30d_V).
```

It follows that across ALL physical B rows after W, including j with m_j=0,

```
D_s=d_V m_s+(V/2)η_s.
```

This replaces the incorrect simplification of D to a single weighted pair at that point. The exact summation identity for any suffix column x is
`Σ_(s in B) D_s A_sx=d_V(Σ_(s in B)b_s A_sx−D_x)+(V/2)D_x`,
as long as its B donors are after W. The same holds for the corresponding linear combination v_k. For v_k, its normalized ordinary V tap is a_V, so the DA quotient equals

```
q_V=V/2+(a_V−d_V)+d_U s_U/d_V.
```

For W itself the physical B donors with nonzero tap are strictly after W and obey this identity. There are no external D ghosts after W, and U,W are its other possible nonzero singleton donors. Let d_W be determined by the true B₅ remainder using the affine M at U,V, and let a_U,a_W,t_V be its three-node ordinary normalized taps (t_V is the total weighted V contribution divided by b_W). Then

```
q_W=(DA)_W/D_W
   =a_W+(d_U/d_W)a_U+V/2+d_V(t_V/d_W−1).
```

These are exactly the checked one-later duplicate formulas, even if two or three earlier B rows follow W and some have zero weight. Forced DA affinity at U,V,W contradicts that gate. No assumption of only two physical donors at V was made in this case.

## Verification and resulting scope

`DIRKOrderTenInvisibleDistinctSlackField.lean` verifies the generic h-moment nonvanishing, marked mass, denominator-free one-label and two-label moment identities, two-row marked DA compensation, and arbitrary finite block summation. The two fixed scalar obstructions (including every division guard) are `oneLater` and `twoLater` of `DIRKOrderTenInvisibleInteriorDuplicateScalar.lean`, already checked on all 24 fixed triples by four Lean versions and independently at 419,719,227,587. The physical ranks, reflected transport, and block-to-scalar case split are the mathematical bridge above, not an end-to-end Lean HasOrder theorem.

Together with the earlier off-slack, zero-slack, repeated-head, and clean-interior-duplicate packets, this closes the invisible nonconstant one-physical-dirty-clock chart for L nonzero. If L is zero, nonconstancy forces δ=0 in the terminal identity; all clocks are then fixed, which the earlier all-fixed theorem excluded independently of weights. Thus no nonconstant one-local invisible cubic chart remains. Constant invisible shapes and multiple physical dirty clocks are distinct problems. No unrestricted DIRK10 stage-interval change is claimed.
