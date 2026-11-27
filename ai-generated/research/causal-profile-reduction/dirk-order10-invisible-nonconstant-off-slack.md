# Invisible nonconstant DIRK10/11 with an off-Lobatto slack clock

Consider an actual eleven-stage lower triangular tableau of rooted order ten over characteristic zero. Write `c=A1`, `C=diag(c)`, `β=bᵀ` and `g=Ac²−c³/3`. Assume all physically nonzero g values occur at one numerical clock ξ, they are not constant, and all their physical weights are zero, so the actual row βg is zero. In the established terminal profile `e_t=H(c)+δg+L(c)h`, assume `L≠0`. Let ζ be the numerical clock of the one extra physical dimension beyond E₆ (the **slack** clock). **If ζ is off the six fixed Lobatto labels, there is no such tableau.** No conclusion about a fixed slack clock or the unrestricted numerical 11–12 interval is made here.

## 1. Weighted and physical blocks without βg

Use the exact nonconstant one-clock band, with `γ=ξ³/6≠0`, `h=(A−ξ/2)g`, `H(X)=42XJ₄(X)` and `g²=γg+Q(C)h`, where `Q(ξ)≠0`. The two exterior h-head labels a,b are distinct from each other and ξ. At ξ the relation reads pointwise `h_i=g_i(g_i−γ)/Q(ξ)`, so every g=0 row at ξ is also h=0. The first nonzero clock is ξ and its g value is γ with h=0. The true terminal t is last, has clock one and weight `1/30`, and `Ae_t=0`.

The paid E₆ clock-block decomposition in the one-physical-dirty-clock note uses `βU₆=0`, not the nonzero row βg: off-label indicators belong to U₆, μ is exactly the fixed Lobatto ordinary aggregate, and E₆ is the span of actual clock indicators and the four defect dimensions. The ξ block has dimension two off-Lobatto or three when ξ is fixed; each head has dimension one off-Lobatto or two when fixed; every other fixed label has dimension one. Exactly one block has one extra physical row, at ζ. The genuine nonzero row `G=βY²A−βY³/3`, `Y=1−C`, spans E₆'s annihilator, is supported at ζ, and at the actual latest active nonunit row j equals `G_j=b_j(1−c_j)^3/6≠0`. These facts follow from the E₆ decomposition and the actual latest pivot, not from βg (which is zero here).

Since ζ is off-Lobatto it must be ξ or one of the two heads. Off ξ cannot be the latest active label: on that block the terminal profile precludes any g=0 row, and all g≠0 rows have zero weights. Thus ζ is one of the exterior heads; let χ be the other. At an off exterior head, the terminal profile fixes the nonzero h value on every physical row at that clock. The ζ block consists of **two identical E₆ profiles**, both with `g=0` and the same nonzero `h_ζ`. One is the actual pivot j with nonzero weight; zero ordinary aggregate at ζ makes the other i active with opposite weight. As their E₆ profiles are identical, G is their contrast. With `V=1−ζ≠0` the pivot now yields

```
G_i=b_i V³/6,  G_j=b_j V³/6,
D=GA/(V³/6)=b_i A_(i,*)+b_j A_(j,*),    b_i+b_j=0.
```

This is an actual active pair, not an assignment of weights to the invisible dirty core.

Because ξ is not the slack block, it has exactly two distinct nonzero g values (one is γ), with two zero-weight ghost rows there; if ξ is fixed there is also just one clean regular active row there. Indeed nonconstancy needs two physical dirty rows, and in the fixed case the nonzero ordinary mass needs a clean row, exhausting the block. The alternate dirty value g′ has `h′=g′(g′−γ)/Q(ξ)≠0`. The χ head has just one physical row if off, and it is a zero-weight h ghost. If χ is fixed, it has two physical rows and nonzero ordinary mass. The paid weighted h and h² moments on that block are zero: both ξ defect weights vanish, and the two opposite weights at ζ share h. Therefore one of the χ rows has h=0 and carries the mass, and the other is a nonzero h ghost with zero weight. The two h values are distinct by the exact block rank. This argument also covers χ at clock 0 or 1; the actual origin/terminal is the corresponding ordinary row. Altogether there are six ordinary active fixed rows with g=h=0, one opposite active off-head pair, and three ghosts (two share ξ).

## 2. The three distinct D readings, not three distinct physical ghost clocks

The grade E₅ is annihilated by D, hence `Dg=Dh=DCh=0`, and D has zero true terminal coordinate. Write `d_γ,d′,d_χ` for its entries at the two ξ ghosts and the χ ghost, and write `d_ζ=D_i+D_j` for the pair's aggregate. The two ξ entries are tied by

```
γ d_γ+g′ d′=0.
```

In particular one vanishes if and only if the other does. Now Dh and DCh kill degrees zero and one of the three **clock contributions**

```
r_ξ=h′ d′,     r_ζ=h_ζ d_ζ,     r_χ=h_χ d_χ.
```

All three clock labels are distinct. If any one contribution vanishes, the remaining two vanish by the two-site Vandermonde; the g relation then also kills the remaining ξ entry. With both ζ weights' D aggregate zero and all ghosts dead, the six true regular D entries vanish by the polynomial degree-five moment test on their six distinct fixed labels. The only remaining D can be the ζ contrast, hence is proportional to G. This would give an A-invariant equality subspace for i,j, also preserved by pointwise products. Starting at the all-ones vector, every tree column would agree at i,j. Folding j into i by merging its column and weight into the earlier stage preserves all trees and lower triangularity, contradicting the eleven-stage minimum.

Thus **each ghost entry is nonzero and the ζ pair aggregate is nonzero**. No claim is needed that the two individual pair entries have the same sign, nor that the two ξ ghosts have different clocks. Two distinct live ghost labels ξ,χ suffice for the independence of `G,D,DY`.

## 3. The repaired reflected suffix transfers

All ghosts precede j by triangular support of D, all ordinary nonunit fixed rows precede j by the genuine latest active pivot, and t is last. Hence j is physical stage 10. Let U,W,R be the reflected numerical clocks of the last three ordinary interiors, in reverse physical order. The first two genuine reflected moments at U force `V≠U`. Since D is independent of G, the ordinary compensated quartic row satisfies

```
B₄=βY³A−βY⁴/4=θG+K D,    K=V(V−U)(V−U/2).
```

The formula for K is the ordinary U read: the only nonzero active labels available there are U and V, the latter's contributions aggregate to D. For a ghost column geometrically after R, the ordinary nonzero donors are a subset of U,W. The actual regular pieces of the first three moments are the negatives of `V D_s, V² D_s, (V³−K)D_s`; the polynomial `Y(Y−U)(Y−W)` would force `V(V−U)(U/2−W)D_s=0`. The fixed guard excludes `U=2W`, contradicting the live ghost entry.

For the earlier pair column i, set `s_i=b_iV/2−D_i`. The regular pieces of the same three genuine moments are `V s_i,V²s_i,(V³−K)s_i`. This follows from `G_i=b_iV³/6` and the B₄ coefficient read at j with `D_j=b_jV/2`. If i were after R, the same vanishing polynomial would give `s_i=0`, hence `D_i+D_j=0`, contrary to the nonzero ζ aggregate. Thus all ghosts and the earlier pair precede R; actual columns 7,8,9 are the regular R,W,U.

Now the full uniform DA calculation applies with ζ instead of ξ in the **reflected** pair parameter V. Its hypotheses are exactly satisfied:

1. The six ordinary fixed profiles show rank E₄=7 and exclude the terminal indicator from E₄ by a degree-four polynomial with five fixed roots.
2. `G,D,DY` lie in and span the three-dimensional terminal-out E₄ annihilator. Independence uses the actual ξ and χ ghost reads, where G is zero; no βg coefficient is used. Both DA and the true B₅ reflected defect are in this span by grade transport.
3. At each of the latest three ordinary columns the weighted contribution at V is now from the single later pair row j, and is exactly that column's D entry. The ordinary first/second/compensated third/fourth reads deriving the fixed `k_U,k_W,k_R` in the repaired suffix therefore give the same formulas. Their nonvanishing and all fixed differences are already certified. No donor involving the earlier pair or ghosts survives in the physical DA inclusive suffix.
4. The common U-column shift gives the same fixed affine determinant among three ordinary columns. Its forced zero contradicts the existing four-version exact scalar check on all ordered fixed triples.

Thus the off-slack invisible chart is impossible independently of the number of non-Lobatto clocks. The condition that L is nonzero is kept in the stated chart; no inference is made for a fixed ζ.

## Verification boundary

`DIRKOrderTenInvisibleOffSlackField.lean` gives generic field lemmas for the three tied D reads, the normalized active-pair column, and the two-regular-column scalar elimination. The fixed DA determinant and generic compensated-tap calculations are the already audited modules in the uniform DA packet. The actual tableau census, rank, folding, and reflected transfer above remain a mathematical bridge, not a complete native HasOrder theorem. No positivity, missed ghost comparison, or reduction of tableau coefficients is assumed.
