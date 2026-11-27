# Invisible one-local DIRK10/11: a fixed interior clean duplicate

Assume the actual invisible nonconstant one-physical-dirty-clock band as in the off-slack note, with L nonzero. Suppose the E₆ slack is a fixed interior clock ζ and is spent on **two identical clean physical profiles**, g=h=0. This includes an ordinary interior duplicate, a repeated-zero class at a fixed exterior h-head, and two clean rows at the fixed cubic core. This chart is impossible over characteristic zero. Fully distinct h-head and fully distinct dirty-core profiles are not claimed here.

## 1. Actual D and the ghost census

Let i<j denote the duplicate physical indices. Their weights sum to ν(ζ)≠0, denoted m, and are not assumed opposite or individually nonzero. The G contrast is supported on i,j; j is the genuine latest active nonunit pivot, so its weight is nonzero. Put `Y=1−C`, `V=1−ζ`, and

```
G_j=b_jV³/6,     G_i=−G_j,
D=GA/(V³/6)=b_j(A_(j,*)−A_(i,*)).
```

There are one regular row each at the other five fixed labels and exactly four ghosts: physically distinct dirty values γ,g′ at ξ (both invisible, with h=0 and h′≠0), and a nonzero h ghost at each of the two exterior heads. A ghost can share ζ, but is not an i,j duplicate. The exact block census away from ζ and the separately paid h,h² means at the fixed heads justify these counts. If a head has two different h values and nonzero fixed mass with both means zero, one value is zero and carries all that mass. The same holds at a repeated-zero head with three rows, where the nonzero class has weight zero.

D annihilates E₅. Dg ties the two ξ entries, and Dh,DCh kill the first two moments of three reads on the distinct labels ξ and the two heads (the ξ read uses h′ times its alternate entry). Hence a zero at any ghost kills all four. The polynomial degree-five D moments would then kill their distinct fixed ordinary aggregates, leaving only the i,j contrast, hence folding and a shorter method. Thus every ghost D entry is nonzero. D has triangular support at or before j, all other active nonunit rows precede j, the terminal is last, and therefore j is stage 10.

Use one clean representative at ζ and all the other ordinary rows to get rank E₄=7 and e_t∉E₄. Two distinct D-live ghost clock labels give independence of G,D,DY, which span the terminal-out annihilator of E₄. Thus the true reverse rows satisfy

```
B₄=βY³A−βY⁴/4=θG+K D,
B₅=βY⁴A−βY⁵/5=θ′G+M(Y)D,
DA=ηG+F(Y)D,                deg M,deg F≤1.
```

The upper analysis never substitutes βg for G. The last three singleton ordinary interior labels other than ζ in reverse physical order are U,W,R in reflected coordinates. Then U,W,R,V are the four distinct fixed interior roots. A row “after” means in forward physical order.

## 2. Two immediate end positions

If i follows all three singleton interiors, its nonzero weighted reflected donor labels are just V. The first moment at column i gives total V tap b_i V/2. Thus its genuine cubic defect there is G_i=b_iV³/6. But G_i=−b_jV³/6, impossible since b_i+b_j=m≠0. This exclusion is valid also if b_i=0.

If all three singleton interiors follow i, then for columns after i the actual weighted V tap is just D_s=b_j A_(j,s). Any ghost after R is excluded by the genuine first/second/compensated third moments and the annihilator polynomial `Y(Y−U)(Y−W)`, since its D entry is live. This is the original uniform paid DA situation, with R,W,U physically the last three ordinary columns and no ghost or earlier duplicate in their inclusive suffix. Its fixed determinant contradiction applies.

For either of the middle positions below, i precedes U. At U the original two-donor calculation is valid regardless of any earlier row. It supplies the fixed quantities

```
K = V(V−U)(V−U/2),         d_U=D_U/b_U=−U³/[6V(V−U)],
M_U = V(U−V)(4U²−5UV−5V²)/5,
q_U=(DA)_U/D_U=V/2+(U²/2−V d_U)/U,     when no ghost follows U.
```

The ordinary K and M_U reads only use active weights; the q_U formula also needs the indicated physical D suffix. It will follow in each case. At j, `D_j=b_j V/2` always.

## 3. Aggregate the two ordinary columns at V

Use `D_V=D_i+D_j` for the **aggregate D** on ζ, and let d_V=D_V/m. Because G_i+G_j=0, both the aggregate B₅ value and the aggregate DA value are their affine functions at V times D_V. This aggregate is not an artificial combined stage.

In the sum of the two literal columns, write a_V for the total ordinary weighted V contribution divided by m, and a_s=b_s A_(s,i)/m for each singleton ordinary s after i. No singleton contributes to column j. The true first and second moments of the sum are V²/2 and V³/3, since the mass is m and G cancels. Its compensated third and fourth targets are V⁴/4+K d_V and V⁵/5+M(V)d_V.

If there is no ghost after i, the corresponding genuine DA aggregate read is

```
A_ii = a_V−d_V,
q_V=(DA)_V/D_V = V/2+A_ii+Σ_(s after i) d_s a_s/d_V,
d_s=D_s/b_s.
```

Indeed `b_i A_ii+b_j(A_ji+A_jj)=D_V+m A_ii`, and the duplicate pair's contributions to the literal DA sum are `D_V(A_ii+V/2)`, since `D_j/b_j=V/2`. Any ordinary terminal donor has reflected clock zero and D_t=0. The denominator d_V will be a checked nonzero fixed quantity in the actual charts below.

## 4. Exactly one singleton U after i

Here i is after W and before U. There are no ghosts after W: at any such ghost the only nonzero active donor labels can be V,U, even if both physical V rows contribute. Its first and second reflected moment targets are zero, because its weight and G coordinate vanish. The two distinct nonzero labels force each active weighted contribution to be zero. Then B₄ gives K D_ghost=0, contrary to the live read. This also justifies both the aggregate DA formula and the exact later W-column DA read.

At the aggregate V receiver there are just V,U donors. The first two moments give

```
s_U=a_U=−V³/[6U(U−V)],       a_V=V/2−U s_U/V.
```

Its third and fourth defects now give

```
d_V=V³(V−2U)/(12K),
M_V=V³(4V²−5UV−5U²)/(30d_V),
q_V=V/2+(a_V−d_V)+d_U s_U/d_V.
```

Thus the affine functions M,F are pinned at V,U. At W let d_W=D_W/b_W. The literal ordinary donor labels are U,W,V. Replacing the fourth power on these three donor labels by its cubic remainder gives

```
den = M_U+(M_V−M_U)(W−U)/(V−U) − (U+W+V)K,
d_W = W³[3W²−5(U+V)W+10UV]/(60 den).
```

Let `a_U,a_W,t_V` be the ordinary weighted taps in the W column normalized by b_W. They are the three-node solutions at U,W,V to

```
m₁=W²/2,        m₂=W³/3,         m₃=W⁴/4+K d_W.
```

For a donor y and the other two donor labels p,q, its tap is
`[m₃−(p+q)m₂+p q m₁]/[y(y−p)(y−q)]`. This is a literal weighted sum across the two physical V rows for t_V, not an individual A entry. Since `b_i A_iW+b_j A_jW=D_W+m A_iW`, dividing by b_W gives `A_iW/b_W=(t_V−d_W)/m`. With `D_i−V b_i/2=D_V−Vm/2`, the exact compensated DA ratio is

```
q_W=a_W+(d_U/d_W)a_U+V/2+d_V(t_V/d_W−1).
```

There is no ghost correction to this formula because no ghost follows W. Affinity forces
`(V−U)(q_W−q_U)−(W−U)(q_V−q_U)=0`. The finite check excludes this on all fixed orders; the computed scalar equals the negative of the ordinary DA signed square in the order (U,V,W).

## 5. Exactly two singletons W,U after i

Here i is after R, before W. No ghost is after i: for such a column the ordinary weighted V tap is D_s (the earlier duplicate no longer contributes), and only U,W can be the other nonzero reflected donors. Apply the true compensated cubic polynomial `Y(Y−U)(Y−W)` as before. The nonzero fixed coefficient `V(V−U)(U/2−W)` contradicts D live.

Now the pure suffix U,W formulas both apply and their DA quotients use no ghost donors:

```
d_W=W³(2U−W)/[6(U−2W)V(V−U)],
M′=3V(U−V)(U−W)²/[5(2U−W)],
q_W=V/2+(d_U/d_W)a_WU+a_WW.
```

Here a_WU,a_WW are the two-node true taps at U,W for moments `W²/2−V d_W, W³/3−V² d_W` respectively in degrees 1,2. The fixed two-node formula is `(m₂−p m₁)/[y(y−p)]` for the tap at y, with the other donor p.

At aggregate V, U,W,V are the three donor labels, and the actual B₅ fourth remainder gives

```
den=M_U+M′(V−U)−(U+W+V)K,
d_V=V³[3V²−5(U+W)V+10UW]/(60 den).
```

Use the genuine aggregate first three targets `V²/2, V³/3, V⁴/4+K d_V` to determine a_U,a_W,a_V by the three-node cardinal formula from §4. This yields

```
q_V=V/2+a_V−d_V+(d_U a_U+d_W a_W)/d_V.
```

Affinity requires `(W−U)(q_V−q_U)−(V−U)(q_W−q_U)=0`. The finite check again excludes all fixed orders, and this is the negative of the same DA signed square in the order (U,W,V).

## Verification boundary

`DIRKOrderTenInvisibleInteriorDuplicateScalar.lean` computes all fixed divisions and the two nonzero affine differences at the splitting residue 419 and compares them with the previous signed square. The independent exact script repeats the calculations at 419 and 719 (also 227 and 587 on request). Every divided variable d_U,d_W,d_V and each interpolation denominator in the actual chart is guarded. Characteristic-zero transport uses only the fixed quartic splitting field at a prime above 419. Neither the individual signed weight b_i nor any unknown ghost clock is reduced or divided by. These are native finite scalar certificates with a mathematical actual tableau/rank bridge. Together with the fixed-origin and off-slack notes, every clean duplicate is excluded, but fully distinct fixed slack profiles and the unrestricted 11–12 interval are not decided here.
