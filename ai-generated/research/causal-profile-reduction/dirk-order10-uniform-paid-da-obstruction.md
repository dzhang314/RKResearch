# Uniform DIRK10/11 obstruction from the paid row DA

The exact signed ghost skeleton for an actual eleven-stage, rooted-order-ten lower triangular tableau is impossible over characteristic zero. This statement applies **whenever the paid signed skeleton below has been obtained**, independently of the number of off-Lobatto labels. In particular it replaces all off-count cases of the active one-local nonconstant branch with nonzero terminal affine coefficient L. It also applies to the constant-defect branch when the same signed skeleton is established (e.g. the Lobatto aggregate and nonzero (L(ξ)) assumptions of the repaired suffix note). It does not apply to invisible one-local defects in general, to arbitrary active multiclock defects, or to the full 11–12 interval.

## 1. Actual prerequisites and the new paid row

Use the actual one-local rank setup and the repaired reflected suffix of `dirk-order10-paid-one-off-repair.md`. There are six ordinary active Lobatto rows with nonzero fixed weights (each has ordinary defect values g=h=0), a cancelling pair of equal-signature active dirty rows at ξ, and three actual zero-weight ghosts. On the ghost positions G is zero; at least two of the ghosts have distinct clock labels and nonzero D entries. Here

```
Y=1−diag(c),       V=1−ξ,
G=βY² A−βY³/3,   D=G A/(V³/6)=∑_(i in dirty active pair) b_i A_(i,*).
```

The actual terminal index t is last, has numerical clock one, and satisfies Ae_t=0. The usual true grading gives (G∈E_6^\perp, D∈E_5^\perp); the compensated quartic reverse read is (B_4=βY³A−βY⁴/4=θG+K D) with (K=V(V−U)(V−U/2)). These are the literal tableau rows, not a weighted-transpose tableau; negative and zero individual weights are allowed.

**New paid row.** Since (A E_4⊂E_5) by the unary root extension, DA annihilates E₄. Its actual terminal coordinate is zero because Ae_t=0. The three rows G,D,DY lie in the same terminal-out annihilator: for DY this is (YE_4⊂E_5), the true leaf extension and identity. They are independent: on two distinct D-live ghost clock labels G is zero, so a relation forces both coefficients of the affine multiplier of D to vanish, and then the G coefficient vanishes. No ordinary-column entry is divided by in this independence argument.

The terminal-out annihilator has dimension exactly three. In this skeleton E₄ is the five clock polynomials through degree four plus the independent defect vectors g,h. Independence from those polynomials follows by their vanishing on the six fixed ordinary rows. Thus E₄ has dimension seven. And (e_t\notin E_4): its representing degree≤4 polynomial would vanish at the five earlier ordinary labels (clock zero and the four interiors) and hence also at the actual terminal. Therefore the added terminal-out linear constraint is genuine. We conclude

```
D A = a G + (b + cY) D                       (1)
```

where the coordinate multiplier is on the right: equivalently (DA=aG+bD+c(DY)). This is the same exact three-dimensional rank used to place B₅, but DA supplies an additional test.

## 2. The last three ordinary columns

From the already paid suffix, the ordinary interior columns U,W,R in reverse physical order are stages 9,8,7, and the later active dirty row j is stage 10. The earlier active dirty and all ghosts occur before stage 7. If some ordinary clock also appears at an earlier ghost or dirty row, that earlier row is not an inclusive suffix donor. At an ordinary suffix column s, (G_s=0), so (1) forces ((DA)_s/D_s) to be affine in s whenever the three (D_s) are nonzero. We establish that nonvanishing before taking ratios.

The paid first reflected moment, `βYA=βY²/2`, at the later active dirty column j gives `A_{jj}=V/2`: j is the sole contributor with nonzero reflected clock, its weight is nonzero, and V≠0 by the latest active nonunit pivot. In particular (D_j/b_j=V/2). At U the paid first and second moments also give V≠U, as a single repeated nonzero label cannot have the required first and second target moments. The repaired read gives

```
d_s = D_s/b_s = k_s/[V(V−U)],

k_U = −U³/6,
k_W = W³(2U−W)/[6(U−2W)],
k_R = R³(2U−W)(3R²−5R(U+W)+10UW)
       /[6(4RU²−13RUW+4RW²+U²W+UW²)].
```

All fixed differences and each k numerator and denominator are nonzero by the exact fixed-clock test. Thus each (D_s) used as a comparator is indeed nonzero. No assumption about (V-W) or (V-R), and no actual ghost tap denominator other than the live-clock independence above, is required.

For each regular suffix column s let (a_{ell,s}=b_ell A_{ell,s}/b_s) for its actual inclusive regular suffix donors. Their clock set is ({U},{U,W},{U,W,R}) respectively. Because the earlier active dirty row is before all these columns, the only dirty term into s is from row j and its normalized weight is (d_s). Although the actual terminal can contribute ordinary A entries to s, its reflected clock is zero and its D entry is zero. It contributes to neither of the forthcoming calculations.

At ordinary s the genuine first, second, and compensated third moments of the weighted transpose read give, for the moments needed by its number of regular donors,

```
Σ_l a_(l,s)·l    = s²/2 − V d_s,
Σ_l a_(l,s)·l²   = s³/3 − V² d_s,
Σ_l a_(l,s)·l³   = s⁴/4 − V³ d_s + K d_s.
```

The second uses (G_s=0) and the third uses (B_{4,s}=K D_s). Equation (1), triangularity, and the live dirty diagonal give

```
(DA)_s/D_s = V/2 + [Σ_l k_l a_(l,s)]/k_s.        (2)
```

In (2) no earlier repeated-clock row has been aggregated with an ordinary donor; only the actual physical suffix participates.

## 3. Remove the dirty clock exactly

Every donor set contains U. Add exactly (k_s/[U(V−U)]) to its U-weighted tap to obtain `bar a`, leaving all other taps unchanged. This is a change of variables for the read, not an operation on the tableau. The three now fixed targets become

```
m₁(s)      = s²/2,
m₂(s,k_s)  = s³/3 − k_s,
m₃(U,s,k_s)= s⁴/4 − (U+U/2) k_s.
```

For the last, ((V²−U²)/(V−U)=V+U), while (K d_s=k_s(V−U/2)). The singular term cancels identically. This compensating shift changes the ratio (2) by the same constant across all three columns:

```
F_s := [Σ_l k_l bar a_(l,s)]/k_s
     = (DA)_s/D_s − V/2 + k_U/[U(V−U)].
```

So (F_s) has to be affine in s, with no auxiliary condition on the unknown V.

The U donor gives (F_U=U/2). For W with two distinct regular donors (ell,j), the compensated tap at (ell) is

```
(m₂−j m₁)/[l(l−j)].
```

For R with three distinct regular donors (ell,j,h), its tap at (ell) is

```
(m₃−(j+h)m₂+jh m₁)/[l(l−j)(l−h)].
```

These are polynomial Lagrange reads after factoring out the zero clock: take the appropriate linear combination of moments 1–2 or 1–3, then divide by the nonzero fixed factor shown. The corresponding (F_W,F_R) are the k-weighted sums of these taps divided by (k_W,k_R). Thus the necessary affine determinant is a single expression in the **fixed clocks only**:

```
Δ=(W−R)F_U+(R−U)F_W+(U−W)F_R=0.
```

The exact ordered fixed-root test gives Δ≠0 in all 24 cases. An independent simplification of this same determinant, also checked against the direct tap replay, is

```
Δ= −3 (R−U)(R−W)(U−W) J² / [(U−2W)(2U−W) L_R M_R],

J   = R U²−4 R U W+R W²+U²W+UW²,
L_R = 3R²−5R(U+W)+10UW,
M_R = 4 R U²−13 R U W+4 R W²+U²W+UW².
```

The determinant computed directly from the fixed compensated taps is already sufficient; no appeal is made to a sign of Δ, the ordering of the field, or a characteristic-zero square-root choice.

## 4. Verification and scope

`DIRKOrderTenPaidDAObstructionScalar.lean` computes the shifted fixed moment systems, every fixed nonvanishing guard, and the determinant directly modulo 419. `DIRKOrderTenPaidDAField.lean` checks the compensating identities, the two- and three-tap Cramer reads, and the affine determinant identities over a generic field. `check-dirk10-uniform-paid-da.py` independently replays the direct and signed-square evaluations at 419 and 719.

The characteristic-zero step uses only the splitting field of (42 X^4−84X^3+56X^2−14X+1). At a prime above 419 the four fixed roots remain distinct; their possible ordered images are exactly the tested list. Every fixed denominator is a residue unit, so the nonzero residue of Δ proves nonvanishing in the fixed-clock field. No tableau coefficient or dirty clock is reduced. The grade, physical rank, and order-to-suffix bridges above remain mathematical, not a complete native HasOrder proof. Without a derivation of this signed skeleton there is no general field proof from this packet alone, and no change to the unrestricted DIRK10 stage interval.
