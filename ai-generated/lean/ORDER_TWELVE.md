# Explicit Runge–Kutta order twelve needs eighteen stages

This source delta is based on published source snapshot `182d77cc` and is pinned to Lean 4.36.0 and Mathlib v4.36.0 (Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). The source theorem is in `RKCert/ExplicitOrderTwelve.lean`:

```lean
theorem RKCert.explicit_order12_ge18_field
    {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Fin s → Fin s → K} {b : Fin s → K}
    (ha : RKCert.StrictLower A)
    (ho : RKCert.HasTreeOrderAtLeast A b 12) : 18 ≤ s
theorem RKCert.explicit_order12_ge18_charZero
    {R : Type*} [CommRing R] [CharZero R] {s : ℕ}
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : RKCert.StrictLower A)
    (ho : RKCert.HasTreeOrderAtLeast A b 12) : 18 ≤ s
```

These are lower bounds, not existence assertions. Repeated nodes and zero or signed output weights are allowed. The field need not be ordered or algebraically closed. The ring theorem allows zero divisors. The proof is separate from the positive-characteristic uniform ERK floor and from the strict SDIRK and nonsingular DIRK bounds.

## Proof outline

Write `E_j` for the span of stage-tree columns of grade at most j and `F_j` for the span of differences of normalized stage-tree columns of equal grade at most j. The columns `P_j(c)` evaluate clock polynomials through degree j. The clocks are actual row sums c. The ordinary explicit stage zero and the rational Cauchy moment decoder separate `P_6(c)` from `F_6` in the p=12 order conditions.

### 1. Saturation and the terminal mesh

If there are at most 17 stages, the grade-five surplus and elementary strict growth force `dim F_5≥5`, `dim F_6≥6` and `dim E_6≥13`. The reverse growth cost is four additional dimensions. Equality therefore fixes 17 stages, ranks 5, 6 and 13, zero initial reverse residual, and exact reverse ranks 0 through 4 (the Lean index is one less than the conventional backward grade). No terminal-live assumption is added: if the last physical weight is zero, strict causality trims it without affecting any tree order condition, and the same 17-stage floor on the trimmed tableau contradicts equality.

The last active clock is one. Its coordinate column lies in `E_6` by the exact reverse annihilator, and products with this column show all `F_5` values at that row are zero. The one-clock escape forces `F_6=F_5 + C F_5`, so `F_6` vanishes there too. A fixed seven-row rational moment packet solves the polynomial part of the last coordinate: it is
`f(x)=x (132 x⁵−330 x⁴+300 x³−120 x²+20 x−1)`,
normalized by `f(1)=1`. It follows that `(x−1) f(c)` is paid in the first grade-seven escape.

The last-zero part of `F_7` meets `P_6(c)` trivially: use zero at 0 and 1 and all five mixed moments, never a squared-polynomial positivity argument. Consequently it has dimension at most seven. Strong Hermite gain excludes C-invariance of `F_6`, making that last-zero space precisely `F_6+C F_6` of rank seven. The resulting `E_7` rank is fourteen.

### 2. One-head chart and reverse obstruction

The equality `dim F_6=dim F_5+1` and the genuine C-escape give a largest C-invariant core U and a single head w with r consecutive powers in `F_5`. The grade-five equality gives `dim U+r=5`, and Hermite gain from U gives r≥2. Coordinate-block subtraction normalizes the chosen head: a nonzero head block at any numerical site is genuinely outside U. No Euclidean projection is used.

Reverse Hermite gain excludes C-invariance at `E_7` and `E_8`; the rank caps make their successors rank 15 and 16. The separate proof in `REVERSE_OBSTRUCTION.md` excludes C-invariance at `E_9` by a single two-node induction in a corrected reflected column; in particular there is no unverified chronology split. Therefore `E_10` is the full 17-dimensional space. Each escape extends the same head by one power. Through `E_7,E_8,E_9,E_10` these are `P_6(c)` plus U and respectively r+2, r+3, r+4 and r+5 head powers. The last genuine power implies at least r+5 distinct effective head sites, by polynomial interpolation.

### 3. Exact leakage and chronological multiplier tests

A degree-six polynomial part in `F_7` is on the line spanned by the specified `H_7` (constant coefficient zero and five mixed moments). In the end-zero grade-eight band the corresponding leakage is only `H_8=5x−75x²+350x³−700x⁴+630x⁵−210x⁶`. If two consecutive clock shifts both lie in that last-zero band, both leakage coefficients vanish. Indeed subtract the two polynomial components after multiplication by x, cancel the degree-seven coefficient using `(x−1)f`, and then use the zero intersection of the degree-six polynomial band with the rank-nine head band. The two remaining fixed coefficient equations force both scalar coefficients to zero. The terminal derivative factor of f and `H_8` have an explicit rational Bézout identity; their roots cannot cancel each other, even over an unordered field.

For a defect multiplier v preserving U and whose action on the head powers fits in a short enlarged chain, comparison of the quotient polynomials gives a low-degree P with `v*w−P(c)w∈U`. Its degree is at most the number of levels added to the band. If v is outside U then P is nonzero: otherwise `v*w∈U`, and the chart gives `v²∈U); interpolate the reciprocal of the finitely many nonzero v values to recover v in U. This avoids invoking an orthogonal complement or requiring the field to be infinite at that step.

For the chronological test, use simultaneous blocks of c and v. The first prefix at which `Q(c)(P(c)−v)` cannot be matched by U defines a numerical knot u. At a mismatch block the head's restriction belongs to U, because the multiplier difference is nonzero on the block and `v*w−P(c)w∈U`. Thus a vector in the head band gives a legitimate U correction there. Strict causality lets one use the earlier matching U vector within A, and the corrected primitive is constant on this prefix block. If this constant were not its permitted leakage, scaling its U component would contradict the first unmatched block. The mesh relation gives `u=1` or `f(u)=0`; the mask Q forces a nonzero eligible endpoint and, on the second test, a distinct one.

For degree-two multipliers the three primitive tests at one nonzero knot give a Cauchy matrix. For the cubic profile the cheap tests have zero leakage and the degree-three test coefficient can have a single common scalar multiple of `H_7`. Apply the two masks x and `x(x−u)`. The five exact scalar equations are checked against the fixed rational Appendix B gate at two distinct roots of `(x−1)f/x`. This implication uses verified rational identities, not inference from a modular sample.

### 4. Exhaust the chart

For any v in `F_2`, its products with `F_5` are last-zero grade seven. Localize the products with U by numerical site; a one-site vector in a chain with more remaining sites than degrees must be in U. The multiplier and the degree-two Cauchy test force `F_2⊆U`. Thus r≤4. For v in `F_3`, products with consecutive head powers are in the last-zero grade-eight band, and the paired leakage result pays both shifts in the pure band. The same localization preserves U. The cubic primitive test forces `F_3⊆U` in the r≥3 branch. Since `dim F_3≥2`, r=4 is impossible. At r=3 equality gives `F_3=U` and Hermite gain gives `dim F_4=4`. In that case `F_4=U+span(w,Cw)`. Site-local multiplication and the no-leak result make U an actual coordinatewise algebra. Its support indicator removes the overlap from w without altering the head chart. The square of this disjoint head and both clock shifts are in grade eight, so w equals a polynomial of degree at most three on its support. Because both w and Cw are in `F_4`, the cubic tests are affordable and exclude r=3.

At r=2, the dimension of `F_4` is either three or four. In the first case `F_4=U` and `dim F_3=2`; the primitive restrictions of every off-mask row to the three-dimensional mask algebra annihilate `F_3`, and hence lie on one common line. The first off-mask nonzero clock h fixes the ratios by the first three monomial primitives. The first different nonzero off-mask clock y would then satisfy `y²(y−h)²=0`. Thus there are at most two off-mask nodes, and at most three mask nodes, contradicting the seven necessary head sites.

In the rank-four r=2 case, clean w by the mask-algebra indicator. Its square has a representation `w²=αH_8(c)+u+w R(c)` with `deg R≤4`; the terminal relation supplies on the head `f(c)=w Q(c)` with `deg Q≤2`. If α is nonzero, the head feature pairs (c,w) are counted by roots of the nonzero degree-at-most-twelve eliminant `f²−fQR−αH_8 Q²`. Where Q is nonzero there is at most one head value; at a shared zero there are at most two values and at least two root multiplicities. Zero always costs an extra unused multiplicity, including when it is itself a head feature. Hence there are at most eleven head features. The mask algebra has at most three classes and the remaining off-mask, off-head part has only the numerical features 0 and 1. The 17 physical coordinates are distinguished by the full chart `E_10` but at most 16 features exist, a contradiction.

If α is zero, the head on its support is a polynomial P of degree at most four. Seven distinct head sites imply the polynomial identity `f=P Q`, so P has degree four and is a divisor of the fixed f. The first off-mask contrast gives the formal primitive of xP, or of P when x already divides P, as zero at a qualifying nonzero mesh knot. The literal-polynomial divisor gate rules this out using the nonzero cubic/quartic factor certificate over arbitrary characteristic-zero fields, including when a complementary quadratic does not split in the field. This finishes the field theorem. The ring theorem uses the existing characteristic-zero prime quotient and fraction-field specialization and ordinary base change of the actual tree identities.

## Proof replay and reuse

Apply all new `RKCert/*.lean` sources from this archive to `182d77cc`, and append the single public import in the supplied umbrella file. No published proof leaf is changed. Run `lake build` and `lake env lean OrderTwelveAudit.lean`. The evidence lists source hashes, exact local dependency closure, kernel replay status and axiom output. No new trust assumption, sorry, native decision, or runtime CAS is required.

The implementation reuses Mathlib's polynomial degree/evaluation, root multiplicities and finite-set root bounds, Lagrange interpolation, finrank/sup/inf/rank-nullity, dual annihilator codimension, rank-one spans, linear combinations, finite-class injections, polynomial extensionality, and ring normalization. It reuses the published row/dual implementation unchanged (including the Mathlib dot-product equivalence), the native RK order equations, grade-five surplus, OneEscape, physical chronological matching, weighted Hermite gain, and exact Appendix B gates. New arithmetic is limited to the displayed small rational row packets and the p12-specific mesh and profile coefficients.

