# DIRK10/11: corrected one-off exclusions and exact reflected suffix

> **Follow-up:** The [all-fixed degree-four prefix proof](dirk-order10-all-fixed-prefix-exclusion.md) subsequently closes the all-fixed nonconstant exception left open in this note.

**Erratum.** A row with `g=h=0` has exact `C(5)`, which integrates inputs of degrees **0 through 4**. The old anchored quintic and the `X` multiple of an anchored quartic have degree 5. Those tests in the prior first-clean cut, including the resulting `q` formula, must not be used. The old Lean scalar computations are arithmetic under their displayed premises, not proofs that `C(5)` supplies those premises. This note replaces the one-off bridges. It does not modify the frozen packets in place.

Throughout, the tableau is lower triangular, has eleven physical stages and actual rooted order ten over a characteristic-zero field. Assume `g=Ac²−c³/3` is physically nonzero at only one numerical clock `ξ`, with at least one nonzero `b_i g_i`. We use the valid one-clock rank band of the original note, with `h=(A−ξ/2)g`, `c=A1`, `C=diag(c)`, `β=bᵀ`,

```
F₄=⟨g,h⟩,     F₅=⟨g,h,Ch⟩,      Ah=(m+nC)h,
U₆:=F₆∩{v_t=0}=⟨g,h,Ch,C²h⟩,     E₆^⊥=K G,
e_t=H(c)+δg+L(c)h,                 H(X)=42XJ₄(X),     b_t=1/30,
G=β(1−C)²A−β(1−C)³/3,            G∥βg≠0.
```

The six fixed Lobatto labels are `ℒ={0,1,J₄ roots}`. Work in a splitting extension as needed; no ordering or weight signs are assumed. The terminal column is zero and the terminal clock is one. The genuine latest active nonunit pivot is a nonzero entry of G, so this pivot has clock ξ and `ξ≠1`. The first nonzero numerical stage has nonzero g, with `γ=ξ³/6` and h=0.

**Correct conclusions.** Exactly one numerical off-Lobatto label is impossible, for both constant and nonconstant nonzero g values. Zero off-Lobatto labels are impossible if g is constant, or in the nonconstant case with `L≠0`. In particular the active branch ordinarily needs at least two off-Lobatto labels, with the all-fixed nonconstant `L=δ=0` still open. If `L=0,δ≠0`, the terminal identity forces constant nonzero g and all exterior clocks fixed, which the valid old paired cut already excludes. No conclusion is made about all-ghost one-local, a full `HasOrder` impossibility, or increasing the unrestricted DIRK10 stage interval beyond 11–12.

## 1. Corrected constant one-off bridge

Call a row exterior if g=0 (it can share the dirty numerical clock). The first three distinct nonzero exterior clocks `a,b,u` satisfy the **valid** native low-grade cut: `h_a,h_b≠0`, `d_u=0`, and, with `P=X(X−a)(X−b)`, the primitive values at a,b,u equal `k·h` for a common nonzero scalar k. The paired equation is

```
C(a,b,u)=u(4ab−a²−b²)−ab(a+b)=0.                    (1)
```

These arguments only use primitive inputs of degrees at most four; they are the first-three exterior cut, not the first *regular* quintic. In particular all three cannot be distinct fixed nonzero clocks. Under the one-off premise, let q be the sole off-Lobatto clock. If q=u, then `h_u≠0` from the actual terminal identity. If q is one of a,b, let v be the other, fixed. If `h_u=0`, the degree-three primitive at u yields

```
q=u(4v−3u)/(6v−4u).
```

The denominator is a unit mod 419 on distinct fixed pairs, and substituting in (1) fails on all such pairs. Thus the three head clocks are exactly `{q,1,τ}`, where τ is a common interior root of H,L: only a shared fixed root or nonterminal clock one can carry exterior h away from q. This also rules out `L=0` in this branch.

The signed block census in §2 of the older constant note is valid, and can be summarized independently. The measure is Lobatto because its at-most-seven labels and the degree-nine ordinary payments determine it by Vandermonde. The four defect directions are the three clock projections of h plus g, independent even if ξ shares one head (an exterior h is live there). The off q indicator is carried by a single h projection, plus the dirty indicator g/γ if ξ=q. Fixed clock indicators then give the full E₆, and only the ξ block has a one-row excess since `G∥βg`. The six fixed masses each have one regular active row. The only extra rows are three single ghosts with `h≠0` at q,1,τ, and the opposite-weight dirty pair. If ξ=τ, the four rows in that block include two clean and two dirty: `βgh=0` makes the clean h mean zero while its mass is nonzero, and the dirty pair has h=0 from its common weighted h and first-row value. In all placements the τ h² payment then forces exactly one clean regular row and the other a h-ghost. The other two head ghosts follow from zero off-Lobatto mass and from the matched physical terminal weight at one.

Let x be the first nonzero regular clock. It is an active fixed interior; before x there is only the first dirty row, since the late dirty follows all active ordinary nonunit rows. Its tap into x is zero by `Ag(x)=0`. If not all three head ghosts precede x, there are at most two nonzero earlier head labels. If the effective donor labels are contained in `{0,a,x}` (including when a ghost shares x), the anchored cubic `X(X−a)(X−x)` and its degree-four X multiple cannot both have zero primitive at x: they give `2a=x` and `5a=3x`; pad any missing a without affecting the test. Otherwise x is the third distinct exterior clock after exactly two heads a,b, so the paired cut has `d_x=0`. With the dirty tap and the diagonal both removed, the two degree-three/four inputs `X(X−a)(X−b)` and its X multiple give

```
a+b=6x/5,       ab=3x²/10.
```

Among a,b at least one is fixed because only q is off-Lobatto. Eliminating the other gives `10a²−12ax+3x²=0`, excluded for fixed nonzero a and fixed interior x. Thus all three ghosts precede x.

If x=τ, the actual degree-four nodal polynomial `S=X(X−a)(X−b)(X−u)` vanishes on every effective donor, so `I S(x)=0`. If x≠τ, x is a fresh numerical donor (and not 0,1,q). Applying the same degree-four polynomial gives `d_x S(x)=I S(x)`. On the other hand the honest degree-four input `I P` has values proportional to h on the three ghosts and is zero at the origin; the sole earlier dirty tap has already been removed. Since `Ah(x)=0`, integrating `I P` at x gives `I²P(x)=d_x I P(x)`. Thus the necessary scalar is

```
I²P(x) S(x) − I P(x) I S(x) = 0.                    (2)
```

After clearing 60 and 3600 as appropriate, (1) and either `I S(τ)=0` or (2) are polynomials of degree at most two in q. The three orders modulo interchange of a,b make (1) respectively linear, quadratic, quadratic. Its leading coefficient is a unit modulo 419 in each case, so any algebraic root is integral over the localized fixed-clock field. The checked common-root separation holds over the **algebraic closure** of the residue field: if the first polynomial is quadratic, cancel quadratic terms from the second to get a nonzero constant or a linear polynomial and test its root after clearing the denominator. No assertion that q already reduces into the prime field is needed. This supplies the corrected constant exclusion.

## 2. An exact reflected suffix on the signed ghost skeleton

The following math works beyond the one-off case whenever the stated skeleton is available. It applies to constant g with `μ=ν` and `L(ξ)≠0`, and to active nonconstant g with `L≠0` (in particular the one-off census described below). The actual physical rows consist of six regular fixed active rows (`g=h=0`, one at each Lobatto clock and weights ν), a dirty active opposite-weight pair with equal g,h and clock ξ, and three ghosts. In the constant case these have three distinct h-head clocks. In the nonconstant case there is one alternate-g ξ ghost plus two exterior h-head ghosts. At the active pair, `G` is their contrast multiplied by a nonzero scalar. Let `Y=1−C`, `V=1−ξ`, and set

```
D = GA/(V³/6) = ∑_{i in the dirty active pair} b_i A_{i,*}.
```

The equality follows from the true latest active nonunit `G_j=b_j V³/6` and the proportionality of G to βg (g is the same nonzero value at both active positions). We have `D∈E₅^⊥`. In either skeleton D is nonzero at each ghost. In the constant case this follows from the two vanishing moments on `(D_i h_i)` at the three distinct ghost clocks, since D annihilates `h,Ch` and h is zero elsewhere. In the nonconstant case the D aggregate of the active pair is `−g_d D_d/g_*` by Dg=0, where d is the core ghost and `g_*` the constant value at the active pair. Its resulting h reading is `D_d g_d(g_d−g_*)/Q(ξ)`, using `h=g(g−γ)/Q(ξ)` on the core. This coefficient is nonzero, so the same two-moment test acts on three scaled ghost entries at distinct clocks. In both cases a zero entry would force all three to vanish; then the remaining pair has aggregate zero, and the six D entries on regular fixed sites are zero by degree-five Vandermonde. That would give `GA∥G`, so the pair equality subspace is A-invariant and closed under coordinate products. Folding those two stages would preserve all tree values and order, contradicting the 11-stage minimum. This proves the ghost assertion without individual positive weights. For the constant skeleton beyond one-off: identical dirty signatures spend the codimension-one contrast, so any other fixed block has at most one ordinary occurrence, except a possible 1-head or shared H/L root τ. A τ block has at most two clean rows (profiles only 1,h), and `βh=βh²=0` makes any second a ghost as above. Every off label can have at most one exterior row, h constant nonzero there, so it is a ghost if μ is Lobatto. This yields exactly three ghost heads by counting. For nonconstant g with nonzero L, the same census holds even with two or three off-Lobatto labels. An off ξ block has exactly two nonzero g classes by the terminal profile, so they cancel separately and contribute nothing to the h² weight. All off head blocks are singleton ghosts; a fixed 1-head is a ghost by terminal mass, and there is at most one fixed nonunit head (it requires the root of L). The separate h and h² payments make that head, if present, a ghost alongside its one ordinary fixed row. A fixed ξ instead forces L(ξ)=0, so its exterior heads are either off or at 1 and again ghosts. The h² read then adds the fourth signed g moment on the core, giving a cancelling equal-g active pair and one different-g ghost plus the necessary regular fixed core row.

Triangularity forces the late dirty stage after all ghosts with nonzero D, as well as all active ordinary nonunit rows by the latest genuine pivot. Thus it is physical stage 10. The true reflected rows

```
B₄=βY³A−βY⁴/4 = θ₄ G+K D,
B₅=βY⁴A−βY⁵/5 = θ₅ G+M(Y) D
```

lie in the indicated spans. For B₄, `G,D` span the two-dimensional E₅ annihilator. For B₅, `G,D,DY` are independent from the live distinct ghost reads, lie in E₄'s annihilator with terminal coordinate zero, and exhaust it by the native unanchored terminal-out rank. Thus `M(T)=m₀+m₁ T` is affine. These are actual paid reverse rows, using root orders 4 and 5 in the reverse defect grading, not guessed ordinary weights.

Use `U` for the reflected coordinate of the latest regular interior row, and `W,R` for the second and third latest. (These clock symbols are unrelated to the subspace `U₆`.) At U, D(2) and the vanishing G component force `U≠V`, since otherwise all nonzero later reflected donors have a single clock and its powers 1,2 would require both half and third. Solving those two literal equations gives its normalized dirty tap `D_U/b_U=U³/[6V(U−V)]`. Evaluating B₄ there then gives

```
K=V(V−U)(V−U/2).
```

At any ghost i, exact D(2) and vanishing G_i give zero right-hand targets for its degree-one and degree-two weighted row moments. For degree three the target is `K D_i`. If it has at most the two regular interior coordinates U,W later, applying the polynomial `y(y−U)(y−W)` to all later taps yields `(V(V−U)(V−W)−K)D_i=0`. The coefficient equals `V(V−U)(U/2−W)`, nonzero because fixed distinct interior U,W satisfy `U≠2W` (verified on the fixed roots). Thus every ghost precedes the three latest ordinary interiors.

In the nonconstant case the first active dirty i must precede those three too. Write `s_i=b_i V/2−D_i`. The degree-1,2,3 regular suffix taps from its column have sums `V s_i,V² s_i,(V³−K)s_i` respectively: subtract the dirty contributions from the true rows and calibrate the G coefficient for B₄ at the late dirty j (`D_j=b_jV/2`, `G_j=b_jV³/6`). The same polynomial as the ghost case would give `s_i=0` if only the last two regular interiors follow. Then `D_i+D_j=0`, which together with Dg=0 kills the core ghost, impossible. In the constant case the earlier dirty is the first nonzero-clock stage anyway. It follows that the last three ordinary interiors are **physical stages 7,8,9**. Their reflected coordinates are respectively R,W,U, possibly with a regular core clock coinciding with V at R or W; the formulas below do not divide by those two differences.

The B₅ ratio at U and W, using repeated reads of the exact lower rows, gives

```
M(U)= V(U−V)(4U²−5UV−5V²)/5,
m₁ = 3V(U−V)(U−W)²/[5(2U−W)] ≠ 0.
```

For verification, at a regular row of reflected coordinate y, write `Z_y=D_y/b_y`. At U the only nonzero reflected donor labels are U,V. Substitute `y⁴=(U+V)y³−UV y²` in the compensated B₅ read, obtaining `M(U)=(U+V)K+UV(U−V)(3U−5V)/10`. At W, apply `y(y−U)(y−W)` to get

```
Z_W= W³(2U−W)/[12 V(V−U)(U/2−W)].
```

For `y⁴` use the cubic-reduction identity on donor labels V,U,W. This gives

```
M(W)=(U+V+W)K + W³(3W²−5(U+V)W+10UV)/(60 Z_W).
```

The quotient `(M(W)−M(U))/(W−U)` simplifies to the displayed slope. All the fixed denominators `2U−W`, `U−2W` are guarded in the scalar check. A ghost after the earliest ordinary interior (so with exactly U,W,R later) satisfies

```
M(Y_i)=V(V−U)(V−W)(V−R)+(U+W+R)K.
```

This follows by applying `y(y−U)(y−W)(y−R)` to the weighted later taps and using D_i nonzero. For an early active dirty i placed after that same earliest regular, the exact degree-four *regular* shifted moment is `(V⁴−M(V)) s_i` by calibration at j, and `s_i≠0` (otherwise D kills the alternate core ghost). The same equation must then hold with Y_i=V. Solving the nonzero affine equation in either case gives the fixed value

```
Z(U,W,R) = [10 R U²−25 R U W+10 R W²+U²W+UW²]/[6(U−W)²].      (3)
```

In particular at most one ghost can be after the earliest regular, and any such ghost has prescribed reflected coordinate independent of ξ.

Finally the normalized dirty taps at U,W,R are `Z_s=k_s/[V(V−U)]` with

```
k_U = −U³/6,
k_W = W³(2U−W)/[6(U−2W)],
k_R = R³(2U−W)(3R²−5R(U+W)+10UW)
      /[6(4RU²−13RUW+4RW²+U²W+UW²)].                 (4)
```

The first two were derived above. For R apply the polynomial `y(y−U)(y−W)(y−R)` to the normalized exact degree-1 through degree-4 reflected tests on its inclusive suffix. The coefficient multiplying `Z_R` is `m₁ (Z(U,W,R)−R)` and its right-hand primitive is `−R³(10UW−5R(U+W)+3R²)/60`. Substitution gives (4). These are exact polynomial identities, with only the displayed fixed guards and `V(V−U)≠0`.

## 3. Corrected nonconstant one-off bridge

For this branch the valid one-clock census gives `g²=γg+Q(C)h`, with two non-core h-head labels and `Q(ξ)≠0`. The invariant E₆ clock blocks give exactly Lobatto ordinary aggregate, one block's excess at ξ, and other counts as in the original rank band. Under the exactly-one-off premise, `L` is nonzero: if q is an exterior head then its terminal identity requires `L(q)≠0`; if `ξ=q` and `L=0` the core identity would imply constant g. There are two assignments:

- `ξ=q` off, and the two heads are 1 and τ, where τ is a common root of `H,L` (it can at this point be 0). No other fixed head can be live because it would require another L root. The ξ block has three rows; its two nonzero g values on the off fiber, and the paid g and g² moments, give one cancelling active pair plus a different-g ghost. At 1 the extra row is a ghost because terminal mass matches. At τ the two rows have a vanishing h mean and h² mean: on the core, each g value class has zero aggregate and h is its function, and the other head is a ghost. Nonzero fixed τ mass forces one clean regular and one h-ghost.
- ξ fixed interior and q an off head: `δ=0` on the earliest ξ row and nonconstant g forces `L(ξ)=0`, so put τ=ξ. The other head must be 1, and both h-heads are ghosts. The global h² payment then adds the core fourth g moment from `h=g(g−γ)/Q(ξ)`, all earlier moments through g³ already paid. The four-row core has one clean regular for its nonzero fixed mass, a cancelling active pair, and an alternate-g ghost; group the nonzero g values by the degree-four nodal tests. This gives the same signed ghost skeleton required in §2.

To fix q **without a degree-five forward test**, write `q#=1−q`, and use the actual D row of §2 on the seven reflected physical numerical labels. It kills clock polynomials through degree five, so its aggregate at s is

```
σ/[Λ′(s)(s−q#)],          Λ(X)=(X−1)H(X)
```

for a common nonzero σ (the clock-one ghost's D entry is nonzero and the terminal coordinate is zero). Here the formula is used only at fixed labels s. Among the last three regular interior blocks, at most one is nonsingleton, namely `τ#=1−τ`. At any singleton s among U,W,R, the exact tap (4) gives the equation

```
E_s (s−q#)=σ V(V−U),      E_s=k_s b_s Λ′(s).
```

The fixed `b_s Λ′(s)` is the unit primitive of the degree-five polynomial `Λ/(X−s)` for the six-node rule; this is an exact *ordinary output* integration well below its paid degree nine. Comparing two singleton equations gives the guarded linear formula

```
q#=(E_s s−E_t t)/(E_s−E_t).                           (5)
```

If all three are singletons, their third ratio fails for every fixed order (this includes `τ=0` or τ equal to the first ordinary interior x). Otherwise use (5). The finite tests modulo 419 show all denominator guards are units, and that (3) is not any of `0,τ#,q#`. Those are exactly the reflected ghost labels and the possible early-dirty clock. Therefore all three ghosts and the early active dirty precede x, making x **physical stage 6**. The two prior ξ rows have different g values (one is the ghost and the other the early active), so the changed ξ can only occur after the first head. The real prefix is origin, first ξ, first head y, then second head z and changed ξ in either order. Also τ is fixed interior and x is a different fixed interior; ξ cannot equal the latest regular clock.

At x the C(5) input degree-four nodal cardinals determine aggregate taps `S_v` on the five known nodes `{0,ξ,τ,1,x}` if ξ=q, or `{0,ξ,q,1,x}` if q is a head. These are precisely the five fixed nodes needed for the actual row; no input degree five is invoked. The true local tests from the original scalar packet now apply with **q from (5), not the former quintic**. Briefly put `L=ℓ(X−τ)`, `s_v=ℓ h_v` on a head, `F=H/(X−τ)`, and `α=3(y−ξ)(y−2ξ)/ξ²`, `h_y=ξ²y³/[36(y−ξ)]`. Then `s_1=−1/(1−τ)`, `s_q=−H(q)/(q−τ)` if q is a head, and if ξ=q the actual equation `Ah(x)=Ag(x)=0`, `Ae_t=0` gives `s_τ=I F(x)/S_τ−F(τ)` (input F has degree four). If the changed core is before z, the literal C4 defect at that core yields, after cancelling its changed g-value difference,

```
α H(ξ) h_y − γ(y−ξ/2)s_y(ξ−τ)=0                    when ξ=q,
α h_y(S_y s_y+S_z s_z)−γ(y−ξ/2)s_y S_ξ=0          when q is a head.
```

If it is after z, all prior core g values at z are γ. The degree-three `X(X−y)(X−z)` read produces

```
36(ξ−y)(y−2z)s_z h_y−ξ² z³(2y−z)s_y=0.
```

The corrected finite replay excludes all these cases. If the represented ordinary clocks were all fixed and `L≠0`, nonconstant g would force L(ξ)=0 as in the second assignment, leaving only clock one for an exterior h-head, contradicting the need for two. With `L=δ=0`, that argument does not apply; in that case the old nodal quintic when all interior labels are present is `H/42` itself, and its genuine grade-six residual prevents the previous attempted exclusion.

## 4. Exact verification scope

`DIRKOrderTenPaidOneOffRepairScalar.lean` and its audit verify the fixed Radau guards, the constant common-root separation, and the nonconstant reverse-ratio/prefix checks modulo 419. The nonconstant replay also succeeds modulo 587. The existing p419 arithmetic module is reused, but neither of its previous forward-quintic consistency checks is used. The above rank/tableau and good-reduction bridges are mathematical, not yet a fully native Lean `HasOrder` theorem.

Good reduction uses only the splitting field of the fixed clock quartic, whose four distinct roots at 419 are `[67,141,279,353]`. The characteristic-zero denominators are units after reduction by the explicit guards. In the nonconstant case q is a rational expression of fixed roots by (5); no unknown tableau coefficient is reduced. In the constant case q is integral after the guarded monic normalization of (1), and the modular common-root proof allows any residue extension. This is a characteristic-zero argument and is not a proof about all positive-characteristic order-ten tableaux.
