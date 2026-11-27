# One exceptional clock is impossible in the active nonconstant DIRK10/11 branch

> **Proof status (2026-11-27):** This note contains an invalid use of a degree-five donor polynomial. A row satisfying `C(5)` integrates input degrees at most four. The claimed consequences of the degree-five step, including its finite tests as applied to actual tableaux, are suspended. See the [scope correction](dirk-order10-one-clock-grade-erratum.md).

Assume a genuine eleven-stage lower triangular tableau of order ten over a characteristic-zero field. Let `c=A1`, `C=diag(c)`, `β=bᵀ`, and `g=Ac²−c³/3`. Suppose every nonzero `g` is at one physical clock `ξ`, some `b_i g_i` is nonzero, and the nonzero values of `g` are not all equal. **Then there cannot be exactly one numerical physical clock outside the six fixed Lobatto clocks.** Together with the prior all-Lobatto exclusion, this leaves at least two off-Lobatto labels in this active nonconstant branch. The independent all-ghost branch is not addressed. No ordering or positivity of tableau weights is assumed, and the unrestricted DIRK10 interval is still 11–12.

## 1. Paid bands and the exact physical prefix

Use the reviewed saturation and the one-clock reduction. Write

```
γ=ξ³/6,      h=(A−ξ/2)g,
H(X)=42XJ₄(X),   J₄=X⁴−2X³+4X²/3−X/3+1/42,
e_t=H(c)+δg+L(c)h,           deg L≤1,    b_t=1/30,
F₄=⟨g,h⟩,    F₅=⟨g,h,Ch⟩,    Ah=(m+nC)h,
g²=γg+Q(C)h,    Q(ξ)≠0,
U:=F₆∩{v_t=0}=⟨g,h,Ch,C²h⟩.
```

The two non-core head labels with `h≠0` are the roots of `Q`. On the ξ fiber `h=g(g−γ)/Q(ξ)`, so a clean core row also has `h=0`. On every ordinary row outside ξ and the two head labels, all `F₅` defects vanish. Such a row integrates polynomials through degree four exactly as an actual `C(5)` receiver. This is also true at any other physical row where both `g,h` vanish.

The ordinary quadrature is known to be exactly the six-site Lobatto rule `ν` from the nonconstant one-clock analysis. The actual `E₆` is its invariant clock space plus the clock-invariant `U`: two independent defect directions on ξ and one on each head, with off-Lobatto indicators already in these defect directions. At each fixed label its ordinary indicator adds one dimension, because its nonzero ν mass precludes a local indicator in `U`, which is β-null. Since `E₆` has codimension one and `G` is proportional to the nonzero actual row `βg`, every block has physical size equal to this dimension except ξ, which has one additional row. In particular ξ is not clock 1: the last active non-unit clock is precisely the latest nonzero entry of `G`, with local value `b_j(1−c_j)^3/6≠0`. That active dirty row comes after all active nonterminal rows of any other non-unit clock. The true terminal is at clock one with `h=g=0`.

Let `x` be the first physical nonzero ordinary clock outside the three exceptional labels (ξ and the heads). Each such clock is fixed, has a singleton block, and carries its nonzero ν weight. Before or at `x`, all numerical donors are among those three exceptional labels, 0, and `x`. If one head is 0, they give at most two nonzero earlier donor labels, one of which is fixed (the other is the sole off-Lobatto label). For a `C(5)` receiver whose possible donors are `{0,a,b,x}`, the anchored nodal quartic and its `X` multiple give `a+b=x`, `5ab=x²` by literal inclusive quadrature. Eliminating the unknown label gives `5a(x−a)=x²` with distinct fixed `a,x`, impossible by the exact 20-pair residue check. It is harmless to include candidate donors that have not yet appeared: the polynomial still vanishes on every actual donor. Thus both heads are nonzero.

There are two block assignments.

- **The off-Lobatto label is ξ.** Both heads are fixed. A fixed interior head with nonzero `h` must be a root of `L`, since there `H=g=e_t=0`. The nonzero affine `L` has at most one root. Consequently the two heads are `τ`, an interior root of `H,L`, and clock 1. There are three ξ rows and exactly two nonzero `g` values there: the terminal identity gives `δ=−H(ξ)/γ≠0`, `L(ξ)≠0`, and on the ξ fiber `(g−γ)(δ+L(ξ)g/Q(ξ))=0`. The first two g moments kill each value's aggregate. Hence the three core rows are an opposite-weight equal-g active pair and one different-g ghost. At clock 1 the only nonterminal row is its head, necessarily a ghost because `b_t=ν(1)`. At τ there are two rows, one rather than both with nonzero h. Indeed the two g value aggregates at ξ vanish, so their h² total vanishes since h is a function of g; the clock-1 h² total is zero. Thus the remaining τ fiber satisfies `∑ b h=∑ b h²=0`, with the linear test also isolable by `U`. For any two h-values their quadratic nodal identity implies `ν(τ) h_1 h_2=0`. Therefore the nonzero h head is a ghost and the other row is clean h=0 and carries ν(τ).

- **The off-Lobatto label is a head `q`.** The fixed core ξ is an interior clock, because it is nonzero and not 1. Its earliest cubic value is `γ` and its earliest h value zero, so `δ=0` from `H(ξ)=0`. Nonconstancy of g gives a row with `h≠0` on ξ, and hence `L(ξ)=0`. Set `τ=ξ`. The other nonzero fixed head cannot be an interior label different from ξ, because it would be a second root of `L`; it is clock 1. Its extra physical stage is a ghost since `b_t=ν(1)`, and the single physical off-head q is a ghost since its ordinary mass vanishes. The ξ block has four physical rows. Since outside ξ the paid `βh²=0` now has zero contribution, the identity `h=g(g−γ)/Q(ξ)` on ξ and the three paid g moments give `βg⁴=0`, without requiring a grade-12 test. A degree-four nodal test using the nonzero g-values kills each nonzero g aggregate. The ordinary mass ν(ξ) is nonzero; at least one physical clean ξ row is needed. The four rows are exactly two active dirty rows with equal g and opposite weights, one different-g ghost, and one clean ξ row carrying the fixed mass. This count uses only signed moments.

In both assignments the exceptional labels are numerically `{1,τ,q}`, where τ is fixed interior, q is the sole off-Lobatto label, and the receiver `x` is another fixed interior. If the clean (non-ghost) row at τ were earlier than x, it would be a `C(5)` receiver with possible donor labels `{0,τ,1,q}`. The same fixed-pair guard, now with fixed pair `(1,τ)`, forbids this. Clock zero has only the physical origin, because it is a fixed ordinary singleton. We will see below that the aggregate ξ tap and both head taps into x are nonzero. Since `Ag(x)=0`, at least two ξ rows with different g-values precede x. The latest active dirty row must follow x, since x is active and has clock different from one. The core clean row, if any, was just excluded before x. Thus exactly two ξ rows appear before x; the second is a genuinely changed g-value `g'≠γ`. Each head supplies one ghost row before x, since its regular partner at τ or 1 cannot precede x. The first four rows after the origin are therefore

```
first ξ, first head y, (second head z and changed ξ in either order).
```

The first changed ξ cannot precede y: through any prefix using only `{0,ξ}`, all ξ defects equal `γ` by the retained `C(2)` tap into ξ. Consequently x is the sixth physical row, and y,z are distinct. This is chronology of actual rows including the diagonal, not a replacement tableau.

## 2. Finite determination of q and the aggregate taps

At x, `C(5)` applies on the node set `{0,ξ,y,z,x}={0,τ,1,q,x}`. The primitive of `X(X−τ)(X−1)(X−q)(X−x)` must vanish at x. Expand it, divide by its nonzero `x³/60`, and solve linearly:

```
q = x[2x²−3(τ+1)x+5τ]/[3x²−5(τ+1)x+10τ].
```

The denominator is a unit in the clock-only good-reduction test below. For any one of these five distinct nodes `v`, the aggregate physical tap `S_v` into x is the primitive at x of the degree-four product at the other four nodes divided by its value at v. This follows by the actual `C(5)` receiver property, including the diagonal at x. The certificate verifies the needed `S_ξ,S_y,S_z` denominators and that these three taps are nonzero for every pair `(τ,x)`. This proves the chronology claims in §1 without presuming an appearance for any donor. In the independent replay all five taps are also nonzero.

Use `L(X)=ℓ(X−τ)` and define `F(X)=H(X)/(X−τ)`, a degree-four polynomial. Write `s_v=ℓ h_v` at a head v and use the following actual values:

- At the nonterminal head at one, `s_1=−1/(1−τ)` by the terminal identity.
- If q is a head, `s_q=−H(q)/(q−τ)` by the same identity.
- If ξ=q, at the ghost head τ put `s_τ=I F(x)/S_τ−F(τ)`. To derive this, away from τ the vector `ℓ h+F(c)−e_t/(1−τ)+δ g/(ξ−τ)` is zero by the terminal identity. Its only τ donor into x is the ghost head. Applying A at x gives `I F(x)` because `Ah(x)=Ag(x)=0`, `A e_t=0` and the receiver integrates F exactly. This fixes `s_τ` with no unknown tap. Here `I` is the ordinary primitive anchored at zero.

Finally the first head y uses only the clocks `0,ξ,y` in its inclusive prefix. Its two retained clock moments give

```
h_y = ξ²y³/[36(y−ξ)],
α = 3(y−ξ)(y−2ξ)/ξ²,
Ac³−c⁴/4 = (3ξ/2)g+α h.
```

The last identity is global from `F₄=⟨g,h⟩`; the first core and first head fix its coefficients. We use `ℓ h_y=s_y` to clear the scale instead of solving for an unknown tableau coefficient.

## 3. The two possible timings of the changed ξ row

### Changed ξ before z

At that changed row the donor clocks still lie in `{0,ξ,y}`. There `X³=(ξ+y)X²−ξ yX` on every donor. The displayed `C(4)` defect, ordinary C(2), and `Ac²−c³/3=g` give

```
α h'=(y−ξ/2)(g'−γ),        h'=g'(g'−γ)/Q(ξ).
```

Cancel `g'−γ≠0`. If `ξ=q`, the terminal identity gives `g'/Q(ξ)=−δ/L(ξ)=H(ξ)/[γℓ(ξ−τ)]`; therefore the necessary scalar test is

```
α H(ξ) h_y − γ(y−ξ/2)s_y(ξ−τ) = 0.             (core before)
```

If `q` is a head, combine `Ag(x)=0` with the total core tap `S_ξ`. The tap into the changed core row is `−γ S_ξ/(g'−γ)`. Now `Ah(x)=0` and the two head taps give `ℓ g'/Q(ξ)=(S_y s_y+S_z s_z)/(γ S_ξ)`. Together with the same canceled `C(4)` equation this requires

```
α h_y(S_y s_y+S_z s_z) − γ(y−ξ/2)s_y S_ξ = 0.   (head before)
```

### Changed ξ after z

At the second head z, all available core rows still have the initial g-value `γ`, so their total tap `S` satisfies `γ S=h_z`. Evaluate `P=X(X−y)(X−z)` in that row. The only possible nonzero donor value is `P(ξ)`, while `I P(z)=z³(2y−z)/12`. The lower two stage moments are exact at z and the `C(4)` defect is `α h_z`. Thus `S P(ξ)=I P(z)+α h_z`. Substituting the known α and the scale from the first head gives the same necessary equation in either assignment:

```
36(ξ−y)(y−2z) s_z h_y − ξ² z³(2y−z) s_y = 0.   (either after)
```

## 4. Exact check and characteristic-zero transport

There are four possible τ and three possible distinct x, two possible first heads y, and two timings per block assignment. All 48 core timing tests and all 48 head timing tests have nonzero residue modulo 227. The standalone kernel-checked Lean file tests both block assignments, all numerical division and tap guards, and the fixed-pair guards. The independent Python replay checks the same equations modulo 227 and modulo 419. The Python check expands the nodal product coefficient-by-coefficient, independently of the symmetric formula used in Lean.

Every scalar tested is a rational function of the four fixed interior clock roots, with guard denominators nonzero modulo 227. They lie in the localized splitting field of `42J₄`, not in a presumed integral model of the whole tableau. The leading coefficient 42 is a unit over `ℤ_(227)`; choose a prime above 227 in the splitting field. Its four fixed roots reduce to the distinct `[24,51,177,204]`, different from 0 and 1. All rational expressions used above reduce at this prime by the explicit guards, including q, the tap numerators and denominators, the first-head normalization, and the scale recovered from the τ tap. A vanishing necessary equation in characteristic zero would have vanishing residue in one checked case, a contradiction. No g-value, weight, or unknown tableau coefficient is reduced.

Lean scope: `DIRKOrderTenOneOffSharedScalar.lean` is `Init`-only and proves the finite checks with a typed audit. Sections 1–3 are the actual-tableau mathematical bridge using the previous reviewed ranks; they are not yet one native `HasOrder` theorem. No assertion is made for a positive-characteristic tableau merely because these scalar residues can be computed there. The active nonconstant r=1 branch with two or three off-Lobatto labels, the possibly constant shared-root branch, and the ghost-only branch remain separate.
