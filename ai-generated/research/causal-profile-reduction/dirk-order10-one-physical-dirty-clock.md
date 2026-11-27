# The single physical dirty clock in DIRK10 at eleven stages

> **Proof status (2026-11-27):** This note contains an invalid use of a degree-five donor polynomial. A row satisfying `C(5)` integrates input degrees at most four. The claimed consequences of the degree-five step, including its finite tests as applied to actual tableaux, are suspended. See the [scope correction](dirk-order10-one-clock-grade-erratum.md).

**Scope.** This note is about a lower triangular tableau of actual reviewed order ten with eleven physical stages over a characteristic-zero field. Let `c=A1`, `C=diag(c)`, `β=bᵀ`, and `g=Ac²-c³/3`. Assume there is exactly one numerical clock `ξ` among the rows with `g_i≠0`, counting zero-weight as well as nonzero-weight rows, with no hypothesis on signs or repeated clocks. No improvement of the unrestricted 11–12 stage interval is claimed. The paper deductions below use already reviewed native ranks; the new Lean files verify their indicated field-algebra and finite scalar components, not a complete `HasOrder` adapter.

## 1. One localized core and the exact two-ended band

Write `F_j` for the native grade-`j` zero-profile flag and `E_j` for the full flag (grade = tree size minus one). The order-ten saturation gives `C(2)`, a zero physical first row, `D(1),D(2)`, a last physical stage `t` at clock one with nonzero weight and zero `A` column, and dimensions `F₃=1`, `F₄=2`, `F₅=3`, `E₅=9`. The genuine reverse cubic row `G=β(1-C)²A-β(1-C)³/3` is nonzero and annihilates `E₆`. In detail, at the last active nonunit clock `j`, `D(2)` and triangularity give `d_j=(1-c_j)/2`, and hence `G_j=b_j(1-c_j)³/6≠0`; all entries after `j` vanish. There is such a `j`, since a quadrature supported at one alone cannot satisfy the first two paid moments.

The terminal indicator `e_t` is in `E₅` by the exact rank-two true `primitiveBack₃` annihilator, whose columns have zero terminal coordinate. Products pairing `E₅` with `F₄` (or its subspace `F₃`) give `F₄(t)=0`. The native inclusive Hermite outgoing and incoming estimates at `j=4` rule out clock invariance of either `F₄` or `F₅`: invariance would give `2+2≤3`. These estimates require characteristic zero; they do not need positivity. Define

```
h = (A - ξ/2)g.
```

There are at least six numerical clocks by the terminal-containing paid unanchored Cauchy test. The first nonzero clock must be `ξ`: with no other earlier nonzero clock, its `C(2)` diagonal is half its clock, so its cubic defect equals the cube of its clock divided by six. More generally, through any prefix using only `0,ξ`, aggregate taps into the `ξ` stages are `c_i²/(2ξ)` by `C(2)`, so `g=γ=ξ³/6` at `ξ`, `g=0` at zero, and `h=0` on this prefix. Let `y` be the first clock outside `{0,ξ}`. At its first physical row only its own diagonal reaches clock `y`; the actual total tap `S` into `ξ` satisfies

```
ξ S + y d = y²/2,       ξ² S + y² d = y³/3,
h_y = γ S = ξ²y³/[36(y-ξ)] ≠ 0.
```

Thus `F₄=⟨g,h⟩`. Since both `F₄,F₅` are non-invariant, `F₅=⟨g,h,Ch⟩` and `g,h,Ch,C²h` are independent. All `F₅` elements vanish at `t` (as `g_t=h_t=0`). Also `Ah∈F₅` and vanishes at the earliest nonzero clock, where `h` is identically zero throughout the inclusive prefix and `g=γ`. Consequently there are constants `m,n` with

```
Ah=(m+nC)h,       Ag=ξg/2+h.
```

A further exact local read gives `Ac³-c⁴/4=(3ξ/2)g+αh` with `α=3(y-ξ)(y-2ξ)/ξ²`. The first core row fixes the `g` coefficient; at `y`, `X³=(ξ+y)X²-ξ y X` on all prefix clocks, giving the displayed `h` coefficient. These identities are global, not just fits at the two measured rows, because the left-hand vectors are in `F₄` or `F₅`.

The polynomial part of `e_t∈E₅` vanishes at zero and has value one at `t`; paid testing against `(1−X)R(X)` for `deg R≤3` shows that, after factoring out `X`, its quotient is orthogonal for the weight `X(1−X)` against every such `R`. The corresponding four-by-four weighted Cauchy form is nonsingular (over the rationals, positivity of `X(1-X)` proves a nonzero determinant, which transports to every characteristic-zero field). Thus the endpoint scalar is

```
J₄(X)=X⁴−2X³+4X²/3−X/3+1/42,
H(X)=42 X J₄(X),                    β e_t=b_t=∫₀¹ H=1/30,
e_t = H(c) + δg + L(C)h,           deg L≤1.          (1)
```

Here the orthogonality of `J₄` is verified by integrating its four products with `X(1−X)X^k`. The two low-degree head components `g,h` in (1) are actual vectors. `A e_t=0` gives `T(c)∈F₆`, where `T=I H` and `I` is primitive anchored at zero. `T(1)=1/30≠0`. The generic native `dirk_grade_six_surplus_C2`, the five jointly separated anchored scalar grades through four, and `G E₆=0` imply `dim F₆=5`, `dim E₆=10`. Thus the full formula, not just a lower bound, is

```
U := F₆∩{v_t=0} = ⟨g,h,Ch,C²h⟩,
F₆=U ⊕ K T(c),                     E₆^⊥=K G.         (2)
```

All of this is over arbitrary characteristic-zero fields. The rank and incoming/outgoing inputs are `DIRKOrderTenSaturation`, `DIRKOrderTenKernelSeeds`, `DIRKPrefixHermite`, and `DIRKC2FourDebut` in the reviewed namespace.

## 2. Constant nonzero cubic values: actual three-debut cut

Assume `g` takes the common value `γ` wherever nonzero. Call rows with `g=0` exterior in this subsection; they may include later clean rows at numerical clock `ξ`. Let `a,b,u` denote the first three distinct nonzero exterior clocks in actual row order (at least four exist). The first is `a=y` above, with `h_a≠0`. If `h_b=0`, `Ag(b)=0` removes total taps to the dirty core, using the nonzero common `γ`. Defects through `F₅` vanish at that `b` row, so its inclusive `C(5)` integration of `X(X-a)(X-b)` and `X²(X-a)(X-b)` must be zero. These primitive values are `b³(2a-b)/12` and `b⁴(5a-3b)/60`, impossible together. Thus `h_b≠0`.

Before the debut of `u`, the genuine column `v=P(c)-P(ξ)g/γ`, `P=X(X-a)(X-b)`, vanishes on **all** earlier rows, including repeated clocks. For the native Volterra defect `R=CA-AC-A²`, `Rv∈F₅`. It vanishes on the strict prefix. Its `g` coefficient is killed by its value at the first core, and its two exterior affine coefficients by the observations at `a` and `b`. So `Rv=0`; its inclusive newest row reads `-d_u² v_u=0`, forcing `d_u=0`. In particular `IP;/h` takes the same value at `a,b` from `IP(c)-Av∈F₄`. Both values of `IP` are nonzero: `IP(a)=a³(2b-a)/12`, `IP(b)=b³(2a-b)/12`, and they cannot both vanish. Here and below evaluation of `h_a,h_b` means the rows of first occurrence.

For the paired cut, let `W` be the space of constant polynomials `q` for which `q h` on the strict prefix is a clock function on exterior rows, zero at clock zero, and constant across core rows. Define `Z` by the same tests on `Q(C)h` for affine `Q`. Then `dim Z≤dim W+1`. Origin-vanishing polynomials `B` of degree at most four have four dimensions. Pairs `(B,q)∈Bspace×W` with `B(a)=q h_a,B(b)=q h_b` have dimension at least `dim W+2`. A single actual multiple of `g` corrects `B(c)-qh` on every core row, so the corrected input is zero throughout the strict prefix. Its image under `A` is zero through the debut `u` by the already proved zero diagonal. The primitive residual belongs to `F₅`, and its affine `h` polynomial must be in `Z` by the same literal prefix tests. Thus the primitive values at `(a,b,u)` have rank at most `dim W+1`. A nonzero pair in their kernel has `B≠0`, since `B=0` forces `q=0` from `h_a≠0`. Its primitive has double root zero and roots `a,b,u`, and degree at most five, so is a nonzero multiple of `X²(X-a)(X-b)(X-u)`. Differentiating at `a,b` and comparing the common ratio `B(a)/h_a=B(b)/h_b` yields

```
(a²/h_a)(a-u) + (b²/h_b)(b-u)=0,
u(4ab-a²-b²)-ab(a+b)=0.                               (3)
```

The second formula uses the earlier `IP/h` relation and clears the nonzero factors. It is the `k=1` actual `DIRKC2PairedCut` / `DIRKC2BarycentricPort` argument and needs only `F₄,F₅`, not a guessed `F₆` band. Modulo 227, no distinct ordered triple from the five nonzero Lobatto clocks `{1,J₄ roots}` satisfies (3), as checked in the portable scalar certificate. Hence the constant case requires a non-Lobatto **exterior** clock, regardless of the value of `L`.

## 3. Nonconstant cubic values: two head clocks and one reflected block

Now `g²` is not proportional to `g` and belongs to `F₆`, with zero terminal coordinate. Write `g²=κg+Q(C)h` from (2), with a nonzero quadratic-or-lower `Q`. Every clock **distinct from ξ** with a nonzero `h` value is a root of `Q`, so there are at most two such exterior head labels, counting possible clock zero. There cannot be only one: on the two numerical fibers of `g,h` the degree-two clock polynomial vanishes, making `⟨g,h,Ch⟩` invariant, contrary to the actual `F₅` rank growth. Let the two labels be `a,b` (this notation is independent of §2). Then `Q(ξ)≠0`, and from the leading core value and `h=0` there, the coefficient `κ` is `γ`. It follows that

```
h_i = g_i(g_i-γ)/Q(ξ)  when c_i=ξ.
```

In particular `h=0` on a clean core row. The space `U` is the clock-invariant direct sum of `⟨g,g²⟩` on `ξ` and the two one-dimensional `h` projections on `a,b`. To see invariance directly, `g,g²` give two independent directions on `ξ`, and the two projections are obtained by clock interpolation from the three powers of `h`. These four pieces are independent and exhaust `U`.

Write `ℒ={0,1,J₄ roots}`, extending the field to split this fixed polynomial if necessary. Every physical clock outside `ℒ` has its full physical indicator in `U`:

- At an exterior value `z∉ℒ`, (1) forces `L(z)≠0` and the same nonzero `h=-H(z)/L(z)` at every row of that clock. Hence this is `a` or `b`, and its indicator is the scalar-normalized exterior projection in `U`.
- If the core clock is `ξ∉ℒ`, the leading row implies `δ=-H(ξ)/γ≠0`. If `L(ξ)=0`, (1) fixes all cubic values to the same `γ`, contradiction. Otherwise (1) on this fiber factors as `(g_i−γ)(δ+L(ξ)g_i/Q(ξ))=0`. The possible values are `γ` and `-δQ(ξ)/L(ξ)`, both nonzero and distinct because there is nonconstancy. The full indicator is a polynomial of degree at most two in `g` with zero constant term, so is in `⟨g,g²⟩`.

Since `β U=0`, the aggregate quadrature vanishes at all off-Lobatto clocks. It is exactly the fixed six-point Lobatto rule: agreement on degrees 0–5 determines the weights, and every one is nonzero. The endpoints have weight `1/30` by symmetry and integration of `H`; for each interior value the polynomial `X(1-X)` times the square of the cubic nodal product of the other interiors has degree eight, vanishes at the other five clocks and has positive integral in the real splitting field of this fixed rational polynomial. The four clock roots are distinct and lie in `(0,1)`: under `t=2X−1`, the quartic is a nonzero multiple of `21t⁴−14t²+1`, whose values of `t²` are `(7±2√7)/21`. The nonzero rational-algebraic integral transfers to the splitting field in use; the assumed tableau field need not be ordered. Consequently all six clocks of `ℒ` are physically present.

The off-Lobatto indicators already lie in `E₆`; interpolate each fixed clock indicator using a degree-five polynomial on `ℒ` and subtract its values on the off-Lobatto fibers. This puts **every** clock indicator in `E₆`, which is exactly their span plus `U` (because `T(c)` is a clock function). In particular `E₆` is `C`-invariant. Its annihilator `K G` is supported at a single clock `ζ` and the following physical census is exact:

| Label type | dimension of its local `E₆` block |
| --- | ---: |
| fixed ordinary label (not `ξ,a,b`) | 1 |
| fixed head label `a` or `b` | 2 |
| off-Lobatto head label | 1 |
| fixed core label `ξ` | 3 |
| off-Lobatto core label `ξ` | 2 |

Each fiber has exactly the stated number of physical rows **except** `ζ`, which has one additional row. Indeed the three nonconstant defect contributions give dimensions `2,1,1` over the clock blocks. Splitting each fixed indicator off them is direct: if a linear combination of fixed indicators lay in `U`, the actual local projection preserving `U` would put every summand in `U` separately, and the nonzero ordinary masses with `β U=0` force all its coefficients to vanish. The off indicators are already included, and there is exactly one missing dimension in the total physical space. The single checked nonzero `G_j` at the last active nonunit clock identifies `ζ`. If any individual `b_i g_i≠0`, the actual paid row `βg` annihilates `E₆` and is nonzero, so `ζ=ξ` and `G` is proportional to `βg` (no transpose or division by an individual weight).

### Finite first clean cut

At the first physical row of a nonzero label `x` outside `{ξ,a,b}`, the row has exact `C(5)` since `g=h=0`. Its inclusive donor clocks lie in `{0,ξ,a,b,x}`. If all physical clocks are Lobatto, there is a contradiction: with three nonzero earlier candidate labels, integrate `X(X-ξ)(X-a)(X-b)(X-x)` and use `C(5)`; the primitive must be zero. Its 60-fold numerator does not vanish on any of the 120 ordered distinct nonzero Lobatto quartets mod 227. If one of `a,b` is zero, the analogous nodal quartic and its `X` multiple require `a'+b'=x,5a'b'=x²` on two distinct nonzero earlier candidate labels, also impossible by the finite triple check. Using labels that have not yet appeared is harmless since the nodal tests still annihilate every actual donor. Thus **nonconstant `g` requires at least one off-Lobatto clock**. There can be at most three, all in `{ξ,a,b}`. When just one of these three is off-Lobatto, the nodal quintic equation at `x` is linear in that unknown clock `q`. If the other two candidate clocks `a′,b′` are nonzero, the only possible value is

```
q=x [2x²−3(a′+b′)x+5a′b′]/[3x²−5(a′+b′)x+10a′b′].
```

The denominator is nonzero for all 60 ordered fixed triples by the same mod-227 verification, so this set of possible labels is finite (at most 30 before further tests, by interchange of `a′,b′`). If there are only two nonzero candidate clocks `q,a′`, the two-donor equations give `q=x−a′`, `5q a′=x²`. This would force `5a′(x−a′)=x²`, impossible at all 20 fixed distinct ordered pairs modulo 227.

In the one-off case with three nonzero candidate clocks, all five aggregate taps from `{0,a′,b′,q,x}` into `x` are nonzero. Indeed the degree-four nodal product omitting one of the five donor clocks has an integral equal to its value at that clock times the corresponding aggregate tap. For each of the five omitted clocks, the cleared primitive numerator modulo 227 is nonzero at every fixed triple and the unique `q` above; the inverse guard for the denominator is checked. This is a polynomial good-reduction statement allowing even incidental coincident residues of `q`: its characteristic-zero clock is distinct by hypothesis, and no Lagrange denominator is reduced. In particular the diagonal at `x` is nonzero and each of `ξ,a,b` must physically precede `x`. Since the total `ξ` tap is nonzero and `Ag(x)=0`, at least two physical ξ rows with different `g` values (possibly zero if `ξ` is fixed) precede `x`. Thus this first regular nonzero clock occurs no earlier than physical stage 6.

Combining the constant and nonconstant ledger, `L=0` is wholly impossible: if `δ≠0`, (1) forces the same nonzero `g` value wherever dirty and every exterior nonzero clock to be Lobatto, including the terminal, contradicting (3). If `δ=0`, (1) forces every physical clock to be Lobatto, and §2 or §3 then applies.

## 4. A weighted degree-eleven test for regular `L`

Even in the general rank band (2), let `μ` be the ordinary aggregate quadrature and `ν` the fixed six-point rule. Set `Δ=μ−ν`, which annihilates ordinary polynomials through degree nine. The quantities `βh=βh²=βCh²=0` are paid (grades 4,8,9). Terms involving `g` and `g²` in (1) have zero aggregate weighted mass on their single clock, independently of possible signed weights.

- If `L` is a nonzero constant, square (1) after solving for `h`. Since `H(1)=1`, `g_t=0`, and `b_t=1/30`, `β h²=β C h²=0` imply `Δ(H²)=Δ(XH²)=0`. The leading degrees are ten and eleven with nonzero coefficients, so `Δ` annihilates polynomials through degree eleven.
- If `L` is nonconstant with root `τ`, assume `τ∉{ξ,1}` and `H(τ)≠0`. Equation (1) then excludes τ from the physical clocks, and it is also not a Lobatto node. Set `f=H/L`. From `βh=βh²=0` get `Δ(f)=Δ(f²)=0`, as the terminal contributions have the prescribed fixed mass and all core-linear/quadratic terms are paid. `f` has a nonzero simple pole at τ and polynomial part of degree four, while `f²` has a nonzero double-pole coefficient and polynomial part of degree eight. Thus `Δ` kills the simple and double reciprocal tests at τ. The measure with masses `Δ_z/(z−τ)²` now annihilates polynomials through degree eleven.

Either way if `Δ≠0` it needs at least 13 distinct possible locations by the Vandermonde matrix, so the original tableau has at least seven distinct **active off-Lobatto** labels. Nonconstant `g` was already shown to give `Δ=0`. If `g` is constant on its dirty support and `L(ξ)≠0`, its nonterminal dirty stages have exactly the same `(clock,g,h)` (use (1) and earliest `h=0`); all their `E₆` values agree by (2). Therefore if no dirty weights are active there is exactly one physical dirty row: two would force the true `G` to be a contrast supported on ghosts, contradicting its actual latest active pivot. If dirty weights are active, there are exactly two dirty rows, both active with opposite weights. Here there cannot be three identical rows in a codimension-one flag, and the paid `βg=0` needs at least two active dirty rows.

In the regular `L` case with `Δ≠0`, `L(ξ)≠0`, and two active dirty rows, exactly seven distinct active **clean** off-Lobatto clocks occur (their dirty aggregate contribution is zero). This pays seven physical rows, plus two dirty rows and both physical endpoints. Hence the dirty stages are precisely physical 2 and 10, one-based, since the first nonzero and last active non-unit clocks are dirty; stages 3–9 are the seven off-Lobatto clean states. If `q=ξ³/6`, the two diagonals are `ξ/2,(1-ξ)/2` and the tap from the later dirty sink into the first is `(2ξ-1)/2` by `h_{10}=0`. The exact remaining weighted relation is `GA=d_{10}G+λ βh`: these rows are in the two-dimensional `E₅^⊥`, and `G,βh` are independent by their supports. The coefficient of `G` is read at stage 10. The coefficient `λ` is nonzero: otherwise the dirty pair's equality hyperplane would be preserved by `A` and by coordinate products, so all elementary stage columns agree on the pair; folding the later row into the earlier would preserve order and violate the native 11-stage lower bound. (This nonzero guard is not required for the next reverse cut.) No rational-pole claims are made when the root collides with `ξ,1` or an interior Lobatto root.

### Literal opposite-end pivots on this restricted skeleton

Let `w=βh` and `Y=1-C`. Stages 3–9 have distinct active off-Lobatto clocks, with `h_i≠0` on each by (1). Hence `G,w` give the entire two-dimensional `E₅` annihilator and `G,w,wC` give the annihilator of `E₄` with row-terminal coordinate zero. To see the latter dimension, `E₄` has rank seven and does not contain `e_t`: a contrary polynomial profile of degree at most four would have six consecutive paid unit moments equal to the same nonzero terminal weight, impossible by the unanchored Cauchy lemma. Both `wC` and `wA` annihilate `E₄` by grade transport and vanish at `t`; they have independent-clock support from `G`, and `wA` has zero coordinate at stage 10 by triangularity. Thus also `wA=(m′+n′C)w` (with the diagonal scalar understood componentwise).

The forward cut in §2 fixes a zero diagonal at the third clean debut, **stage 5**, and gives the cubic on its actual clocks `(c₃,c₄,c₅)`. For the opposite cut use reflected coordinates `a′=1−c₉`, `b′=1−c₈`, `u′=1−c₇`, and the actual row `ℓ=βP(Y)−sG`, with `P=X(X−a′)(X−b′)`. Choose `s` to kill its coordinate at stage 10. The row already vanishes at stages 9, 8 and 11, and is nonzero at stage 7 since that active clock is distinct from 9 and 8 and not unit. For the same Volterra operator `R=CA−AC−A²`, `ℓR` annihilates `E₄`: `R E₄⊆F₆`, so both the grade-three weighted polynomial and `G` annihilate that image by the actual order payments. Its terminal coordinate is zero. It therefore lies in `⟨G,w,wC⟩`. Its strict reverse prefix vanishes by triangularity; the coordinate at 10 kills its `G` coefficient and the two different live `w` clocks 9,8 kill the affine part. Thus `ℓR=0`, and at its first reverse live row the equation reads `−d₇²ℓ₇=0`, forcing a second diagonal zero at **stage 7**. The reviewed gap-two overlap lemma now also gives nonzero stage-6 diagonal and both neighboring taps.

The reflected paired cubic is literal: for degree-three `P`, the row `βIP(Y)−ℓ A` belongs to `⟨G,w⟩` by the paid reflected monomial defects and vanishing terminal coordinate. The reverse inclusive cut makes its `A` term zero through stage 7. Reading stages 9 and 8 gives the same common ratio `IP/h` as in §2, after division only by their nonzero weights. For arbitrary origin-vanishing `B` of degree at most four, fit `B(a′)=q h₉,B(b′)=q h₈`. The pair space has dimension at least three. Subtract `q w` and a suitable `G` multiple from `βB(Y)`; the resulting row vanishes at 11,10,9,8, and multiplying by `A` also gives zero at 7. Its primitive residual is in `⟨G,w,wC⟩`, so the three primitive observations at 9,8,7 have image dimension at most two. A nonzero kernel polynomial gives the same barycentric equation as in §2, yielding `u′(4a′b′−a′²−b′²)−a′b′(a′+b′)=0`. The full two-sided statement uses no division by any zero or unknown weight. It is a restricted skeleton, not an exclusion or an existence certificate.

## 5. Finite verification and transport

`DIRKOrderTenOneClockScalar.lean` uses only `Init` and checks the quartic roots modulo 227, the 60 ordered nonzero triples for (3) and the two-donor relation, the 60 denominator guards and five aggregate tap checks for the one-off label, the 20 two-label guards, and the 120 ordered nonzero quartets for the anchored quintic. `DIRKOrderTenOneClockAlgebra.lean` checks the displayed first exterior tap equation, the two-donor contradictions/implications, the paired-cubic simplification and the quadratic-root split generically over fields; the actual filtration/accounting proofs above are mathematical.

For characteristic-zero transport only the fixed-clock splitting field is used. The polynomial `42J₄` is monic after dividing by a 227-unit, thus its clock roots are integral over `ℤ_(227)`. Choose a prime over 227 in their splitting field; the four distinct mod-227 roots in `𝔽₂₂₇` are `[24,51,177,204]`, different from 0 and 1, so reduction of the five nonzero fixed labels is injective. All checked scalars are polynomials in those clock roots with integer coefficients (the primitives are cleared by 60, a 227-unit). Any vanishing in characteristic zero would reduce to a zero at one of the checked tuples. No coefficient or physical tap of the unknown tableau is assumed integral, and the native rank input has not been asserted in characteristic 227.
