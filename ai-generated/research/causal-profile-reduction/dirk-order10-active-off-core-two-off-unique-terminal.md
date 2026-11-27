# Active nonconstant DIRK10/11: off cubic core, one off head, unique terminal

Over a characteristic-zero field, consider an actual eleven-stage lower triangular tableau of rooted order ten. Assume the cubic defect `g=Ac²−c³/3` is supported at one numerical clock ξ; its nonzero values are not all equal, and at least one `b_i g_i` is nonzero. This note excludes the precise chart where ξ and one of the two exterior h-heads q are off the six fixed Lobatto labels, and the other h-head τ is a fixed label **different from 1**. The head-at-1 case is not covered. No weight signs, ordering, or reality hypothesis is required.

## 1. Actual paid setup

Use the established one-local rank band and the corrected signed-skeleton and reflected suffix from `dirk-order10-paid-one-off-repair.md`. Set `h=(A−ξ/2)g`, `γ=ξ³/6`, and `H(X)=42XJ₄(X)=X−14X²+56X³−84X⁴+42X⁵`. Then

```
F₄=⟨g,h⟩,       F₅=⟨g,h,Ch⟩,        Ae_terminal=0,
g²=γg+Q(C)h,    Q(ξ)≠0,              e_terminal=H(c)+δg+L(c)h.
```

Here `F_j` is the true zero-profile grade-j space. A row with g=h=0 integrates exactly inputs of degree **at most four**. Let I denote the zero-based polynomial primitive. In particular the actual vector `A N(c)−I N(c)` is in F₅ for deg N≤4, and is in F₄ for deg N≤3. Also g is in F₃ and Ag in F₄. These are the only forward grades below.

The terminal clock 1 is unique: at a nonterminal clock-one row the terminal profile would require an additional exterior h-head there (ξ, q, and τ differ from 1). Evaluating the terminal profile at the fixed head τ gives `L(τ)=0`; at q it shows L is nonzero. Thus write

```
L(X)=ℓ(X−τ),       F(X)=H(X)/(X−τ),       s_y=ℓ h_y,
s_q=−F(q).
```

At the first true nonzero clock ξ the value of g is γ and h=0, so `δ=−H(ξ)/γ`. At off ξ the profile and the quadratic defect relation permit exactly two nonzero g values, γ and g′, and give

```
h_i=g_i(g_i−γ)/Q(ξ) at ξ,       J=g′/Q(ξ),       γℓ J=F(ξ).
```

There is no zero g row at ξ, as its h would also be zero and H(ξ) is nonzero. The exact invariant clock-block census gives the usual six ordinary active Lobatto rows (one per fixed label, with g=h=0), two same-g opposite-weight active core rows, one alternate-g core ghost, and one head ghost each at q and τ. In particular the ghost τ can share the numerical clock of its regular row but not its defect values. Only the original actual tableau is used.

For clarity, the exact reflected input is the signed row `D=GA/[(1−ξ)³/6]`, with G the genuine nonzero compensated reflected cubic. It kills E₅, is nonzero at each of the three ghosts, and has zero true terminal column. The late active dirty is physical stage 10; the last three regular interior rows are stages 7, 8, 9, reflected coordinates R,W,U, respectively. Write X for the remaining reflected regular interior and x=1−X for its numerical clock. By the established reflected equations, any ghost or early active dirty located after x must have reflected numerical clock

```
Z=(10RU²−25RUW+10RW²+U²W+UW²)/(6(U−W)²).
```

The fixed-core two-off replay verifies that Z is not a fixed Lobatto label. Thus τ cannot be late. At most one of q and the early core events can be late: distinct labels cannot both equal 1−Z, and both early physical core values cannot follow x, since the first nonzero numerical row (which precedes x) is at ξ. In the all-early chart x is stage 6, and otherwise it is stage 5. The first changed ξ cannot precede a nonzero head: on inclusive donors at only 0 and ξ all nonzero g values are γ by C(2) and the definition of g. When the first head a is nonzero and is before that change, C(2) and the cubic read at a give

```
h_a=ξ² a³/[36(a−ξ)].
```

The anchored cubic `y(y−ξ)(y−a)`, with all inclusive donors before and at the first change among its roots, then gives the paid local gate

```
αJ=a−ξ/2,          α h_a=a³(a−2ξ)/12.               (B)
```

Indeed its residual is in F₄; the first ξ reads the g coefficient and a reads its h coefficient `−I N(a)/h_a`. At the changed row, cancelling `g′−γ≠0` gives (B). In all uses of (B) the first head is nonzero.

## 2. One late event: both possibilities excluded

If q is late, τ must occur before the first changed ξ. If τ=0 or τ=x, the effective inclusive clock donors at x are contained in `{0,ξ,x}`. More generally a clean C(5) row with x≠0 cannot have effective donors in `{0,a,x}`: the anchored cubic and its X multiple would have zero primitive at x, requiring `2a=x` and `5a=3x`. Thus τ is nonzero and distinct from x. The honest degree-four polynomial on `{0,ξ,τ,x}` now has zero primitive at x, forcing

```
ξ=x(5τ−3x)/[5(2τ−x)].
```

The degree-three cardinals at x give the aggregate taps

```
S_τ=x³(2ξ−x)/[12τ(τ−ξ)(τ−x)],
S_ξ=x³(2τ−x)/[12ξ(ξ−τ)(ξ−x)].
```

There are two prior core values. Combining `Ag(x)=Ah(x)=0` gives `S_τ h_τ=γ S_ξ J` without dividing by a tap. Apply (B) with a=τ. The required zero
`τ³(τ−2ξ)S_τ/12−(τ−ξ/2)γ S_ξ` factors after substitution as

```
x⁴ (10τ²−12τx+3x²)²/[720(2x−5τ)(x−2τ)(x−τ)].
```

All displayed fixed denominators and auxiliary τ,ξ,x differences are guarded; the fixed Radau numerator is nonzero.

If a core event is late, the only ξ donor at x has g=γ; its tap is zero by Ag(x)=0. If τ=0 or x, the effective donor set `{0,q,x}` is too small by the preceding anchored cubic argument. Otherwise both distinct nonzero heads a,b (equal to q,τ in one order) precede x. Put `P(y)=y(y−a)(y−b)`. The true grade-three marked input `P(c)−P(ξ)g/γ` is identically zero on the inclusive prefix through the second head. Its residual after A and subtraction of IP lies in F₄. Hence at both heads IP is a common multiple of h. At x, the ξ tap is zero, the origin gives zero, and Ah(x)=0 kills the combined head contributions to `A IP(c)`. Therefore `I²P(x)=d_x IP(x)`, where d_x is the true diagonal. C(5) also gives `IP(x)=d_x P(x)` and `I[yP](x)=x d_x P(x)`; these use inputs of degrees three and four. Since `I²P(x)=x IP(x)−I[yP](x)`, it follows that `d_x² P(x)=0`. The other clocks are distinct from x, so d_x=0. The two zero primitives give `a+b=6x/5, ab=3x²/10`, forcing the same forbidden fixed Radau root τ. No least-stage or positivity assumption was used to drop either tap.

## 3. All-early: genuine suffix aggregate

Set V=1−ξ, `Λ(Y)=(Y−1)H(Y)`, and `Q_off(Y)=(Y−(1−ξ))(Y−(1−q))=Y²−S Y+P`. The eight distinct numerical labels are the roots of Λ Q_off after reflection. The D aggregates annihilate all polynomials through degree five; by the dimension-two barycentric formula their numerator at a reflected label y is affine, over `(Λ Q_off)′(y)`. Its constant term vanishes because the only row at y=0 is the true terminal and D is zero there. Its linear coefficient is nonzero by the live q entry. For any **singleton regular** s among U,W,R, this gives

```
E_s Q_off(s)=constant,    E_s=b_s Λ′(s) k_s/s,
D_s/b_s=k_s/[V(V−U)].
```

The exact k_s and fixed mass-times-derivative are those in the repaired suffix and fixed-core two-off packets. The three k denominator guards and E nonvanishing are checked. Since ξ is off, V differs from every fixed interior. If τ coincides with one of U,W,R (after reflection), **omit precisely that label**, which has a separate ghost at it. At either of the remaining two singleton labels s,z, comparison gives

```
P=α S+β,
α=(E_z z−E_s s)/(E_z−E_s),  β=(E_s s²−E_z z²)/(E_z−E_s).
```

All fixed denominator guards are audited. This does not identify an individual entry of D with an aggregate at a repeated label.

## 4. All-early: the true absent-column read

Write `N_0(y)=y(y−ξ)(y−q)(y−τ)` and `p_v=I N_0(v)`. Before x these roots cover all actual inclusive donor clocks, even if τ=0. Thus `A N_0(c)=0` on that prefix, and the F₅ residual has form `κg+ℓ_N(c)h` with ℓ_N affine. At the first ξ, `κ=−p_ξ/γ`; at each of q,τ, `ℓ_N(v)=−p_v/h_v`. At the changed ξ use `h=g(g−γ)/Q(ξ)`, cancel `g′−γ`, and apply the terminal equation `γℓ J=F(ξ)`. This yields

```
F(ξ) (ℓ_N(ξ)/ℓ)=p_ξ.                                (A)
```

### τ=0 or τ=x: pinned quadratic, no split tap

All three suffix labels are singleton, so the extra linear comparison at R versus U pins S,P. The original two off labels are the roots of the monic quadratic `T²−(2−S)T+(1−S+P)`; at a root t=ξ put `q=(2−S)−t`. If τ=0, p_τ=0 immediately; if τ=x, N₀ also vanishes on all *inclusive* donors at x and C(5) gives p_τ=0. Since h_τ≠0 this gives ℓ_N(τ)=0 in either case. Interpolate with the q read and use `s_q=−H(q)/(q−τ)`. Then (A) implies

```
p_ξ H(q) − p_q H(ξ)=0.
```

The quadratic and this polynomial are coprime in all 48 ordered fixed assignments modulo 419 and 719. There is no appeal to an unpaid grade-five input or to splitting a tap at the common label.

### τ is a different interior from x: Möbius and exact factors

Let r,s be the original clocks of the two singleton reflected suffix labels. Put `c_0=1−α, d_0=2α+β−1`, so `ξq=c_0(ξ+q)+d_0`. The checks give `ρ=d_0+c_0²≠0`. For t=ξ use formal polynomial variables

```
D₀=t−c₀,  B=c₀t+d₀,  q=B/D₀,  T=B−tD₀,   Bτ=B−τD₀,
K=(t−r)(t−s),   C_t=42(t−x),     C_q=42(c₀−r)(c₀−s)(B−xD₀).
```

The same linear comparison is satisfied by the pair of fixed labels r,s (both singleton evaluations of Q_off are zero there). Thus the Möbius map interchanges r,s exactly. This proves `F(t)=t K C_t`, `F(q)=B K C_q/D₀⁴`, since `F(y)=42y(y−x)(y−r)(y−s)`. For the true degree-four tap at the single earlier τ head in the inclusive donor set `{0,t,q,τ,x}` define

```
P_X=10tB−5(tD₀+B)x+3x²D₀,      n=−x³ P_X/60,
v=τ(τ−t)(τD₀−B)(τ−x),          m=I F(x),
s_* = m v−F(τ)n.
```

The τ tap is n/v. At x, Ag=Ah=0 gives `S_q s_q+S_τ s_τ=S_t F(t)` by aggregating the two true changed-core values and using the terminal equation. Also the genuine F input (degree four) integrates exactly, F(0)=F(x)=0, and `s_q=−F(q)`. Consequently `S_τ(s_τ+F(τ))=m`. The fixed guard m≠0 excludes n=0 and gives `s_τ=s_*/n`. None of the other taps is divided out.

The degree of s_* is at most two; it vanishes at t=r,s because the Möbius map swaps r,s and F is then zero at the four other cardinal nodes 0,t,q,x. Exact degree-four polynomial interpolation there gives `m v=F(τ)n`. Thus `s_*=k K` for a fixed scalar k (also a checked unit), and `s_τ=kK/n`. These two exact roots are proved before reduction.

For the p primitives define

```
P_t=10τB−5(τD₀+B)t+3t²D₀,
P_q=10τtD₀²−5(τ+t)BD₀+3B²,
P_τ=10tB−5(tD₀+B)τ+3τ²D₀.
```

Then `p_t=−t³P_t/(60D₀)`, `p_q=−B³P_q/(60D₀⁵)`, and `p_τ=−τ³P_τ/(60D₀)`. Clearing the two nonzero h-head reads and their distinct label difference in (A), and cancelling the harmless factor `t B K²/(60D₀⁶ n)`, gives the polynomial

```
A_num = −k D₀ C_t B² P_q (t−τ)
        +τ³ C_t P_τ C_q T n
        +k t² P_t C_q Bτ.
```

It is divisible **in characteristic zero** by `T(t−τ)Bτ`. For T: its two roots are simple by ρ≠0; D₀≠0 there, q=t, `P_q=D₀ P_t` and `C_q=D₀³ C_t), so the first and last terms cancel. The C relation also holds at any potential overlap with K by the exact swap formula and the nontriviality of r,s (a fixed point cannot be r or s). At t=τ: v=0, `kK=−F(τ)n`, and `P_t=P_τ`; the remaining two terms cancel using F(τ)=τ K C_t. At Bτ=0: q=τ, v=0, `kK=−F(τ)n`, `P_q=D₀ P_τ`, and `F(τ)=τ K C_q/D₀³); the other two terms cancel. The roots of these factors are disjoint by `T(τ)≠0` and ρ≠0; `Bτ` has degree one since `τ−c₀≠0`. All divisions are guarded fixed scalars, and no factor vanishes at the actual off pair. The reduced polynomial `A=A_num/[T(t−τ)Bτ]` has degree at most four.

If the first changed ξ occurs **before the second head**, (B) and `γℓ J=F(t)` give `a³(a−2t)F(t)=t³(2a−t)s_a` for the first head a. For a=q or τ, respectively, this yields the two polynomials

```
B_q = D₀ B²(B−2tD₀) C_t + t²(2B−tD₀) C_q,      degree ≤6;
B_τ = τ³(τ−2t) C_t n − k t²(2τ−t),              degree ≤4.
```

If it occurs **after both heads**, the same marked cubic `y(y−q)(y−τ)−P(t)g/γ` as in the late core case vanishes on the prefix through both heads (where here `P(y)=y(y−q)(y−τ)`). Thus the two head primitive reads are proportional to their h values. This gives `q³(q−2τ)s_τ+τ³(2q−τ)s_q=0`, equivalently

```
B_after=k D₀ B²(B−2τD₀)−τ³(2B−τD₀) C_q n,      degree ≤4.
```

The finite gate checks exact degrees 4,6,4,4 after the proved factor divisions and coprimality of A with each B across all 72 fixed assignments.

## 5. Verification boundary

`DIRKOrderTenOffCoreTwoOffScalar.lean` verifies the Radau gates and the pinned/Möbius scalar tests modulo 419. `check-dirk10-active-off-core-two-off-unique-terminal.py` independently verifies them at 419 and 719. (587 is not a universal good residue for these tests; a few accidental modular collisions remain there.) The underlying physical rank band, chronology/tableau bridge, interpolation, factor exactness, and good reduction are mathematical, not a complete native `HasOrder` theorem.

Use the splitting field of the fixed-clock quartic and a prime over 419; its four distinct roots remain distinct and all allowed orderings were checked. The remaining divisions use only fixed denominators shown to be units. Exact normalized degrees and coprimality give nonzero characteristic-zero resultants in the Möbius case. The pinned monic quadratic is integral and a common characteristic-zero root would give a common residue root in some algebraic residue extension, ruled out by polynomial gcd. No integrality, reality or prime-field reduction for arbitrary tableau coefficients is assumed. This excludes only the terminal-unique active off-core chart described above and does not improve the unrestricted 11–12 numerical stage interval.
