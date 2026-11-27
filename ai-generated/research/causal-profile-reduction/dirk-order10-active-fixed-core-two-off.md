# Active nonconstant DIRK10/11: fixed cubic-core clock and exactly two off heads

Work over a characteristic-zero field with an actual eleven-stage lower triangular tableau of rooted order ten. Assume the physically nonzero cubic defect `g=Ac²−c³/3` has a single numerical clock ξ, its nonzero values are not all equal, and some `b_i g_i≠0`. This note excludes the precise chart in which **ξ is a fixed interior Lobatto clock and both exterior h-head clocks are off-Lobatto**, where `h=(A−ξ/2)g`. It treats the all-early and one-late chronologies of this chart. A dirty clock that is itself off-Lobatto, other active charts, zero-weight one-local charts, and the unconditional 11–12 stage interval are separate.

## 1. Paid physical skeleton and notation

The valid one-local structure gives `F₄=⟨g,h⟩`, `F₅=⟨g,h,Ch⟩`, `Ah=(m+nC)h`, `Ae_t=0`, `g_t=h_t=0`, and `e_t=H(c)+δg+L(c)h`, where `H(X)=42XJ₄(X)` is the fixed terminal Jacobi polynomial. In the nonconstant case `g²=γg+Q(C)h`, `γ=ξ³/6`, with `Q(ξ)≠0` and exactly two exterior h-heads (distinct from ξ). At ξ we have `h=g(g−γ)/Q(ξ)` pointwise. We use `C(5)` only for actual inputs of degree at most four. The nonzero off heads force L≠0. Since ξ is a fixed interior, the first true ξ has g=γ,h=0 and gives δ=0; some changed g has nonzero h, so `L(ξ)=0`. Write `L(X)=ℓ(X−ξ)` and `F(X)=H(X)/(X−ξ)`. Both exterior heads are actual zero-weight singletons by the known invariant clock census; their head values are `s_v:=ℓ h_v=−F(v)`. There is no earlier clock-one row: it would have exterior h nonzero, a third head. Thus clock one is the sole true terminal.

Specialize the exact signed ghost skeleton from the repaired reflected-suffix analysis. There are six regular Lobatto active rows with `g=h=0` and their fixed weights, two equal-g/h active core rows of opposite weights, one different-g core ghost, and two exterior h ghosts. For completeness the core count follows because g is supported at ξ, both off heads are ghosts, and the paid h² equation then gives the fourth signed g-moment on ξ using `h=g(g−γ)/Q(ξ)`. Four core physical rows then must be one ordinary clean (its fixed mass is nonzero), two opposite active with the same value of g, and one alternate g ghost; the moments through g⁴ kill each nonzero g class by nodal interpolation. The E₆ excess is on ξ by the genuine nonzero `G∥βg`, and a one-local argument gives μ exactly Lobatto ordinary quadrature. In particular all fixed regular interiors actually occur. These are the physical rows of the original tableau, not a transformed weighted-transpose method.

Let `Y=1−C`, `V=1−ξ`, and define `D=GA/(V³/6)`, the signed sum of the two active core A rows. It annihilates the actual E₅ and has nonzero entries at all three ghosts, as proved in the repaired suffix note by the g,h,Ch constraints and the impossibility of folding if `GA∥G`. Let `U,W,R,X` be the reflected coordinates of the four ordinary interior regular rows in reverse physical order. Their set is the four fixed interior roots; `V≠U`. The actual later active dirty is physical stage 10, terminal 11, and the last three regular interior rows are stages 7,8,9, with reflected coordinates R,W,U respectively. Any ghost *after* the first regular interior x=`1−X`, or any first active dirty there, must have reflected numerical label

```
Z=[10 R U²−25 R U W+10 R W²+U²W+UW²]/[6(U−W)²].       (1)
```

At most one ghost can be late. These are **true marked-row** calculations using D(2), the reflected cubic identity and its compensated quartic/quintic defects, valid even when the regular ξ clock shares a reflected label with the dirty pair; the details are in the prior repaired note. The finite check gives `Z∉{0,1,four interior roots}` on all 24 orders mod419. Thus neither the early active dirty nor the alternate-g ξ ghost can be late. The only late event could be one of the off heads; otherwise all four non-origin prefix stages before x are precisely both dirty-core values and the two exterior ghosts.

## 2. Exactly one late head

Physical stages 2,3,4,5,6 are then: first ξ value γ, early off head a, changed ξ value g′, first regular interior x, late off head b. The first change at ξ cannot precede another nonzero clock, since the actual inclusive `{0,ξ}` prefix has only γ. The effective inclusive donors at x are among `{0,ξ,a,x}`. If x=ξ, the degree-three nodal polynomial on `{0,a,x}` and its degree-four X multiple require `2a=x` and `5a=3x`, impossible. Thus x≠ξ. The **degree-four** anchored product gives

```
I [X(X−ξ)(X−a)(X−x)](x)=0,
a=x(5ξ−3x)/[5(2ξ−x)].
```

The four-node cardinals (degree three) yield actual aggregate taps

```
S_a=x³(2ξ−x)/[12a(a−ξ)(a−x)],
S_ξ=x³(2a−x)/[12ξ(ξ−a)(ξ−x)].
```

At a the first-head h is `h_a=ξ²a³/[36(a−ξ)]`, and the global cubic-input defect is `(3ξ/2)g+αh`, `α=3(a−ξ)(a−2ξ)/ξ²`. Put `J=g′/Q(ξ)`. At the first changed ξ, genuine C(4) with donors only `{0,ξ,a}` gives `αJ=a−ξ/2`, using the exact formula for core h and cancelling the changed g difference. At x, true `Ag=Ah=0` gives `γ S_ξ J=S_a h_a`. Combining, without any division by either tap, requires

```
αS_a h_a−(a−ξ/2) γ S_ξ=0.
```

Substituting the calculated a and taps gives exactly

```
x⁴ (10ξ²−12ξx+3x²)² / [720 (2x−5ξ)(x−2ξ)(x−ξ)].
```

The needed divisors/clock differences and the fixed Radau numerator are nonzero; the finite module also checks the combined expression directly for the 12 ordered distinct fixed ξ,x. This excludes the one-late chart, without needing the numeric value of b after (1) places it late.

## 3. All-early: the useful exact aggregate relation

The first regular x is physical stage 6. The front is origin, first core ξ, the first head a, then the second head b and the changed core ξ in either order. The clock census imposes precisely these rows, though the early active/ghost choice within the two core values is immaterial below. Both heads already occur before x and `g′≠γ` occurs by x. The only actual uses of primitive quadrature below are through degree four.

Set `a#=1−a`, `b#=1−b`, `Qoff(Y)=(Y−a#)(Y−b#)=Y²−S Y+P`, and `Λ(Y)=(Y−1)H(Y)`. These are the actual eight distinct reflected labels from `Λ·Qoff`. Because D annihilates clock polynomials through degree five, its aggregate mass at any reflected numerical label y has the form `(σ₀+σ₁y)/(ΛQoff)'(y)`. Indeed the two barycentric sequences with numerators 1,y both kill degrees through five and exhaust the dimension two. At y=0 the terminal is uniquely present and D_t=0, so `σ₀=0`. The remaining σ is nonzero by the live D off ghosts. Thus at a **singleton fixed ordinary interior** y,

```
E_y Qoff(y)=σ V(V−U),       E_y=b_y Λ′(y) k_y/y.
```

Here `D_y/b_y=k_y/[V(V−U)]` for the three suffix labels U,W,R, from the correctly paid reflected equations. The exact fixed quantity `b_y Λ′(y)=∫₀¹ Λ(Y)/(Y−y)` follows from the fixed Lobatto rule's degree-five cardinal. The k factors are the known nonzero suffix formulas

```
k_U=−U³/6,
k_W=W³(2U−W)/[6(U−2W)],
k_R=R³(2U−W)(3R²−5R(U+W)+10UW)
      /[6(4RU²−13RUW+4RW²+U²W+UW²)].
```

The quoted formulas and all denominators of these fixed ratios are exactly checked. U is a singleton because `V≠U`. If V is W or R, use the other singleton z of W,R. If V=X, use z=W and then R for the extra singleton. Comparison at U and z gives

```
P=α₀ S+β₀,
α₀=(E_z z−E_U U)/(E_z−E_U),     β₀=(E_U U²−E_z z²)/(E_z−E_U).
```

**No additional affine constraint from the first regular row's diagonal is used.** In particular the tempting row-6 ordinary comparison from the same compensated quadrature is redundant in the scalar experiments; it is not counted as a new equation. The proof uses the genuine changed-core prefix equations instead.

## 4. Prefix equations used in both all-early cases

Let `N(y)=y(y−ξ)(y−a)(y−b)`, `p_v=I N(v)`. The actual residual `A N(c)−I N(c)` is in F₅ (input degree four). Before x all inclusive donor clocks are 0,ξ,a,b, so `AN=0` there. With affine coefficient `ℓ_N` of h, the earliest ξ read gives its g coefficient `−p_ξ/γ`, and the first two heads give `ℓ_N(a)=−p_a/h_a`, `ℓ_N(b)=−p_b/h_b`. At the first change `g′≠γ`, the absent-column read cancels the changed value to give

```
γ ℓ_N(ξ) J=p_ξ,       J=g′/Q(ξ).
```

First-head h and α are as in §2; `s_a=ℓ h_a=−F(a)`, `s_b=−F(b)`. Denote by `Lnum,Lden` the numerator and denominator of the affine interpolation of `−p_a/s_a,−p_b/s_b` at ξ:

```
Lnum=−p_a s_b (b−ξ)−p_b s_a(ξ−a),
Lden=s_a s_b (b−a),        Lnum/Lden=ℓ_N(ξ)/ℓ.
```

If change occurs **before b**, `αJ=a−ξ/2`, as in §2. Combine this with the absent column and the true `αh_a=a³(a−2ξ)/12`, without requiring α nonzero, to get

```
ξ³(2a−ξ)s_a Lnum − p_ξ a³(a−2ξ) Lden=0.             (Babs)
```

If change occurs **after b**, all ξ rows available at b have only γ, so degree-three `y(y−a)(y−b)` at b gives

```
a³(a−2b)s_b+b³(2a−b)s_a=0.                          (Aphase)
```

These deductions retain the true diagonal, and there is no division by a late dirty stage weight or one of the earlier two ξ taps.

### Earliest regular x shares ξ: V=X

All three U,W,R are singleton. Comparing E_R Qoff(R) with E_U Qoff(U) gives a second linear equation, so the check guards the resulting two fixed divisions for S,P. The first physical off label a is now a root of the monic pinned polynomial

```
a²−(2−S)a+(1−S+P)=0,      b=(2−S)−a.
```

If changed before b, (Babs) excludes either possible a. If changed after b, (Aphase) excludes either. These are coprimality tests over the residue algebraic closure (not tests only of F419 points). There is no need to solve for x's individual diagonal: it shares a numerical clock with two early ξ rows, and forcing it from aggregate C(5) would be invalid. The corresponding nodal quartic integral was not used as an extra scalar.

### Earliest regular x distinct from ξ: V=W or R

Only one singleton comparison is needed. In the original variables it reads `ab=c_0(a+b)+d_0` where `c_0=1−α₀`, `d_0=2α₀+β₀−1`. The check gives `ρ=d_0+c_0²≠0`, so the actual b is the Möbius function

```
b=B/D0,      D0=a−c_0,      B=c_0 a+d_0,    T=B−aD0.
```

In particular `D0≠0`; `T≠0` since a,b distinct. Introduce the polynomial `C_ξ=F(y)/y=42J₄(y)/(y−ξ)`, and set `C_a=C_ξ(a)`, `C_b=D0³ C_ξ(B/D0)`. The s values are `−a C_a`, `−B C_b/D0⁴`. They are nonzero because actual heads are off. Use the symbols

```
P_A = 10ξB−5(ξD0+B)a+3a²D0,
P_B = 10ξ a D0²−5(ξ+a)B D0+3B²,
P_V = 10aB−5(aD0+B)ξ+3ξ²D0,
M = [a² P_A C_b(B−ξD0)+B² P_B C_a(ξ−a)D0]/T,
n = −x³[10aB−5(aD0+B)x+3x²D0]/60,
v = ξ(ξ−x)(ξ−a)(ξD0−B),
b_s = −I F(x) v+F(ξ)n.
```

For example `p_a=−a³ P_A/(60D0)`, `p_b=−B³ P_B/(60D0⁵)`, `p_ξ=−ξ³ P_V/(60D0)`. The true degree-four ξ cardinal at x gives `S_ξ=n/v`; both actual off heads and x are distinct from ξ, so v≠0. The scaled head sum is `S_a s_a+S_b s_b=b_s/v`, since the degree-four input F integrates exactly at x, `F(x)=F(0)=0`, and the ξ aggregate contributes `S_ξ F(ξ)`. This avoids division by any off-head tap. The affine interpolation `ℓ_N(ξ)/ℓ` is `−M/(60D0 C_a C_b)`. By `Ag(x)=Ah(x)=0` the actual head sum also equals `ℓ γ S_ξ J`: aggregate the two unequal early core values and note their h difference. No division by Sξ is needed.

There are now exactly two required polynomials per timing:

```
before:   a²(a−2ξ)b_s+ξ³(2a−ξ) C_a n = 0,
          (2a−ξ)M+a²(a−2ξ) P_V C_b = 0;

after:    [a²(aD0−2B) C_b+B²(2aD0−B) C_a D0]/T = 0,
          M b_s−ξ³ P_V n C_a C_b = 0.
```

The first before equation combines `Ah(x)` with `αJ=a−ξ/2`; the second is (Babs). The first after is (Aphase) cleared with `D0⁵/(aB T)`; the second combines the absent-column identity with the actual head sum. The signs follow from `ℓ_N(ξ)/ℓ=−M/(60D0 C_a C_b)` and `p_ξ=−ξ³P_V/(60D0)`.

**Only the following exact factors are divided out.** The two T divisions above are polynomial: its two roots are simple by `ρ≠0`; there D0≠0, b=a, `C_b=D0³ C_a`, `P_B=D0P_A`, so the opposite numerator contributions cancel. Let r,s be the other two fixed interior numerical clocks not ξ,x (ordinary singleton reflected labels U,z). The Möbius map interchanges r,s exactly: putting these two fixed numbers in place of a,b makes both `Qoff(U)` and `Qoff(z)` zero and hence satisfies precisely the defining linear comparison. At either r,s we therefore have `C_a=C_b=0`, with D0,T nonzero. Both before and after polynomials vanish at them. For the before pair, at a=ξ the fixed guard gives `T≠0`, then `v=0`, `F(ξ)=ξ C_a`, and `M=ξ²P_A C_b`, `P_A=P_V`; both polynomials vanish there as well. These are simple fixed factors. Divide the after pair by `(a−r)(a−s)` and the before pair by `(a−r)(a−s)(a−ξ)`. All these factors are nonzero at the actual off a. Their reduced degree bounds are after 4,8 and before 3,6; the residue check shows the degrees are exact and both reduced pairs are coprime on all 48 orders for V=W,R.

## 5. Verification boundary

`DIRKOrderTenFixedCoreTwoOffScalar.lean` checks the fixed late-location guard, the true forward one-late test, and all 72 fixed assignments of the all-early chart (24 cases V=X and 48 V=W/R) modulo 419. It reuses the corrected reflected fixed polynomial data and the earlier portable finite coefficient operations. The independent replays evaluate the one-late guard and all-early normalized polynomial divisions and resultants by exact residue arithmetic, with the all-early calculation also passing modulo 587.

For characteristic zero use only the splitting field of the fixed-clock quartic at a prime over 419. Its fixed roots remain distinct. All fixed-node denominator guards and exact normalized degrees are verified, so the coprime residue pairs give nonzero characteristic-zero resultants. In the pinned case the monic quadratic is integral over that localization, so its prospective root could only yield a common residue root in an algebraic extension, which is also excluded. No actual tableau coefficient, off clock, or defect amplitude is assumed to reduce into the prime field before these guards. The actual hypotheses-to-scalar bridge above is mathematical, not a full native `HasOrder` theorem. This excludes the specified fixed-core two-off chart only and does not increase the unrestricted lower bound.
