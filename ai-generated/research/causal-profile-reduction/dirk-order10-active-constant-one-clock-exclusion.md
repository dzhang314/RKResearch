# Active constant DIRK10/11 with one physical cubic-defect clock

Work with an actual eleven-stage, rooted-order-ten lower triangular tableau over a characteristic-zero field. Let `g=Ac²−c³/3`. Assume it is physically nonzero at only one numerical clock ξ, its nonzero values are all the same, and at least one `b_i g_i≠0`. **This chart is impossible.** The argument covers the shared terminal-polynomial root at ξ or away from it, and the non-Lobatto ordinary quadrature branch. No statement is made about invisible cubic defects, multiple physical dirty clocks, or the unrestricted 11–12 stage interval.

The established one-clock data are used as actual grade identities:

```
γ=ξ³/6,                  g_i∈{0,γ},
h=(A−ξ/2)g,              Ah=(m+nC)h,
F₄=⟨g,h⟩,              F₅=⟨g,h,Ch⟩,
U₆=⟨g,h,Ch,C²h⟩,        F₆=U₆⊕K I H(c),
dim E₅=9,               E₆^⊥=K G=K (βg),
e_t=H(c)+δg+L(c)h,       H(X)=42 X J₄(X), deg L≤1.
```

Here `E_j,F_j` are the true full/zero-profile spaces through grade j; I is the zero-based primitive; `G=β(1−C)^2A−β(1−C)^3/3` is the actual compensated reflected cubic. The true origin is a zero row, the actual terminal t has clock one and weight `1/30`, and `Ae_t=0`. The latest active nonunit row has `G_i=b_i(1−c_i)^3/6≠0`, so it is dirty, and ξ is distinct from zero and one. The first nonzero numerical clock is ξ, its g value is γ and h value zero. The fixed six-node Lobatto measure is ν, with roots of `J₄=X^4−2X^3+4X^2/3−X/3+1/42` as its four interior nodes. Its endpoint weights are `1/30`, all six fixed weights are nonzero, and its ordinary moments are exact through degree nine.

The case L=0 is already excluded without using an erroneous quintic: every exterior numerical clock would be fixed, contrary to the genuine first-three-exterior paired cut on fixed nonzero clocks. Assume L≠0 below. There are at least two physical dirty rows by βg=0 and active g. Their number n is at most three: every actual E₆ value restricted to a dirty row is affine in h because c and g are constant, and `E₆` has only one missing dimension. If `L(ξ)≠0`, the terminal profile makes all dirty h values zero (use its first dirty read), so n=2. Always the signed total dirty quadrature mass is zero, since g=γ on them; also (sum_{g_i≠0} b_i h_i=0) by the paid βgh test.

## 1. If the ordinary aggregate is Lobatto, the paid DA gate applies

Write μ for ordinary clock aggregate. Assume μ=ν. The following is an actual physical census and does not assume that dirty h is always zero.

- At any noncore exterior clock not a root of L, the terminal profile fixes h on all nonterminal rows. Equal `(c,g,h)` gives identical E₆ columns of evaluations on the two rows, which is impossible for two exterior rows: their contrast would be in `E₆⊥=K(βg)`, supported on dirty rows. Thus every off-Lobatto exterior label is a singleton (with h≠0), and its weight is zero by μ=ν and the zero dirty aggregate, even if it shares ξ. A nonterminal clock-one row is likewise a unique possible h-head, separate from the ordinary terminal, and has weight zero. If `L(1)=0`, it cannot occur.
- A fixed ordinary clock distinct from ξ, one, and a shared root of H,L has just one h=0 exterior row, carrying its fixed mass. A shared fixed root `τ≠ξ` can have at most two exterior rows, as E₆ there has values affine in h and projects onto the full exterior coordinates. All other exterior h contributions are from zero-weight ghosts; dirty h=0 in this case. Hence the paid βh and βh² reads make the τ h mean and second moment zero. Since the τ mass is nonzero, this yields one regular h=0 row carrying that mass and at most one h≠0 ghost. Indeed, with two h values, their interpolating quadratic gives their product times the nonzero aggregate as zero, and the h mean kills the nonzero class.
- If ξ is off and `L(ξ)=0`, no exterior row at ξ is possible by the terminal profile. If ξ fixed and `L(ξ)=0`, the ξ block has at most four physical rows, since its E₆ values are affine in 1,g,h and the one missing dimension is there. Its nonzero fixed mass forces an exterior row. If n=2 the dirty h values are both zero by βgh, opposite active weights, and the first dirty h=0. At ξ the identical first-and-second h-moment argument on the exterior rows gives one clean row and at most one h ghost. If n=3, there is exactly one exterior ξ row, with fixed mass and h=0 by βh and βgh. If ξ fixed with `L(ξ)≠0`, its n=2 dirty h values are zero and its h=0 exterior row is unique.
- For n=3 the dirty rows are all at a root of L (there is no separate shared fixed root). After the preceding exterior census, all weighted exterior h and h² contributions vanish. The dirty h classes thus have zero signed moment at 1,h,h²; interpolation at their at most three values kills each class mass. With active g, exactly two dirty rows are an opposite nonzero weight pair with equal h. The third is a zero-weight alternate-h dirty row. All three cannot share h, since three identical E₆ rows would give two missing dimensions.

In all cases there are six regular active rows with `g=h=0` at the six fixed clocks, an opposite-weight equal-profile active dirty pair, and three ghosts. If n=2 the ghosts are three exterior h-heads at distinct labels. If n=3 the ghosts are two exterior h-heads at distinct labels other than ξ, and one alternate-h dirty at ξ. A regular ξ or a regular head clock can repeat a ghost label but is a different physical row.

For the compensated row `D=GA/[(1−ξ)^3/6]`, we have `D∈ E₅⊥`, `D_t=0`, and `D=Σ_(i active dirty) b_iA_{i,*}` by the latest active pivot and `G∥βg`. It is live at all three ghosts: in the n=2 case Dh=DCh=0 gives two moment equations on the three `D_i h_i`; in the n=3 case Dg=0 makes the core h contribution exactly `(h_d−h_*)D_d` at ξ, where d is the alternate ghost and `h_*` is the common active h. The other two are again `D_i h_i`. Distinct three clocks and nonzero h differences imply that one zero forces all three to vanish. Then Dg and polynomial moments through degree five show that D is proportional to G: its remaining regular six entries vanish by the fixed Vandermonde. This would make the two active rows' equality subspace A-invariant and closed under coordinate products. The later row could then be folded into the earlier one (merge the later column into the earlier for each retained row and merge their weights), preserving lower triangularity and all trees, contrary to the eleven-stage minimum.

This is exactly the paid signed suffix used by the uniform DA obstruction. In the n=3 case the earlier active dirty need not be the first nonzero row, but the repaired B₄ chronology still applies. In its column i set `s_i=b_i V/2−D_i`, `V=1−ξ`. The three reflected regular moments are `V s_i,V²s_i,(V³−K)s_i`, `K=V(V−U)(V−U/2)`. If its only later regular interior labels were U,W, the vanishing polynomial `Y(Y−U)(Y−W)` on those donors forces `s_i=0`, as the leftover coefficient is `V(V−U)(U/2−W)≠0`. Then `D_i+D_j=0` for the later dirty j; Dg=0 kills the alternate ghost, impossible. The same three-moment argument for a ghost column already applies (its weight and G component are zero). Thus the last three regular interiors are actual columns 7–9 and the late active dirty is 10. The entire paid DA three-column proof, including numerical clock coincidences with an earlier ghost, applies. This excludes μ=ν for constant active g, with no extra `L(ξ)≠0` hypothesis.

## 2. A non-Lobatto aggregate can only leave the shared zero chart

Let `Δ=μ−ν`. It annihilates ordinary degree ≤9. Ordinary closure for a constant nonzero L or a pole not shared with H was proved by the terminal-debit argument. Thus a candidate here requires `L(X)=ℓ(X−τ)`, `H(τ)=0`. Put `F=H/(X−τ)`, a degree-four polynomial, and `s=ℓ h`. The fixed root is either zero or a fixed interior and `F(τ)≠0`. Use the correction

```
r = s + F(c) − F(1)e_t − F(ξ) g/γ .
```

When `τ≠ξ`, the terminal identity and the first dirty read show r supported only at τ and zero on all dirty rows. When `τ=ξ`, it is likewise supported there; its dirty restriction is s. In both cases `β r=ν(τ) F(τ)≠0`, since βh=βg=0, the terminal mass is known, and F vanishes at every other fixed node except one. In the n=3 case necessarily `τ=ξ` is an interior (otherwise `L(ξ)≠0` or the nonshared-pole theorem applies). Its dirty contribution to βr is zero by βgh=0, forcing a retained exterior row at τ. Removing the three mutually cancelling dirty rows leaves eight physical rows, including distinct fixed 0,τ,1 rows. There are at most five active off fixed labels; if five, the remaining rows have only one at clock 1, so Δ(1)=0. Thus the discrepancy has support at most ten, impossible unless Δ=0 by Vandermonde.

Now n=2, both dirty h=0 and r=0 on them. Also `β r^2=ν(τ) F(τ)^2`: expand the square; βh², βhF(c), and the dirty signed contributions vanish, and the only terminal-square term is exactly subtracted by its known weight. There are at most two exterior rows at τ by the affine h profile and G supported on dirty rows. If the τ row is unique, the two nonzero r moments force its mass `ν(τ)` and `h=0`. There must be at least one such row. There are at most two rows at clock one, with the true terminal supplying ν(1).

If `τ≠0`, let m,p in {1,2} be the counts at τ and clock one after dirty cancellation. There are nine retained rows, and at least one additional fixed origin distinct from both. At most `8−m−p` active off labels are left; among the six fixed discrepancy labels, at most `4+(m−1)+(p−1)` can be nonzero because either singleton has the prescribed mass. Thus support is at most ten, again impossible.

If τ=0, let m,p count the exterior rows at zero and one. At most `9−m−p` off labels are left, and at most `4+(m−1)+(p−1)` fixed discrepancy sites. The sum is eleven. Nonzero Δ forces *every* allowed site to be live and this count exact: the retained exterior rows other than the m,p have distinct off clocks and nonzero weights. If m=2, the actual origin has r=F(0), and the other zero-row r value differs (otherwise its E₆ signature would equal the origin's). That other weight is nonzero by Δ(0)≠0. Subtract `F(0)β r` from βr² to give `b_extra r_extra(r_extra−F(0))=0`, hence its r is zero and the origin has weight ν(0). If m=1 the origin already has that weight. At 1 the actual terminal always has ν(1); an extra is active iff present and has h by the terminal identity.

Therefore the only putative debris has two dirty active physical rows with opposite weights and zero h, the true origin and terminal each weighted `1/30`, and seven other distinct numerical **exterior** rows of nonzero weight, with

```
s=-F(c),       F(X)=42J₄(X),       F(1−X)=F(X).
```

Their clocks avoid all fixed interiors but may include one extra zero and/or one extra one. All seven s values are nonzero. Call these the generic rows in the rest of the note. The row `w=βh` is live on all seven and annihilates E₅ by true grade four plus five. Thus `G,w` span `E₅⊥`; `D` has nonzero w component or the preceding folding contradiction applies. D is live on all seven, forcing them before the late active dirty by triangularity. The first dirty is physical stage 2: before the first nonzero clock there can only be an origin row (an extra identical zero row with h=0 would contradict the exterior E₆ rank). Hence the true layout is origin 1, dirty 2, generic 3–9, dirty 10, terminal 11.

## 3. Paid debut equations at both ends

We now derive a necessary scalar system independently for the first three forward generic clocks and the first three reverse reflected generic clocks. Define `𝓡=CA−AC−A^2`. The true Volterra grade gives `𝓡 E_j⊂ F_{j+2}`; its literal diagonal is `-d_i^2`.

Forward, let a,b,u be the first three distinct **nonzero** generic clocks, in physical order. There are at least six nonzero generics. For `P(X)=X(X−a)(X−b)`, the actual column `v=P(c)−P(ξ)g/γ` vanishes strictly before the u row, even if a generic zero had intervened. Its `𝓡 v` is in F₅ and vanishes on that strict prefix. Read the first dirty row (g nonzero, h=0) and the two distinct live a,b rows to kill the g and affine h coefficients, so `𝓡 v=0`. At u the inclusive triangular read gives `-d_u^2 P(u)=0`, hence `d_u=0`. Thus `Av=0` through u. The residual `Av−IP(c)∈ F₄` shows that `IP/h` is the same at a,b,u. If an extra generic zero had preceded u, the latter read has `IP(0)=0,h≠0` there and would force `IP(a)=IP(b)=0`, impossible since these are `a³(2b−a)/12,b³(2a−b)/12`. Thus a,b,u are actually the first three generic rows, all nonzero.

Reverse, use Y=1−C. The reflected generic clock profile is again h=−F(Y)/ℓ. Here rank E₄=7 and e_t∉E₄ have short direct proofs from the seven actual generic profiles. For either a zero combination p(c)+a₀g+b₀h, or a hypothetical representation of e_t in that form with deg p≤4, its zero values on the seven distinct generic clocks imply p=(b₀/ℓ)F identically. The origin then gives b₀=0 because F(0)=1. The zero combination gives a₀=0 at a dirty row, proving independence; the representation gives the contradiction 0=1 at the terminal. Therefore the terminal-out annihilator of E₄ is exactly ⟨G,w,wY⟩: dimension three, with independence on two distinct w-live clocks where G=0.

Let a,b,u now be first three distinct nonzero reflected generic clocks in reverse physical order. For the same P, use the actual marked row `ρ=βP(Y)−λ G` with λ chosen to kill the later dirty index (nonzero G there). It vanishes strictly before u in reverse order even with a potential intervening reflected-zero generic. The row `ρ𝓡` annihilates E₄ by `𝓡 E₄⊂ F₆` and the paid degree-three reflected read, and its terminal coordinate is zero since `𝓡 e_t=0`. In the span of `G,w,wY`, the strict reverse prefix reads at the late dirty and at a,b again kill all coefficients. Thus `d_u=0` from the inclusive read, since `ρ_u=b_u P(u)≠0`. The actual primitive residual `βIP(Y)−ρ A` is in `⟨G,w⟩` by the true reflected grade-three integration-by-parts identity. The A term is zero through the debut. Dividing only by the live ordinary weights gives the same common `IP/h`, also excluding an extra reflected-zero generic beforehand. Thus these are the actual latest three generic rows. No weighted-transpose tableau or fictitious stage was introduced.

At either end the genuine paired rank argument gives

```
u(4ab−a²−b²)=ab(a+b).
```

For completeness, fit `B(a)=q h_a, B(b)=q h_b` in the at-least-three-dimensional space of pairs `(B,q)`, with degree≤4 and `B(0)=0`. Forward use `B(c)−q h−B(ξ)g/γ` (all dirty h=0); reverse use `β B(Y)−q w−λ_B G` with the marked late dirty correction. It vanishes on the strict prefix through the first two generics, and its A image is zero at u as `d_u=0`. The true degree-four residual on the three generic observations has dimension at most two (affine h coefficient; reverse divide by live b). Hence a nonzero kernel pair has `B≠0` and `IB` a multiple of `X²(X−a)(X−b)(X−u)`. Comparing its two derivative-to-h ratios and the already common `IP/h` yields the displayed paired cubic. Every forward input here has degree **at most four**.

## 4. Exact one-end elimination

Use `S=a+b,P₀=ab,D₀=6P₀−S²,N₀=P₀S`. The paired cubic gives `u=N₀/D₀`; all `S,P₀,D₀≠0` by the distinct nonzero clocks (if `D₀=0` the paired equation first forces S=0). The primitive factor is `J(X)=12IP(X)=3X^4−4SX^3+6P₀X²`. Since at both ends `h∝ F`, the pairs of values of F,J at a,b,u are proportional. Reduce F and J modulo `X²−SX+P₀` to `f_0+f_1X`, `j_0+j_1X`. Set `f_U=D₀^4F(N₀/D₀)`, `j_U=D₀^4J(N₀/D₀)`, simple cleared polynomials. The three necessary polynomials are

```
C=f₁j₀−f₀j₁,
E=(f_U j₀−j_U f₀)/P₀,
E′=(f_U j₁−j_U f₁)/S.
```

Both indicated divisions are polynomial identities (and the actual denominators are nonzero). The exact rational resultant/gcd replay gives, up to a nonzero factor, the gcd of `Res_{P₀}(C,E)` and `Res_{P₀}(C,E′)` as

```
S¹⁷ (S−1)(3S²−6S+2)(224S⁴−672S³+672S²−252S+27) G₈(S),

G₈(S)=2016S⁸+46200S⁷−253204S⁶+530922S⁵−587973S⁴
       +376686S³−140670S²+28512S−2430.
```

The exact reduced rational bases after adding each candidate factor give `P₀=1/4, S/2−1/6, 2S²/9` for the first three nonzero factors respectively, making either a=b or u one of a,b. The remaining factor is G₈, for which `P₀=p(S)` exactly, with

```
p(S)=[240326547552 S⁷+5605993175160 S⁶−27886169534188 S⁵
      +51867299523606 S⁴−48858014778303 S³+24916972066389 S²
      −6582222614817 S+709443967905]/7990348842.
```

This is exact rational arithmetic, not a heuristic search over numeric roots. These requirements apply to the unordered first pair and its third debut; their cubic has no dependence on the orientation of a,b.

## 5. The middle node contradicts a tensor-unit certificate

Let S and T be the paired sums of the first and last three generic clocks (the latter *reflected*). Define the scaled cubic

```
C_S(X)=(X²−SX+p(S)) [(6p(S)−S²)X−p(S)S].
```

It has the forward three clocks as roots, and `C_T(1−X)` has the backward three original clocks. Put `Q_6(X)=C_S(X) C_T(1−X)`, and let z be the remaining middle generic (physical stage 6). The actual seven generic weighted nodes represent the interior part of ν through degree nine: the true endpoint weights already match, and the dirty pair cancels. Thus `(X−z)Q_6(X)`, and its first two X multiples, have zero interior Lobatto integral. Write `J_i=ν_interior(X^i Q_6)`; exactly,

```
J_i = ∫₀¹ Xⁱ Q₆(X) dX − [Q₆(1)+1_(i=0)Q₆(0)]/30.
```

We have `J_1=zJ_0, J_2=zJ_1`, so `J_0J_2−J_1^2=0`. The residue of this minor is a **unit** in `𝔽₄₁₉[S,T]/(G₈(S),G₈(T))`, by exact computed 8×8 coefficient arrays and an explicit inverse. In particular no pair in any *extension* of the residue field can make it zero. The same independent computation passes modulo 719. Good reduction needs only the two algebraic sums: the leading coefficient 2016 and the rational denominator 7990348842 are units modulo 419, and a prospective S,T are integral after monic normalization. Reduce at any prime over 419 in their algebraic field. All moments and the necessary polynomial identity specialize, contradicting the explicit unit; no assumption of prime-field residues or of integral arbitrary tableau coefficients is made.

The two Python scripts independently replay the exact rational resultant/basis calculation and the modular tensor certificate. `DIRKOrderTenConstantSharedZeroScalar.lean` verifies the finite normalizations, actual computed moment minor, and explicit inverse in the octic tensor quotient. The actual grade/rank and end-cut bridge and the rational elimination are mathematical plus exact external algebra, not a complete native HasOrder theorem. The signed DA case is supported by the separate generic field and fixed-clock Lean packet. Together they close all active constant one-physical-dirty-clock cases. Invisible cases and the unrestricted numerical stage bound remain unchanged.
