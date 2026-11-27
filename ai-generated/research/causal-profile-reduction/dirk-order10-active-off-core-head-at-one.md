# Active nonconstant DIRK10/11: off core and off head, with other head at 1

Work over characteristic zero with an actual eleven-stage lower triangular rooted-order-ten tableau. Assume the cubic defect `g=Ac²−c³/3` has one physical numerical clock ξ, its nonzero values are not constant, and some `b_i g_i≠0`. This excludes the chart where ξ and one of the two exterior h-heads q are off-Lobatto, and the other head is at **clock 1 on a nonterminal physical row**. It is separate from `dirk-order10-active-off-core-two-off-unique-terminal.md`, which assumes terminal clock uniqueness. Combined with that packet and the fixed-core two-off packet, the active nonconstant one-local branch cannot have exactly two off-Lobatto labels. No conclusion is made here about active constant, invisible, or three-off branches or the unrestricted 11–12 interval.

## 1. Physical setup and one late event

Use the signed physical and compensated reflected suffix of `dirk-order10-paid-one-off-repair.md`, with `h=(A−ξ/2)g`, `γ=ξ³/6`, `H(X)=42XJ₄(X)`, and `e_t=H(c)+δg+L(c)h`, deg L≤1. The first core value is γ, the alternate is g′; `J=g′/Q(ξ)` using `g²=γg+Q(C)h`. The terminal profile gives

```
δ=−H(ξ)/γ,   γJ=H(ξ)/L(ξ),       h_q=−H(q)/L(q),       h_1=−1/L(1).
```

These L evaluations are nonzero: H(ξ) and H(q) are nonzero at off clocks, a changed core exists, and the nonterminal unit head has h nonzero. No zero g row can occur at off ξ. There are exactly six ordinary active Lobatto rows, a same-g opposite-weight active core pair, an alternate-g core ghost, and ghosts at q and 1. In particular the nonterminal unit head and true terminal are distinct physical rows, and the latter occurs only as stage 11.

As before, physical stages 7,8,9 are the ordinary interiors R,W,U in reflected coordinates, and stage 10 is the late active dirty. The finite location guard shows the head at 1 cannot follow the first regular interior x. Exactly the forward one-late arguments of the terminal-unique packet apply with τ=1: the nonterminal unit head really is an earlier physical donor, but the true terminal is not. A late q yields the nonzero swapped-Radau square, and a late core yields the forbidden Radau root by the marked degree-three input and `d_x=0`. The new finite check evaluates the same `lateForward` gate at τ=1 for all four possible fixed x. Nothing in that argument conflates the two clock-one rows or uses terminal uniqueness. Hence the first x is physical stage 6 and both heads and the two early core values precede it.

## 2. The affine barycentric numerator is proportional to L

Let D be the same live signed row of the true repaired reflected suffix, specified by `D=GA/[(1−ξ)³/6]`. Write `D_v` for its numerical-clock aggregate in this section. It annihilates E₅, hence clock polynomials of degrees 0–5 as well as h,Ch,g. Since both off labels ξ,q and all six fixed labels occur, its eight-node barycentric expression in original coordinates is

```
D_v=R(v)/[(y−1)H(y)(y−ξ)(y−q)]′(v),       deg R≤1.
```

This is the two-dimensional Vandermonde nullspace for six moment equations on eight distinct nodes. It allows D at the original clock 1 to be nonzero: the true terminal entry is zero, but the unit head has a live D entry.

The total contribution of the core clock ξ to Dh is `−D_ξ γJ=−D_ξ H(ξ)/L(ξ)`. To see this without splitting an aggregate tap, let λ′ be the sum of D entries carrying g′. Then `Dg=0` gives `(g′−γ)λ′=−γ D_ξ`, and the h contribution is `J(g′−γ)λ′`. The q and 1 contributions are `−D_v H(v)/L(v)` by the terminal profile; all other h vanish. The two paid tests Dh=DCh=0 therefore make

```
D_v H(v)/L(v),     v∈{ξ,q,1},
```

a three-node barycentric sequence of degrees 0 and 1. Since the global denominator factors as `H(y)Π(y)` on these nodes, where `Π(y)=(y−ξ)(y−q)(y−1)`, their entries are `[R(v)/L(v)]/Π′(v)`. The q entry is nonzero. Thus R(v)/L(v) is one constant at all three distinct nodes, and, as both are affine, **R is proportional to L**. This uses actual paid h moments rather than imposing a false terminal zero.

## 3. Suffix affine line and exact normalization of L

Let (t=ξ), let U,W,R be the three reflected ordinary interiors, X the earliest regular reflected interior, and set (u=1−U, v=1−W, r=1−R, x=1−X). All three suffix ordinary interiors are singleton. To distinguish the fixed reflected clock R from the numerator of §2, now write (M_s=b_s\Lambda'(s)k_s), (\Lambda(Y)=(Y−1)H(Y)), and (Q_\mathrm{off}(s)=(s−(1−t))(s−(1−q))). Using the repaired tap (D_s/b_s=k_s/[V(V−U)]), where (V=1−ξ), the previous identity gives

```
L(1−s)  proportional to  M_s Q_off(s),           s=U,W,R,
```

with a single nonzero proportionality across s. Importantly **there is no division by s** here, unlike the terminal-unique case. Affinity of these three values gives a line (P=αS+β) for the sum S and product P of the reflected off pair. With (w_U=W−R, w_W=R−U, w_R=U−W), the two constants are

```
Δ=Σ_s w_s M_s,
α=(Σ_s w_s M_s s)/Δ,        β=−(Σ_s w_s M_s s²)/Δ.
```

The fixed denominator Δ is a unit in the replay. With (c_0=1−α,d_0=2α+β−1), the original labels obey (tq=c_0(t+q)+d_0); the unit check (ρ=d_0+c_0^2\ne0) yields (D_0=t−c_0, B=c_0t+d_0, q=B/D_0, T=B−tD_0). Do not confuse this polynomial denominator (D_0) with the paid row D.

Normalize the L profile by a common nonzero scalar (all subsequent identities are homogeneous in L) as

```
l(y)=(v−y)M_U(t−u)(B−uD₀)+(y−u)M_W(t−v)(B−vD₀),
l₁=l(1),
L_t=M_W(B−vD₀)−M_U(B−uD₀),
L_q=M_W(t−v)−M_U(t−u).
```

Then exactly `l(t)=(t−u)(t−v)L_t` and `D₀l(q)=(B−uD₀)(B−vD₀)L_q`. The relation fitted at R is a polynomial identity in this Möbius parameter: if t=r then the value l(r) at the third suffix clock must vanish. Since r≠u,v, this shows (L_t(r)=0). Likewise when (q=r) at the root of (B−rD_0), the same l(r) must vanish, so (L_q=0). At those evaluations all relevant (D_0) are nonzero by the fixed guard (c_0\ne r) and ρ≠0. Accordingly the exact linear factors are

```
L_t=λ_t(t−r),        λ_t=M_W(c₀−v)−M_U(c₀−u),
L_q=λ_q(B−rD₀),      λ_q=(M_W−M_U)/(c₀−r).
```

Both λ are nonzero, with checked guards. Cancelling only the nonzero ordinary-clock factors at the actual off pair gives the useful normalized head/core ratios

```
C_t=42(t−x),            C_q=42(B−xD₀),
H(t)/l(t)=t C_t/λ_t,     H(q)/l(q)=B C_q/(D₀⁴ λ_q),
H(1)/l(1)=1/l₁.
```

No individual diagonal or grade-five ordinary input is used here.

## 4. True absent column and chronology

Use the monic quartic `N(y)=y(y−t)(y−q)(y−1)`, with (p_v=I N(v)). It vanishes on all actual inclusive donors strictly before x. Its residual (A N-I N) is in F₅, spanned by g,h,Ch: at a head its h coefficient is (-p_v/h_v), and at the changed core it reads (p_t=\gamma J\ell_N(t)) after the first-core read and the nonzero changed-value cancellation. Hence (p_v l(v)/H(v)) on the three labels (t,q,1) is an affine sequence. In particular with (F(v)=H(v)/l(v)) it requires

```
(1−q)p_t/F(t) − (1−t)p_q/F(q) − (t−q)p_1/F(1)=0.
```

The primitive polynomials are

```
P_t=10B−5(D₀+B)t+3t²D₀,        p_t=−t³P_t/(60D₀),
P_q=10tD₀²−5(1+t)BD₀+3B²,      p_q=−B³P_q/(60D₀⁵),
P_1=10tB−5(tD₀+B)+3D₀,         p_1=−P_1/(60D₀).
```

With (B_1=B−D_0) the cleared absence polynomial is

```
A_num=B₁ t² P_t λ_t C_q +(1−t)D₀B²P_qλ_q C_t − T P_1 l₁ C_t C_q.
```

The exact factor (T(t−1)B_1) is divided out in characteristic zero. At t=1 we have (P_t=P_1), (l_1 C_t=λ_t) (the latter is just (H(1)=1)), and (T=B_1), so the first and third terms cancel. At (B_1=0), q=1 and (P_q=D_0 P_1), (l_1C_q=D_0^3λ_q); terms two and three cancel. At (T=0), q=t, (P_q=D_0 P_t, C_q=D_0 C_t, λ_t=D_0^2λ_q); terms one and two cancel. The constant λ identity at T follows by equating (l(t)=l(q)) using the exact factored expressions. If a T root equals one of u,v,r, the cancellation instead follows algebraically from those factorizations of L_t and L_q: (L_t=D_0 L_q) at q=t, so (λ_t(t−r)=D_0^2λ_q(t−r)), and the special r case is excluded by the fixed check (T(r)\ne0). The units (T(1),c_0−1,ρ) ensure the factors' roots are disjoint and simple. Thus the reduced A has degree at most four, and none of the removed factors can vanish at the actual distinct off labels.

As in the terminal-unique case, the first changed core must be after the first nonzero head. If it is before the second head, the honest anchored cubic before that change gives (a^3(a−2t)F(t)+t^3(2a−t)F(a)=0) at the first head a. If after both heads, the cubic `P(y)=y(y−q)(y−1)` modified by subtracting `P(t)g/γ` is zero on the prefix through both heads. Their IP reads are then proportional to h, which gives (q^3(q−2)F(1)+(2q−1)F(q)=0). The cleared alternatives are

```
B_q     = λ_q D₀ B²(B−2tD₀) C_t + λ_t t²(2B−tD₀) C_q,   degree ≤6;
B_one   = (1−2t) C_t l₁ + λ_t t²(2−t),                   degree ≤4;
B_after = λ_q D₀ B²(B−2D₀) + (2B−D₀) C_q l₁,            degree ≤4.
```

The exact residue checks give degrees 4,6,4,4 and coprimality of the reduced A with all three alternatives for each of the 24 physical suffix orders. No other forward quadrature or normalization is needed.

## 5. Exact verification scope

`DIRKOrderTenOffCoreHeadOneScalar.lean` replays the finite scalar guards and primitive/chronology resultants modulo 419. The independent exact Python computations pass modulo 419 and 719. The proof of the tableau-to-scalar bridge and exact characteristic-zero divisibilities is in this note, not a complete native Lean HasOrder theorem. Good reduction uses only the splitting field of the fixed-clock quartic at a prime over 419, with fixed denominator and leading-degree guards, then nonzero resultant. There is no reduction or integrality requirement on the unknown tableau coefficients.
