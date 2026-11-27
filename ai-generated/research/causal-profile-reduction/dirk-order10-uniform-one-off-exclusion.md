# DIRK10/11: the one-off ghost branch closes without a weighted census

For an actual eleven-physical-stage lower triangular tableau of rooted order ten over a characteristic-zero field, put `c=A1`, `C=diag(c)`, and `g=Ac²−c³/3`. Assume all physically nonzero g, including those on rows with weight zero, are at one numerical clock ξ. Then **exactly one physical off-Lobatto clock is impossible, for arbitrary weights**. This covers the previously unresolved invisible case and is independent of a signed/block census or of `G∥βg`. Along with the all-fixed exclusion, it forces at least two distinct off-Lobatto physical labels in the one-local branch. It does not change the unrestricted 11–12 stage interval.

The valid one-clock band is used throughout: let `h=(A−ξ/2)g`, let I denote primitive from zero, and `H(X)=42XJ₄(X)` be the fixed terminal Jacobi polynomial. Then

```
F₄=⟨g,h⟩, F₅=⟨g,h,Ch⟩, Ah=(m+nC)h,
F₆∩{v_t=0}=⟨g,h,Ch,C²h⟩,
e_t=H(c)+δg+L(c)h, deg L≤1,  Ae_t=0,
g_t=h_t=0,  c_t=1.
```

The first nonzero numerical clock is ξ, with `γ=ξ³/6≠0`, and every stage in a prefix using only `{0,ξ}` has h=0 and g=γ at ξ and g=0 at 0. These are actual C(2) computations on inclusive rows. The ordinary quadrature equals the fixed six-label Lobatto measure: the difference is supported on the six labels and the sole off q, and kills powers 0 through 9, so it vanishes by Vandermonde. Each fixed mass is nonzero and therefore all fixed labels occur. This uses ordinary order only and does not classify any physical weights. At a row where `g=h=0`, genuine C(5) integrates inputs of degrees **0 through 4**.

## 1. Constant nonzero g: only the first prefix is needed

Here every dirty g equals γ. Call a row exterior if g=0, even if it shares ξ's numerical label. The valid earlier three-debut cut says that the first two distinct nonzero exterior clocks `a,b` have nonzero h, the third `u` has zero diagonal, and the primitive `I P` of `P=X(X−a)(X−b)` gives a common scalar multiple of h on these three rows. Their paid paired scalar is

```
u(4ab−a²−b²)−ab(a+b)=0.                         (C)
```

All three cannot be fixed. If the third is off q, it has h≠0 by the terminal identity. Otherwise q is one of a,b; if the third had h=0, its actual primitive would give `q=u(4v−3u)/(6v−4u)` for the other fixed head v. The fixed-pair certificate rules this out together with (C), with the divisor guarded. Thus the three nonzero h-head labels must be `{q,1,τ}`: at any fixed nonzero exterior label other than one, live h requires a root of nonzero L, which has at most one root. In particular `τ` is a fixed interior common root of H,L, and all other exterior h positions are zero (including at zero). The h values at q and at the nonterminal exterior clock-one head are each functions of their label by the terminal identity.

Let x be the first nonzero physically regular row (`g=h=0`); some fixed interior outside the exceptional labels is regular, and no nonterminal regular clock-one row exists. At x the identity `Ag(x)=0` removes the **total** dirty tap, since all nonzero g equal γ. This still works when the dirty clock also has clean rows: only taps from the dirty subset are removed. If fewer than three head labels occurred earlier, the effective inclusive donor set is contained in `0,x` and at most two earlier head labels. If at most one is distinct from x, two paid nodal inputs of degrees 3 and 4 contradict exact quadrature (for labels `0,a,x` their primitives give `2a=x` and `5a=3x`). Otherwise x is the third exterior debut, so has zero diagonal by the original cut. Integrate `X(X−a)(X−b)` and its X multiple (degrees 3 and 4), now zero on every effective donor. Then `a+b=6x/5`, `ab=3x²/10`. At least one of these two heads is fixed, and the fixed Radau guard `10a²−12ax+3x²≠0` contradicts this. Therefore all three heads precede x.

To include repeats and signed/invisible weights, use the real grade-four input

```
N(X)=X(X−q)(X−1)(X−τ),   N(c)−N(ξ)g/γ.
```

This masked input vanishes on **every** physical row strictly before x, including repeated dirty rows, simultaneous h-head copies, and clock zeros; triangularity retains the current diagonal. Its actual primitive residual in F₅ agrees there with `−I N(c)`. At any earlier exterior τ row it thus reads `−I N(τ)=ℓ_N(τ)h_i` with affine ℓ_N. The already verified corrected constant coprimality case at receiver `x=τ` says that (C) and `I N(τ)=0` have no common root q (over the residue algebraic closure, with leading guards). Therefore all earlier τ h values agree; moreover x cannot equal τ, because then N vanishes on every effective donor at x and C(5) would require `I N(τ)=0`.

Thus h at every prior h-head row agrees with h at its first occurrence, and hence with the same scaled `I P` there, independent of weights and multiplicity. At x the degree-four input N isolates its actual diagonal: `d_x N(x)=I N(x)`. The separately paid degree-four input `I P` and `Ah(x)=0` give `I²P(x)=d_x I P(x)`. The resulting scalar `I²P(x)N(x)−I P(x)I N(x)=0` is disjoint from (C) by the corrected constant resultant. This proves the full constant case without any weighted block or repeated-clock census.

## 2. Nonconstant g: actual prefix and three exhaustive assignments

The actual grade-six payment and one-clock band give

```
g²=γg+Q(C)h,     deg Q≤2, Q(ξ)≠0,
h_i=g_i(g_i−γ)/Q(ξ)  at c_i=ξ.
```

There are exactly two exterior h-head labels, distinct from ξ, by the same native non-invariant F₅ gain. If q is an exterior head it needs `L(q)≠0`; if q=ξ off and `L=0`, the core terminal identity fixes all g to one value. Thus L is nonzero, and the exact possibilities are:

1. **Off core:** `ξ=q`. The exterior heads are `τ,1`, where `τ` is a fixed common root of H,L (τ may initially be zero), as two distinct fixed nonunit heads would need two L roots.
2. **Interior fixed core:** q is an exterior head, ξ fixed interior. Initial core h=0 gives δ=0, and nonconstancy forces `L(ξ)=0`; put `τ=ξ`. The other head must be one, since outside q and 1 any exterior head requires this L root.
3. **Endpoint fixed core:** q is an exterior head and `ξ=1`. The other exterior head is the fixed common root τ (possibly zero), and `δ=−1/γ`. Every nonterminal row at ξ is dirty: the terminal identity excludes g=0 there because its core h would also be zero. Nonconstancy forces `L(1)≠0` (otherwise g would be fixed).

In assignments 1 and 3, `H(ξ)≠0` and the earliest core row gives `δ=−H(ξ)/γ`; all nonterminal ξ rows have exactly two nonzero g values. In fact their identity factors as `(g_i−γ)(δ+L(ξ)g_i/Q(ξ))=0`. Thus a second value is `g′/Q(ξ)=H(ξ)/[γ L(ξ)]`. This statement counts distinct values, not rows. The terminal row never contributes to these taps.

Let x be the first physical regular interior label outside all exceptional numerical labels. It is a fixed nonzero interior number distinct from τ if τ is interior, with `g=h=0`; it exists since all four fixed interiors occur. Before x the possible numerical donors are `0,q,τ,1`. No other exterior nonzero label can have appeared, by the definition of x. For τ≠0, the genuine degree-four cardinals on `{0,q,τ,1,x}` give **all** actual aggregate taps `S_v` into x, including a possibly absent clock (whose tap is zero). For τ=0 use the four-node set `{0,q,1,x}` and degree-three cardinals instead.

For the following prefix read use

```
N(X)=X(X−q)(X−τ)(X−1),   p_v=I N(v).
```

Its actual F₅ residual `A N(c)−I N(c)=κg+ℓ_N(C)h` has grade at most five; every input monomial has degree ≤4. Triangularity and the literal inclusive donor clocks annihilate `A N(c)` throughout the strict x prefix. Hence at head v in the prefix, `ℓ_N(v)h_i=−p_v`. On the first ξ row, `κ=−p_ξ/γ`. If `p_ξ≠0`, the strict core-prefix equation is quadratic in g with nonzero constant term, so at most two g values and none zero appear there. For assignments 1 and 3, this two-value restriction already holds globally on nonterminal rows even if `p_ξ=0`.

When `S_ξ≠0` and the strict prefix has at most two nonzero g values, `Ag(x)=0` forces actual occurrence of both γ and g′. If `p_ξ=0` the assignment 1/3 shape still forbids a clean core before x. At a changed core row the absent-column equation gives

```
γ ℓ_N(ξ) J=p_ξ,      J=g′/Q(ξ).                       (A0)
```

When the h values are constant on the prior rows of each head, `Ah(x)=0` gives `γ S_ξ J=Σ_heads S_v h_v`, because the g′ class tap equals `−γ S_ξ/(g′−γ)`. This remains true with repeated core rows: it sums over the entire class. If only one head has appeared, the missing one contributes zero. If `S_ξ=0` and there are at most two nonzero g values before x, then `Ag(x)=0` kills both core class sums and the core contribution to `Ah(x)` is zero.

## 3. Common local timing equations and the τ=0 case

Write `L(X)=ℓ(X−τ)`, and `s_v=ℓ h_v` on a head prior to x. Let y be the first head label and z the other, if the other is present. The first changed core must follow y: before any other nonzero physical clock the inclusive `{0,ξ}` prefix permits only γ. If τ=0, the first **nonzero** exterior head is used for y (any prior zero-clock row has h=0 before a different nonzero clock). The actual first head read gives `h_y=ξ² y³/[36(y−ξ)]`, and the global C(4) defect is `(3ξ/2)g+αh` with `α=3(y−ξ)(y−2ξ)/ξ²` as previously verified. When the changed core is before z (or z has not yet appeared), the inclusive core donors are 0,ξ,y and the polynomial identity for their cubics gives `α J=y−ξ/2`. When it is after z, the strict core history at z still has exactly γ: the degree-three input `X(X−y)(X−z)` at z then gives

```
y³(y−2z)s_z+z³(2y−z)s_y=0.                            (After)
```

For the latter, one can first use `36(ξ−y)(y−2z) h_z=ξ² z³(2y−z)` and substitute `h_y,s_y`; no nonzero ratio involving a g′ tap is needed.

If τ=0, either ξ=q (the other head is one) or ξ=1 (the other head is q). Before x the only possible nonzero donor labels are q and one, besides x. Therefore the **degree-four** polynomial `X(X−1)(X−q)(X−x)` has zero forward integral at x. It gives the fixed expression `q=x(5−3x)/(10−5x)`. The guarded degree-three cardinals at x give nonzero taps to q and one, hence the other nonzero head is physically prior and, by `Ag(x)=0`, two core g values were needed. The first change is after that nonzero head; all these donors are still `{0,q,1}` whether or not the zero h-head has appeared. Applying the before-change equation with `s_1=−1` for ξ=q or `s_q=−H(q)/q` for ξ=1 gives, up to sign in both assignments,

```
(1−2q) H(q)/q+q³(2−q)=0.
```

The fixed substitution above fails in all four cases mod419. No assertion about a quintic forward input is made.

## 4. Polynomial gates for fixed interior τ, x

The following is the exhaustive gate ledger for τ≠0. In the formulas below the variable q is now denoted `z` to distinguish it from the fixed actual receiver x. Write `F=H/(X−τ)=X Cτ`; `Cτ=42J₄/(X−τ)` is degree three, and the factors below are paired with `z` only at the algebraic variable. Put

```
nt = I[X(X−z)(X−1)(X−x)](x),
n1 = I[X(X−τ)(X−z)(X−x)](x),
nq = I[X(X−τ)(X−1)(X−x)](x),
k0 = τ(τ−1)(τ−x),   r = I F(x),   fτ=F(τ),
K = r k0(τ−z)−fτ nt,
pτ=I N(τ),  p1=I N(1),  pz=I N(z)=z³ Cp(z),
Cp(z)=−[10τ−5(τ+1)z+3z²]/60.
```

Thus Sτ=`nt/[k0(τ−z)]`, S1 has numerator n1, and S_q has fixed numerator nq (all nonzero denominators by distinct actual labels). The gate verifies the fixed nonzero quantities `r,nq,k0`, that `nt,n1,pτ,K` have guarded linear leading terms, and all indicated coprimalities. The score `nq≠0` requires the off q **clock** to have appeared prior to x. Independently, if neither exterior head had been prior, the effective stencil `{0,ξ,x}` cannot integrate both the cubic nodal product and its degree-four X multiple; hence at least one head prior even in the off-core assignment.

### 4.1. τ is a head (off core or endpoint fixed core)

For either assignment, the actual column

```
ℓ h+F(c)−e_t/(1−τ)+δ g/(ξ−τ)
```

is supported entirely on τ by the terminal identity. At x, applying A to it gives `I F(x)` by actual `Ah(x)=Ag(x)=0` and `Ae_t=0`; F is degree four. Consequently the normalized aggregate h contribution from τ is `K/[k0(τ−q)]`. If all prior τ h values agree, their scaled head value is `sτ=K/nt`.

| Trigger | Necessary consequence from the literal prefix | Checked exclusion |
| --- | --- | --- |
| `nt=0` (zero τ tap, including missing τ) | The `nt,pτ` guard gives `pτ≠0`, hence prior τ h values, if any, are all equal. Its aggregate primitive correction vanishes with Sτ=0, contrary to `r≠0`. | `cop(nt,pτ)`, `r≠0` |
| `pτ=0`, with `nt≠0` | `K≠0`, so at least one prior τ h is nonzero, forcing `ℓ_N(τ)=0`. At ξ=q the unit head is present since `n1≠0`; at ξ=1 the nonzero core S1 similarly follows. In both assignments a changed ξ value occurred (nonzero core tap), so (A0) must hold. Interpolate from zero at τ and the other head to obtain `f=(z−τ)p1 F−pz=0`. | `cop(pτ,K)`, `cop(pτ,n1)`, `cop(pτ,f)` |
| `ξ=q`, with no clock-one head prior | `n1=0`, τ is the first head because nt≠0, and the changed core before x follows it with no second head; the `beforeτ` equation below applies. | `cop(n1,beforeτ)` |
| `ξ=1` and zero *core* tap `n1=0` | Both heads are prior (nt,nq≠0); pτ≠0 by guard. If a changed core had occurred, (A0) would imply A below, contradicting the n1/A test. Therefore g is literally γ on all prior ξ rows. The cubic mask refund at x earns `d_x=0`: use `X(X−q)(X−τ)(c)−[X(X−q)(X−τ)](ξ)g/γ`, zero on every strict-prefix row; its true Volterra defect in F₅ vanishes there and is killed by the first core and two live heads, so its newest diagonal read is `−d_x²·v_x=0` with `v_x≠0`. Then the actual degree3/4 inputs on effective donors `{0,q,τ}` give the fixed-head Radau obstruction. | `cop(n1,A)`, fixed Radau guard |

Otherwise both heads occur and (A0) holds for the changed core. There is no problem if the **head** at one in assignment ξ=q is present but has zero aggregate tap. Interpolating ℓ_N from `−p_v/h_v` at the two heads and using the exact terminal `γ ℓ J=F(ξ)` produces in both assignments, up to sign, the same normalized polynomial

```
A = [ F ((1−τ)K(z−τ)p1 − (1−z)pτ nt) − (1−τ)K pz ] / [z(z−τ)(z−1)].
```

The numerator has the three displayed factors exactly. At z=0 both F and pz vanish. At z=τ, `K=−fτ nt` cancels the terms. At z=1, `F(1)=1/(1−τ)` and `p_z=p_1` do so. Thus deg A≤4, and no discarded linear factor vanishes at the actual off q. The first-change phases are:

```
ξ=q, first τ:   beforeτ = τ³(τ−2z) Cτ nt − z²(2τ−z) K;
ξ=q, first 1:   before1 = (1−2z) Cτ − z²(2−z) s1,  s1=−1/(1−τ);
ξ=q, after:     after = τ³(τ−2) s1 nt+(2τ−1)K;
ξ=1, first τ:  endBeforeτ = τ³(τ−2) nt−(2τ−1)(1−τ)K;
ξ=1, first q:  endBeforeq = z²(z−2)+(2z−1)(1−τ)Cτ;
ξ=1, after:    endAfter = z²(z−2τ)K−τ³(2z−τ)Cτ nt.
```

They are just `αJ=y−ξ/2` (using `α h_y=y³(y−2ξ)/12`) or (After) with the known scaled head values. Swapping y,z in (After) only negates it. Each is coprime to A, with degrees preserved in the finite check.

### 4.2. ξ=τ is the fixed interior core; the heads are q and one

Here `s_q=−F(q)`, `s_1=−1/(1−τ)` by the actual terminal identity, including any repeated head rows. Define the exact polynomials

```
B2=[−nq Cτ + n1(z−τ)(z−x)/((1−τ)²(1−x))]/[(z−1)(z−x)],
E=[z² Cp+(τ−z)p1 Cτ]/(z−1).
```

For B2 the numerator vanishes at z=1 (where `n1=nq` and `Cτ(1)=1/(1−τ)`) and at z=x (where `Cτ(x)=0`). For E at z=1 use `Cp(1)=p1` and the same Cτ value. Consequently the actual normalized head sum is `S_q s_q+S1 s1=B2/(q−τ)` and, when both heads appear, `ℓ_N(τ)/ℓ=−(1−τ)E/Cτ`. All denominators are nonzero at q off.

| Trigger | Necessary consequence | Checked exclusion |
| --- | --- | --- |
| `nt=0` (core total tap zero) | `pτ≠0`, so at most two nonzero ξ g values occur before x. `Ag(x)=0` kills their two aggregate taps and hence the core h contribution. `Ah(x)=0` requires B2=0. | `cop(nt,pτ)`, `cop(nt,B2)` |
| `pτ=0` | `n1≠0` so both heads appear; `E≠0` gives `ℓ_N(τ)≠0`. Since `κ=0`, the prefix equation forces every core h to zero, hence B2=0 again. | `cop(pτ,n1)`, `cop(pτ,E)`, `cop(pτ,B2)` |
| Unit head absent before x | `n1=0`; then `nt,pτ≠0`, so there is a changed ξ before x, with q first and no unit head yet. The before-q phase below is necessary. | `cop(n1,nt)`, `cop(n1,beforeq)` |

Otherwise there are two nonzero g classes before x from `pτ≠0` and `Sτ≠0`, both heads are present, and `γ Sτ J = (S_q s_q+S1 s1)/ℓ`. Substitute into (A0) and clear nonzero factors to get

```
Ahead = [(1−τ) k0 E B2 − Cτ nt pτ]/(z−τ).
```

This quotient is exact. At z=τ, `nt=nq`, `E=pτ/[τ(τ−1)]`, `B2=−nq Cτ/[(τ−1)(τ−x)]`, so the numerator vanishes. The quotient has degree ≤4, and `z−τ` cannot be zero at the actual off q. The corresponding phase polynomials are

```
beforeq = k0 z²(z−2τ)B2 − τ³(2z−τ) Cτ nt;
before1 = k0(1−2τ)B2 + τ³(2−τ)s1 nt;
after = z²(z−2)s1 − (2z−1) Cτ.
```

The certificate separates Ahead from each.

## 5. Exact verification and scope

`DIRKOrderTenUniformOneOffPolynomialScalar.lean` performs the residue arithmetic with explicit coefficient lists and guarded Euclidean division over the prime residue 419. The typed audit checks the τ=0 guards and all normal/exceptional gates on 12 ordered distinct interior `(τ,x)` pairs. The independent Python replay uses exact finite fraction-field operations and Euclidean polynomial gcd, and passes at 419 and 587. The constant argument uses the existing corrected common-root check, including its `x=τ` case for `I N(τ)≠0`.

For the characteristic-zero bridge, reduce only the fixed-clock splitting field at a prime over 419. The four fixed roots remain distinct and all fixed denominators are units. The normalized generic separator polynomials have the stated degree bounds and their leading coefficients are guarded as units, so coprimality modulo 419 proves nonvanishing of their exact resultants. Equivalently the first such polynomial gives monic normalization over the localization, and any prospective algebraic q reduces in an extension of the residue field. Neither approach requires q to lie in the prime field. Each small exceptional branch uses a linear gate with unit leading coefficient; reduce its uniquely determined root and apply the corresponding coprimality guard. Exact divisions removed only the displayed structural factors, all nonzero at q off. No weights, tableau coefficients, or amplitudes g′ are reduced. The finite computations are Lean checked; the actual-tableau and good-reduction derivations here are mathematical, not yet one native `HasOrder` theorem.
