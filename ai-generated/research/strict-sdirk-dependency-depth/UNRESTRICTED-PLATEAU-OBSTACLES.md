# Limits of repeatable plateau routes to the unrestricted SDIRK table

**Pure mathematical architecture comparison, not an unrestricted
lower bound or a new upper entry.** The verified unrestricted real
algebraic strict SDIRK upper through orders 1,...,20 is

    1,1,2,3,5,7,9,11,14,17,20,23,26,30,34,38,43,48,54,59.

The diagonal may be chosen rather than prescribed. The class allows signed weights, nonterminal output and skips. None of the arguments below changes
it. They isolate what would have to change in two natural repeatable
construction strategies. All arithmetic below is characteristic zero.

## 1. Keeping independently isolated paid clock hulls is too costly

A single local hull is a useful arithmetic certificate precisely
when the paid physical observations can be grouped in that hull's
clock labels. The following obstruction does not assume adjacency.
Let c=A1, Y=diag(1−c), B=A−γI. For d=0 define r₀=ceil(p/2);
for 1≤d≤p−2 define r_d=floor((p−d)/2). Consider the normalized
paid matrices with columns c^a/a!, 0≤a<r_d, and rows

    L_j = bᵀ Y^j B^d/j!,
    j=0,...,r_d when d≥1;    j=0,...,r₀−1 when d=0.

Assume there are pairwise **physically disjoint** sets S_d of
stages such that each L_j at that distance, after grouping equal
labels, reads only labels represented in S_d. Stages outside the
set may contribute on those same labels; they need not have zero
taps. This is a paid-length clock-isolation assumption, not a
consequence of triangularity in general. It includes the adjacent
terminal proof, its compensated skip extension and any redesigned
clock/field plateaus which still separate disjoint physical cores
in this way. It also covers mixed outputs if their relevant paid
labels really stay in these distinct core packets.

The d=0 matrix is the ordinary nonsingular beta moment matrix.
For d≥1 the paid substitution B↦I−γ id, c↦x gives the
published full-column-rank rectangular beta block:

    M_(j,a) = Σ_(v=0)^d binom(d,v)(−γ)^(d−v)/(j+a+v+1)!.

All entries are paid because d+2r_d≤p. To recall the no-sign
rank argument, put r=r_d, N=d+2r and R=1−γz. A column kernel
vector v reverses to a nonzero Q(z)=Σ_a v_a z^(r−1−a).
The missing coefficients of W E_N, with W=R^d Q and E_N the
exponential jet through N, are d+r,...,N. Its degree-≤d+r−1
truncation P is nonzero and agrees with W E_N mod z^(N+1).
Put U=RQ, V=RQ′+dR′Q. Then U W′=V W and deg V<deg U.
The polynomial U(P′−P)−VP has nonzero leading term from −UP
and degree at most N−1, yet is divisible by z^N (differentiate
the congruence and use E_N′−E_N=−z^N/N!). This contradicts
a nonzero kernel. The square terminal matrix is equally
the pairing of two polynomial bases under the rational
unit-interval integral, so is invertible in characteristic zero.

The actual matrix factors through one evaluation row per
clock in S_d, so r_d≤|S_d|. By disjointness the whole tableau has
at least

    r₀+Σ_(d=1)^(p−2) r_d
       = floor(p²/4)+1_(p odd)

stages. Thus any construction retaining this certification
architecture cannot match, let alone beat, the verified free
upper at every p=3,...,20. At p=2 it gives the one-stage bound.
The actual fixed-γ depth p−2 instead of p−1 does not evade it:
the displayed lengths stop at p−2. Reusing roots or their number
field across these distinct cores need not create even one
physical stage merger.

The same reasoning gives a useful test when clock isolation is
intentionally relaxed. Split each actual paid matrix into the
part on labels represented in S_d and the remaining part.
If ε_d is the actual rank of the second part (after grouping
equal labels), then

    r_d ≤ |S_d|+ε_d,
    Σ ε_d ≥ floor(p²/4)+1_(p odd) − total physical stages.

This is an architecture diagnostic, not a new unconditional
stage floor. For example improving 59 at order 20 would require
at least 42 summed rank units of genuinely new-label leakage
relative to any such disjoint proposed cores. At most two new
labels per paid length cannot supply this: there are only
19 lengths in the displayed family. The rows and ranks, rather
than labels alone, are the exact resource. Same-clock repetitions
and fully compensated skip windows supply no such rank.
A serious candidate can instead have genuinely overlapping
cores or use mixed-grade signed numerical observations; the
argument deliberately leaves those possibilities open.

## 2. A fixed-diagonal order ceiling for uniform prefix extrapolation

Fix a common diagonal γ≠0. In one branch choose a spacing h and
any length m, and use the strict prefix weights

    B_(i,j)=h for j<i;       A=B+γ I.

Allow arbitrarily many branches, arbitrary algebraic or other
characteristic-zero spacings (including negative or zero), and
arbitrary signed output weights at all branch stages. The
constant-spacing condition is only per branch; spacings of
different branches need not be equal. Exact sharing of literal
identical prefix stages is allowed, since one can unmerge them
to recover the disjoint union without changing any rooted
output. This covers an ordinary same-diagonal prefix interpolation
or Richardson mixture. It is not the class of general skips or
general variable-increment prefixes.

**Theorem: these tableaux cannot attain order five.**
Let C=diag(c), u=c−γ1=B1, and let H be the diagonal matrix whose
entry is the branch spacing. Thus H commutes with B and C.
Direct prefix counting gives

    [C,B]=B²+HB,              2B²1 = u²−Hu,

where vector powers and products are coordinatewise. In the
first identity the (i,j) strict diagonal entry is (i−j)h²,
while in B² it is (i−j−1)h². These exact identities can also
be used as sufficient hypotheses in a more general architecture.

Set R=CA−AC−A². It has zero scalar profile for exact integration
since X I−I X=I². Define the two actual pure vectors

    F=R1,      G=2[C,R]1,

of grades two and three, respectively (grade is tree order
minus one). From the spacing identity,

    R=(H−2γI)B−γ²I,     F+γ²1=(H−2γI)u,
    G=(F+γ²1)·(u+H1),   u·(u+H1)=c²+F.

Hence the literal vector identity

    γ² c² = u·G − F·c² − F² − γ²F.                         (A)

Every vector on the right is a pure combination of paid
rooted profiles of grade at most four. In particular F²
is the coordinatewise product of two grade-two pure
combinations; it is not inferred from a one-ended linear
word condition. Order at least five would annihilate the
right-hand side under b, yet yield γ² bᵀc²=γ²/3≠0.
This contradiction does not depend on branch lengths, a
choice of moments for the spacings, stability or a small
coefficient field. It gives no ceiling whatsoever at γ=0:
then the crucial left-hand side vanishes.

A related obstacle for exactly self-adjoint/Richardson
components does not need a prefix form. A consistent
single-diagonal branch has stability denominator dividing
(1−γ z)^s. If it is self-adjoint as a method, its stability
function R_s obeys R_s(z)R_s(−z)=1. In lowest terms this
forces R_s=((1+γ z)/(1−γ z))^j: every pole can only be
at 1/γ, and reflection forces its zero at −1/γ with the
same order. Consistency on the full time step makes
2jγ=1. Thus at a fixed γ all such branches have the same
nonzero cubic log-stability error, and no consistent
affine output combination of them exceeds order two.
This last statement is for individually consistent
self-adjoint components on the same step. It does not
assume all possible SDIRK designs are self-adjoint,
nor replace (A) when prefix branch times vary.

## 3. What genuinely variable spacings must supply

The variable-increment version of the prefix scheme is not
included in the theorem above. In a branch now let

    B_(i,j)=τ_j for j<i,    u_i=Σ_(j<i)τ_j,    c_i=γ+u_i,

and keep the same definitions F,G. Direct entrywise calculation,
without assuming a central spacing matrix, gives

    P_i=F_i+γ²=Σ_(j<i)τ_j(τ_j−2γ),
    G_i=2 Σ_(j<i)τ_j(τ_j−2γ)(u_i−u_j),
    c_i²+F_i=u_i²+Σ_(j<i)τ_j²
            =2 Σ_(j<i)τ_j(u_i−u_j).

Thus the exact discrepancy from uniform prefix identity is

    D_i = u_i G_i − P_i(c_i²+F_i)
        = 2 Σ_(j<l<i) τ_j τ_l (τ_j−τ_l)(u_l−u_j).          (B)

The equality follows by expanding u_i G_i and pairing the
ordered indices j,l. If such a tableau pays order five, the
same pure-vector bookkeeping as above requires

    bᵀD = −γ²/3.

This is one explicit early nonuniform-spacing observable;
it is identically zero on uniform branches, even if the
branches have different uniform spacings. With nonnegative
increments and nonincreasing spacing chronology, every D_i
is nonnegative, so nonnegative output weights also cannot
pass this order-five test. Arbitrary signs or a genuinely
different set of increments can evade that last sign
obstruction. Passing (B) is only necessary, and no upper
bound of order five or higher is established from it.

## 4. Implication for the proposed free-upper direction

Field descent and signed bypasses preserve stage count by
design. If used together with independent one-ended hull
certificates on disjoint depth cores, they still face the
stage-count obstruction of Section 1. The easy repeatable
way to imitate variable-diagonal midpoint extrapolation
without changing γ instead faces the exact nonlinear
grade-four obstruction of Section 2. Neither obstacle
excludes unrestricted strict SDIRK methods.

The viable next general template would have to pay actual
nonlocal defects: allow mixed supports at many paid lengths
while checking the real nonlinear feature pairings. A
genuinely coupled forward/reverse triangular bridge is one
such template already reflected in the public upper
constructions, not something obtained for free by moving
a hull to another layer or adjoining its roots. The finite
rank and spacing identities above are auditable cheap reject
tests for putative simpler templates. I did not obtain a
repeatable construction beating any verified unrestricted
entry, and have not raised a lower entry. No order-specific
search or computation is part of this analysis.

When prefixes are shared, the calculation requires exact row-sum intertwining under the map from separated copies to physical stages. In particular, for each receiving stage and each donor class the separated row has the same aggregate donor mass as the physical row. Merely matching clocks does not suffice.
