# Compact signed clock lifts and late character fusion

**Pure mathematical analysis, not a new unrestricted stage bound.**
Use the exact variable-prefix/QSym order theorem and its one-clock
character χ_x. A readout history w is an actual prefix of increments
τ, with physical clock c=γ+Στ and γ≠0. A strictly prefix construction
consists of such ladders, possibly sharing literal common prefixes.
The results below distinguish those constructions from a general
common-diagonal tableau with a mixed continuation. The latter may
escape the tight-lift restrictions. Counts use nonzero-weight effective histories: coalesce identical histories after deleting zero moves. In Gaussian conjugacy arguments, the nonresonance assumption is over the stated diagonal field, not a claim for every rational diagonal.

## 1. Fuse after a signed character lift, not only after jet equality

The paid clock localization theorem says: with q actual distinct
readout clocks, the signed group at any clock x with aggregate W
realizes W χ_x on every QSym feature through degree d=p−q.
Zero aggregate is allowed if such individual readout clocks are
included in q. Here only actual prefix histories are used
before the proposed continuation.

There is an exact nonlinear fusion rule stronger than agreement
of the individual states. Suppose histories w_i terminate at
actual input states z_i, and their weights b_i realize W χ on
QSym through degree d for **one character** χ, with W=Σb_i≠0.
Let them all take the *same* continuation Φ with
Φ(z,h)=z+O(h^t), and set z̄=Σb_i z_i/W. Then

    Σ b_i Φ(z_i,h) − W Φ(z̄,h) = O(h^(d+t+1)).             (A)

The identity part is exact. For the rest write Φ−id=h^t U,
expand U at the initial y, and use that the coefficient
of h^j in z_i−y is a linear combination of history features
of degree ≤j with vector-field dependent, history-independent
coefficients. This follows from T_w id: only a last W_1
acts on id, so it uses M_(α,1) of degree |α|+1. In each
coefficient through h^d of U(z_i,h), products of those
history features use total degree ≤d. At these grades
the weighted products agree with products of weighted
means, because χ is a character. This proves (A) for all
formal vector fields, not just linear stability. If W=0
and the same low-degree moments vanish, the whole weighted
suffix correction can instead be dropped through d+t.

The mean z̄ is a legitimate causal common-diagonal
input: every z_i is y plus h times a row of earlier
actual slopes, so its affine combination can feed the
ordinary stage equations of one continuation. Its
field and physical diagonal do not change. In particular
clock localization permits a suffix that first acts
at order q to be shared once per clock, preserving
order p, even if the individual histories do not agree
at low grades. For an ordinary continuation starting
at order one this does not suffice when q>1. The useful
target is a genuinely late **correction**, possibly itself
a signed combination of suffix blocks whose low outputs
cancel. Paying for independent new correction copies at
all clocks is not a stage-count gain.

## 2. Exact planning constraints at the least support per clock

Use p_j=M_(j), and at a fixed nonzero clock with aggregate
weight W≠0 put

    Z=p₄−2γp₃+γ²p₂ = Σ τ²(τ−γ)² ≥ 0,
    D=p₃−γp₂,
    χ_x(Z)=0,    χ_x(D)=γ²x≠0.

If Z=0, all effective increments are γ, and in particular
D=0. Normalize the group's weights by W hereafter.
Suppose the paid local degree is d=4k+δ with k≥1 and
δ=2 or 3. Moments of Z through k mean exact evaluation
at zero. Moments of D Z^j are paid through
j=floor((d−3)/4), and only the j=0 term is nonzero.

Thus at least k+1 histories are needed (as in the
earlier support note), and at exactly k+1 histories they
have distinct positive charges Z. Indeed the D equation
needs at least k effective positive charges. If there
are at most k such charges, the k positive power
moments force their aggregate weights to vanish; the
D moments need a pair of opposite weights at each,
plus some zero-charge weight to carry the total.
This costs 2k+1>k+1. For δ=3 the D moments already
need k+1 different charges outright.

With k+1 distinct positive charges, the weights are
exactly Lagrange evaluation at zero on Z-polynomials
of degree ≤k. Write H(t)=∏(t−Z_i); H(0)≠0. A feature
F of degree e has differences F_i−χ_x(F) interpolated
by a polynomial P(t) of degree ≤k. The tests against
Z^j for 0≤j≤floor((d−e)/4) imply:

* P(0)=0 from j=0;
* each succeeding j kills the highest remaining
  coefficient by the constant of the remainder
  of t^(k+1) modulo H, namely −H(0)≠0.

Thus the degree is at most
k−floor((d−e)/4), interpreted as zero when the
bound is zero. In particular every pure feature
of e≤3 has values of the form a_F Z_i. The paid
test F² Z^(k−1) has degree ≤6+4(k−1)≤d. Its numerical
value is a_F² times the nonzero value of Z^(k+1)
under Lagrange evaluation, whereas its target is
zero. Therefore a_F=0. We conclude:

    Every history of a tight (k+1)-history fiber
    individually realizes χ_x through degree three.    (B)

For e≤δ+4 the residuals are at most linear in the
same single charge. In particular at order 20 with
ten readout clocks, d=10 and all low residuals through
grade six in a tight three-history fiber lie on this
one charge direction. It is not enough to choose
any three signed histories with the same clock.

## 3. One surplus history still forces pointwise degree two

Under the same d=4k+δ conditions, if a fiber uses at
most k+2 histories, all its histories still have

    p₂=2γx−γ².                                           (C)

Here are details allowing arbitrary signed weights and
coincident nonzero charges. Put F=p₂−(2γx−γ²).
The paid tests F Z^j, j=0,...,k, and F² all have zero
target. A zero-charge history has F=−γx≠0.

If there are at most k positive charges, the 2k+1
count from Section 2 already exceeds k+2 unless
k=1. In that exceptional count the sole positive
charge has two histories and zero aggregate, and
there is just one zero-charge history. The F Z
moment kills the total F on the positive charge,
and the F moment then incorrectly gives F=0 on
the zero-charge history.

If there are k+1 distinct positive charges and
one repeated history on a charge, the aggregate
weights at these charges are Lagrange evaluation
at zero and nonzero. Vandermonde on the FZ moments
kills each conditional F mean. At all singleton
charges F is zero. On the one doubled charge its
signed mean and second moment are zero; because
the two weights and their sum are nonzero, both
values must vanish (substitute either one in the
two equations). This proves (C).

It remains to treat N=k+2 distinct charges,
possibly including zero. Let H be their monic
polynomial. The base weight equations through
degree N−2 give

    b_i=ℓ_i(0)+a/H′(Z_i),

where ℓ_i is the full N-node Lagrange cardinal.
The F-moments through N−2 give b_i F_i=t/H′(Z_i).

If zero is a charge, the weights at all positive
charges are a/H′ and a≠0. Thus F=L=t/a at every
positive charge, while its weighted value at zero
is (b₀−1)L. The F²-moment is
−(b₀−1)L²/b₀, nonzero unless L=0. But L=0 would
force F=0 at zero charge too, contradicting −γx≠0.
So this case is impossible.

When all charges are positive put c₀=H(0)≠0.
If a≠0 then
b_i=(a−c₀/Z_i)/H′(Z_i) and

    Σ b_i F_i² = t² Σ Z_i/[(aZ_i−c₀)H′(Z_i)].

The displayed factor after t² is nonzero: split
Z/(aZ−c₀) into its constant polynomial part and
a nonzero simple fraction at c₀/a. The constant
sums to zero, while the partial fraction sum is
a nonzero multiple of 1/H(c₀/a). The denominator
point is not a node because all b_i≠0. Therefore
t=0. If a=0, the weights are full Lagrange at zero
and F_i is proportional to Z_i. The paid F^N
moment forces that coefficient zero because
2N=2k+4≤d and the Lagrange value of Z^N is
−H(0)≠0. This completes the proof of (C) without
assuming positive individual weights.

## 4. Comparison with stage budgets and moderate diagonals

For p=2q with exactly q actual readout clocks the
nodes are the ordinary interior Gaussian ones, and
their aggregate weights are positive. In particular
write x_min>0 and x_max=1−x_min. If all fibers have
at most one surplus history as above, (C) at the
least node forces

    0<γ<2 x_min<3/[q(q+1)] .                            (D)

The first two strict inequalities follow from
p₂≥0 (and if p₂=0 then every increment is zero,
inconsistent with x=γ/2). The final rational estimate
can be obtained exactly without isolating nodes.
Put Q=q(q+1). The normalized shifted Legendre hull
at zero has coefficients
(−1)^j(q+j)!/((q−j)!(j!)²), by Rodrigues expansion.
For its reciprocal roots the first three elementary
sums are Q, Q(Q−2)/4, Q(Q−2)(Q−6)/36, so their power
sums are S₂=Q²/2+Q and S₃=Q³/3+5Q²/6+Q. Thus

    1/x_min ≥ S₃/S₂ > 2Q/3.

This already excludes the usual scale of moderate γ
from compact fixed-clock prefix lifts as q grows;
one must enlarge at least some fibers or abandon
pointwise prefix lifting. Within a fixed budget S,
any tight-grade-three clock satisfies an even
narrower two-sided requirement:

    x/(2S−1/2) < γ < 5x/9.                              (E)

Indeed put t=x/γ. By (B), p₂=γ²(2t−1)>0 and
p₃=γ³(3t−1). Real |Στ³|≤(Στ²)^(3/2) forces
(3t−1)²≤(2t−1)^3, hence t>9/5; the quotient on
t>1/2 is strictly decreasing and at 9/5 its square
is 2420/2197>1. Meanwhile a history of length N
has N≥p₁²/p₂=(t−1)²/(2t−1)>t/2−3/4.
Since N≤S−1, (E) follows. If *both* extreme
fibers are tight, the same exact reciprocal-root
estimate gives

    S > (3/5)q(q+1)−13/20.

At p=12,14,20 this already exceeds the verified free
upper 23,30,59 respectively. Thus even choosing
a moderate positive γ cannot make both extreme
fibers tight at these budgets. These comparisons
are for fixed Gaussian-clock prefix architectures,
not new unrestricted lower entries.

An additional sign check: if all increments were
nonnegative, a history realizing both p₂ and p₃
at a positive clock would violate
p₂²≤p₁p₃, because the virtual values give
p₂²−p₁p₃=γ²x²>0. Thus tight fibers need genuinely
signed increment histories, not merely signed b.

## 5. Physical prefix-trie cost, not just readout support

Distinct effective histories that individually realize
χ_x through degree three are at graph distance at
least three in the literal prefix trie. Zero increments
can be ignored since they do not change the history
evaluation. Empty history cannot itself realize
degree two at any γ≠0.

For siblings with final increments u,v, the differences
of power sums must be kγ^(k−1)(y−x) for k=1,2,3.
If the clocks differ, these give u+v=2γ and
u²+uv+v²=3γ², hence uv=γ² and u=v, impossible.
Equal clocks give u=v immediately. For comparable
histories of distance ≤2 let their short suffix
be (u,v), padding a missing increment by zero.
If the clock difference is zero, equality of the
second moments forces u=v=0. Otherwise the ratio
of the two prefix characters is
δ_γ exp_*(Δx L) δ_γ^−1
=exp_*(Δx·δ′_γ*δ_γ^−1) to grade three. Its
M_(2,1)−M_(1,2) value is −Δx γ²:
in the first-order term the marked part is now
the *first* part, and the second-order term is
symmetric. Normalize u,v by γ and set z=Δx/γ.
The first three power-sum differences give
u_norm+v_norm=z, their product z(z−2)/2,
and z²−6z+6=0. The squared antisymmetric
moment requires

    (z−2)² z(4−z)=4.

Using z²−6z+6=0, the left side is
4(z−1)(3−z)=4[1−(z−2)²]. This forces z=2,
contradicting the first equation. Thus the
two-step separation is impossible too.

It follows that a set of M₃ such marked histories
has M₃ different parents, none itself marked;
it costs at least 2M₃ physical nodes after exact
prefix sharing. This alone rules out the all-tight
Gaussian design at p=12 and p=20 (24 and 60 nodes);
the extreme-clock bound above covers p=14 as well.

A useful generic moderate-diagonal check also counts
more histories. Assume no two distinct marked clocks
differ by ±2γ. For histories satisfying only grade two,
a one-step marked-to-marked edge would require
u²=2γu, and hence the forbidden gap. At a common
parent there are at most two marked children by
their pairwise sum u+v=2γ. If M₂ histories are
grade-two exact and M₃ of them grade-three exact,
the number of physical stages is therefore at least

    M₂ + max(ceil(M₂/2), M₃).

If every fiber is tight or one-surplus, with n
tight fibers, this applies with M₂=(k+2)q−n,
M₃≥(k+1)n. In particular the uniform one-surplus
choice also cannot beat the free entries at
p=12,14,20 (27,32,60 stages respectively) under
this nonresonance. If the clock roots are conjugate
over the diagonal field, the nonzero gap in that
field is automatically excluded: a finite Galois
orbit cannot indefinitely translate by 2γ. Mixed
counts, resonant gaps and general non-prefix
continuations are not excluded by this test.

## 6. Stop line

No near-table family follows from these identities.
The previous large interpolation constructions
remain much larger. The positive usable mechanism
is (A): build actual small signed state lifts and fuse
their identical *late* corrections before counting
every stage. It evades a requirement of raw low-jet
equality, but not the cost of generating those actual
history states or the need to pay their coupled higher
residuals. The exact tests above rule out the smallest
uniform pure-prefix lifts at several orders and isolate
specific alternative regimes: enlarged or mixed clock
fibers and genuinely coupled high-order continuations.
They do not eliminate a moderate diagonal in an
unrestricted common-diagonal tableau. No external
compute, numerical root search or new stage-table
endpoint is part of this analysis.
