# QSym clock quotient, signed support, and actual suffix compression

**Mathematical analysis, not a new unrestricted upper or lower
endpoint.** Keep the actual variable-prefix SDIRK model and
common diagonal γ≠0 from the prefix-moment theorem. This note
gives exact rank and suffix compression rules, a limit on
physical lifting of Gaussian support, and a smaller explicit
construction outside the pure prefix class. Merely adjoining
a coefficient field, or compressing a linear output support
without its ancestors, is not counted as a stage saving.

## 1. The exact target is a one-clock quotient of QSym

Let Q be the quasisymmetric algebra on histories, with monomial
basis M_α, weighted degree |α|, and empty composition 1.
An actual history w is a finite sequence of increments, and
its evaluation on Q is a character. For two histories
concatenated, the evaluation on M_α splits at every prefix
of the composition. Thus multiplication of history transforms
is convolution for the deconcatenation coproduct

    Δ M_α = Σ_(α=β·η) M_β⊗M_η.

This coproduct is an algebra map: concatenate two independent
variable alphabets and evaluate products. The identity of
convolution is empty-history evaluation. Define δ_t to be one
increment t. Its convolution inverse at γ has
δ_γ^−1(M_α)=(-1)^ℓ γ^|α| (ℓ=length α), since evaluations at
N equal increments are binom(N,ℓ)γ^|α| and continue polynomially
to N=−1. This inverse is a character as well. Put
L=δ_γ^−1 * δ′_γ. Then

    χ_x = exp_*(x L) * δ_γ^−1

is a character. For a direct formal verification,
δ_γ^−1*δ_(γ+t)=1+t L+O(t²) is a one-parameter curve
of characters through the convolution identity. Taking
its nth convolution power with t=x/n has coefficientwise
constant term exp_*(xL) in 1/n. This follows by log in each
finite weighted degree; all nonconstant terms have positive
powers of 1/n. The constant term of the multiplicativity
identity is still multiplicativity.

Expansion into convolution words gives

    χ_x(M_α)=Σ_(j=0)^ℓ (−1)^(ℓ−j) e_j(α) γ^(|α|−j) x^j/j!.

Indeed each derivative marks a different letter, with
factor its part a_i, and every unmarked letter contributes
−γ^(a_i). The chosen j marked positions appear once in the
term (δ_γ^−1*δ′_γ)^j*δ_γ^−1. This is the primitive target
from the exact prefix-moment formula, with 1/(j+1)! recovered
by integration:

    λ(F)=∫₀¹ χ_x(F) dx,        χ_x(c)=x,
    c=γ+M_(1).

In particular F↦χ_x(F) is a split algebra surjection
Q→K[x], degree-nonincreasing, with section K[c]. Its
kernel is an ideal, not just a list of separate pure
moments. For example substitute p_k=M_(k), for which

    χ_x(p_k)=kγ^(k−1)x−γ^k.

A practical consequence is that on any prescribed finite
library of actual histories the paid moment rows split
into ordinary clock polynomials and evaluations of the
kernel. If the latter span rank r on the library, and
there are q active clock labels, the order-p functional,
**if in the actual span**, can be represented with at most

    min(q,p)+r

nonzero readout histories, by choosing a column basis.
This retains the actual histories, their algebraic fields,
and allows new signed output coefficients on the selected histories. Then keep only the
prefix closure of the selected histories, sharing identical
prefix stages literally. At that point the physical cost
is the number of retained prefixes including the final
observations, not their number of clock labels. This exact
rank/pruning rule is useful with a small actual residual
library but does not say such a low-rank library exists.

## 2. Clock-local lifting and the first real obstruction

If a candidate has q distinct actual readout clocks x_j
(count also any with nonzero individual but zero aggregate
weights), denote its aggregate weights by w_j. At p pay
ordinary quadrature through degree p−1. For each F with
deg F≤p−q, multiply by the degree-(q−1) clock cardinal at
x_j. Exactness and χ_x multiplicative show

    Σ_(i:c_i=x_j) b_i F(history_i) = w_j χ_(x_j)(F).       (A)

Indeed the target is the integral of that cardinal times
χ_x(F), a polynomial of degree ≤p−1, so the actual clock
quadrature gives the right-hand side. Higher degree
residuals need not vanish separately: for a degree-d F
their clock-group vector must annihilate powers 0,...,p−1−d.
This gives the exact low-local/high-coupled problem for
sparse signed lifts. Checking only (A) does not certify
the omitted higher residuals.

Although Gaussian time quadrature reduces the target to
ceil(p/2) virtual characters, **no one real history can lift
even one χ_x through degree four**. Namely put

    Z = p₄−2γ p₃+γ² p₂ = Σ τ_i²(τ_i−γ)²,
    D = p₃−γ p₂.

The target has χ_x(Z)=0 and χ_x(D)=γ²x. Real equality
Z=0 would force every τ_i to be 0 or γ, hence D=0 and
x=0. But then p₂=−γ² on the target is impossible for
real increments. This obstruction is independent of the
coefficient field inside the reals and allows signed
increments. It also proves that any prefix tableau of
order ≥5 requires some negative output weights:
nonnegative b and Σ b_i Z_i=0 would force D_i=0 at all
support, contradicting λ(D)=γ²/2.

There is a useful quantitative clock-local lower test.
If x_j w_j≠0 and d=p−q≥4, (A) requires at least
floor(d/4)+1 histories carrying weight at that clock.
For k=floor(d/4), use Z moments 1,...,k and D Z moments
0,...,floor((d−3)/4). The latter require at least k
effective positive distinct Z values, since D=0 at
Z=0 and the target has only the degree-zero D moment.
If there are already at least k+1 positive charges the
bound is done. Otherwise all positive charges have
aggregate weight zero by the first k moments and
Vandermonde; each effective D charge then needs two
opposite-sign observations, and a nonzero zero-charge
weight must remain. This even costs 2k+1. If d mod 4=3
the D test already forces at least k+1 positive charges.

## 3. A degree-two charge can already beat the free upper
as a conditional obstruction, not as a construction

At a clock x_j suppose every contributing history has

    F₂ = p₂−(2γ x_j−γ²)

strictly positive (or strictly negative). Its target is
zero and its degree is two, using the global clock c
in place of x_j when paying the moments. The same
Vandermonde test on F₂^1,...,F₂^floor((p−q)/2) implies

    at least floor((p−q)/2)+1 histories at that clock      (B)

whenever w_j≠0. Weight signs make no difference.

For even p=2q with the minimal q total readout clocks,
they must be the interior Gaussian nodes with positive
aggregate weights. Their monic hull is uniquely determined
by orthogonality to degree <q, and cardinal-square exactness
makes its weights positive. The strict charge sign in (B)
holds at all such clocks in any of these regimes:

* γ<0, since p₂≥0 and 2γx−γ²<0 at x>0;
* γ≥2 x_max, similarly, with p₂>0 at a possible equality
  because the sum of increments x−γ is then nonzero;
* 0<γ≤x_min/(2S) in a proposed tableau of at most S≥2
  physical stages. A prefix has at most S−1 increments,
  so Cauchy gives
  p₂≥(x−γ)²/(S−1)>x²/S≥2γx−γ².
  An empty prefix cannot occur at these clocks under
  that strict ratio.

Here the total support alone is at least
q(floor(q/2)+1) stages. At p=4,8,12,16,20 this is
4,12,24,40,60 respectively, strictly above the
verified free upper 3,11,23,38,59. This excludes a
cost-saving design with these sign and clock hypotheses,
including a small-positive-diagonal deformation at a
fixed stage budget. It does not cover moderate positive γ,
extra readout clocks, or rows that do not have the prefix
form. No unconditional stage column changes.

## 4. A sharp alphabet test, independent of branching

Let S be the set of distinct nonzero increments among
histories actually receiving output weight, and m=|S|.
Zeros can be ignored in M_α. A degree-a polynomial
P(t) with zero constant determines the power-sum
observable Σ_j P(τ_j), whose target under χ_x is
−P(γ)+xP′(γ). In particular take

    P(t)=t∏_(a∈S)(t−a).

That observable vanishes at every history. If m≤p−3,
both P and tP are paid, giving successively
−P(γ)+P′(γ)/2=0 and then P(γ)=0, P′(γ)=0.
The latter is impossible because the roots are simple.
Hence m≥p−2, even for arbitrary signed output and
unbounded numbers of blocks.

At m=p−2 the one remaining alphabet condition
P′(γ)=2P(γ) is also sufficient for the **moment span**
of arbitrary histories on S. Write d=p−1,
P(t)=t^d+Σ_(a<d)P_a t^a. Vandermonde on the nonzero
alphabet entries in degrees 1,...,d−1 gives in the
operator span of T_τ−I the vectors W_a−P_a W_d.
In any word with at least two letters and total degree
≤d these replacements give exactly the original word:
a correction containing W_d together with a positive
grade exceeds d. Thus only the top single-letter
relation is missing, and that is the stated equation.
All expressions are linear combinations of actual
history words. This is sharp in the sense of alphabet
size, not stage count.

For p≥4 one can realize the minimal alphabet in Q(γ)
without any root search: all steps are distinct and
not γ, and the condition is
1/γ+Σ_(a∈S)1/(γ−a)=2. Choose the first m−1 inverse
differences freely avoiding a finite union of proper
hyperplanes, then solve the last one. This avoids
zero increments, collisions and poles; at rational γ
the choices can all be rational. If a given algebraic
γ has degree >p−1, an entirely rational minimal alphabet
is impossible by the degree of P′−2P; p−1 distinct
rational increments always give full Vandermonde.
This is field and parameter control, not proof that
the supporting histories can fit a small tableau.

## 5. A genuine common-diagonal *physical* suffix merge

There is a nonlinear compression rule beyond merely
reweighting readout support. Suppose actual histories
w_i arrive at states z_i=y+h times previously evaluated
physical slopes, and all are to be followed by the same
ordinary common-diagonal continuation Φ(z)=z+O(h^t),
with endpoint mixture weights κ_i. Assume κ=Σ κ_i≠0.
If the histories' states agree through order r−1,
their affine mean z̄=Σ κ_i z_i/κ satisfies

    Σ κ_i Φ(z_i) − κ Φ(z̄) = O(h^(2r+t)).

Indeed the identity part and the first Taylor term cancel;
the remaining differences are quadratic in the
O(h^r) deviations, times the h^t onset of Φ−id.
For a generic continuation t=1 this preserves through
order 2r. For universal formal state series (not a single fixed ODE), the state agreement is exactly the QSym
condition that M_(α,1) agree for |α|+1<r:
only words ending in W_1 act nontrivially on the identity.
Thus no nonlinear tree search is needed to check the
merge when these low-degree signatures are known.

The merged continuation is an actual common-diagonal
RK block: z̄ is an affine sum of the original base y
and already paid slope increments, and one feeds its
linear row into each continuation stage. Its diagonal
remains γ. The field is unchanged. If the duplicate suffixes are otherwise unused and disjoint, all but the merged suffix can be deleted, saving (number of
histories−1)·(suffix size) physical stages. The merged
matrix need not itself be a prefix ladder (this is
allowed at an unrestricted upper endpoint).
Failure of the low-grade agreement leaves genuine
nonlinear second-order Taylor terms. Equal clocks suffice for the ordinary merge through order four, but not generally beyond. A valid marked-suffix
family could exploit this rule; no family attaining an
improved free count is established here.

## 6. A concrete compression of virtual midpoint, with its limit

There is a smaller ordinary common-diagonal construction
than the preceding quartic whole-history interpolation,
but still not near the free table. Use the same virtual
identity with τ_±=γ±1/(2n), midpoint substep
E_+ ∘ E_-^−1. At each substep input z, compute the
p−1 successive same-diagonal τ_- moves, retaining
each endpoint E_-^m(z) for m=0,...,p−1.
Polynomial interpolation in the common power m
at −1 gives an affine state z̄ equal to E_-^−1(z)
through h^(p−1). This is the very same prefix operator
argument, now done at the state rather than on the
whole endpoint. Evaluate the implicit slope ψγ(z̄), defined by ψγ(u)=f(u+hγ ψγ(u)), using one more physical γ-diagonal stage. The virtual midpoint update is z+(h/n) ψγ(E_-^−1(z)), so the approximate
substep agrees through h^p. Performing n substeps,
then the ordinary even-power midpoint extrapolation,
pays all rooted trees through p. All stages share
γ and lie in Q(γ); the intermediate affine row is
causal and makes this an ordinary tableau rather
than a pure prefix.

With q=ceil(p/2) this costs at most p q(q+1)/2 actual
stages. When γ=1/(2n) a corresponding virtual substep
is a direct one-stage midpoint and need not be lifted.
Exact order p can be enforced if desired by targeting
p+1 and adding the same signed next-grade unit-increment
difference as before. This is a cubic rather than
quartic construction, but nowhere a claimed improvement
of the verified table.

There is a sharp scalar reason independent *full-order*
local homogenization cannot make these costs competitive.
An r-stage common-γ block has stability function with
numerator degree ≤r and denominator dividing
(1−γ z)^r. A midpoint substep at diagonal s≠γ,
s≠0, has stability (1+s z)/(1−s z). If the two agree
through order p>r, clearing denominators gives a
numerator of degree ≤r+1 divisible by z^(p+1), hence
zero, contradicting their distinct poles. Thus that
independent local repair actually needs r≥p; the
construction above attains that per-substep cost
through p. Beating the stage table would need
cancellation across many substeps or a different
bridge, not just a cheaper exact per-substep lift.

The clock quotient and physical suffix merge identify
such conditional opportunities without huge moment grids.
The alphabet, virtual-real and per-clock charge
obstructions specify where those opportunities do not
follow automatically. No numerical special-order
search, unrestricted endpoint change, or cold input is
used.
