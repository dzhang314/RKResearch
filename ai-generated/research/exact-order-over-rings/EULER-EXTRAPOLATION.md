# Exact RK order over a nonzero commutative ring: the factorial-unit boundary

Let R be a nonzero commutative ring with identity and let p≥1. The following
are equivalent.

1. The scalar p! is a unit of R.
2. There exists an explicit RK tableau over R of exact order p.
3. There exists a lower triangular RK tableau over R of exact order p
   with A_ii∈R^× at every stage.

“Exact order p” means the literal, denominator-cleared HasOrder p and failure
of HasOrder (p+1). The third statement is a DIRK with unit diagonal entries
(not necessarily a common diagonal, so not a general SDIRK assertion).
The explicit construction uses at most 1+p(p−1)/2 stages; the unit-diagonal
DIRK construction uses p(p+1)/2 stages. These are existence counts, not
minimal-stage claims.

## Necessity and unit coefficient arithmetic

Let γ(t)=t! be the native tree factorial (the root size times the product
of the full factorials of its rooted branches). For the p-vertex tall
tree γ=p!, so any HasOrder p tableau satisfies

    (p!) · 𝐛 · 𝚽(tall_p) = 1.

Thus p! is a unit in R, irrespective of triangularity. Conversely we now
assume p! is a unit. Every nonzero integer with absolute value≤p, and
every integer divisor of p!, then maps to a unit. The multiplication
and inverses of these scalars can equally be interpreted in the universal
coefficient ring Z[1/p!] and transported to R. No inverse of (p+1)! is
assumed.

## Native tree read on an Euler block

For each n=1,…,p set z_n=(n: R)^(-1). Work in an n-stage block with
i,j=0,…,n−1 and b_j=z_n. Define the two block matrices by

    A⁻(n)_ij = z_n if j<i,  and 0 otherwise  (forward/left Euler);
    A⁺(n)_ij = z_n if j≤i, and 0 otherwise  (backward/right Euler).

Let w_n^σ(t) be the raw output 𝐛 · 𝚽(t) of either block for σ=− or +.
When t has q vertices, expand the native product recursion in physical
stage indices; each occurrence of a vertex uses its own position,
including distinct occurrences of isomorphic branches. Every term is
z_n^q: one z_n for the output/root stage, one for each edge. The surviving
terms correspond to assignments of labels 0,…,n−1 to vertex positions
whose labels strictly decrease along each parent-to-child edge for σ=−,
or weakly decrease for σ=+. This statement is inductive on the same
rooted-tree recursion and involves no analytic ODE assumption.

Group such assignments by the ordered nonempty classes of positions which
receive equal labels. Let M^σ_{t,k} be the integer number of valid class
patterns with k distinct labels, independent of n. Choosing the k
increasing actual labels gives exactly binom(n,k) assignments per
pattern, including zero if k>n. Hence for every n with n invertible,
even outside the paid tree range, the raw output is

    w_n^σ(t) = z_n^q Σ_{k=1}^q M^σ_{t,k} binom(n,k).                (1)

For q≤p all the necessary k! are units. Substitution of the falling
factorial expression for the integer binomial coefficient proves that
(1) is evaluation at z=z_n of

    P_t^σ(z) =
      Σ_{k=1}^q [M^σ_{t,k}/k!] z^(q−k) Π_{r=0}^{k−1}(1−r z).       (2)

The r=0 factor is 1; each summand has degree at most q−1. Only k=q can
contribute to the constant term. When labels are injective, the strict
and weak requirements coincide. Their ordered class patterns are the
linear extensions of the ancestry order. If the branches have sizes
q_1,…,q_a, fix the root last and shuffle the branch linear extensions:
the count is the multinomial integer (q−1)!/Π q_i! times their individual
counts. By induction this gives the integer identity

    M^-_{t,q} γ(t) = M^+_{t,q} γ(t) = q!.

In particular γ(t) divides q! and in the paid range is a unit. Thus for
both Euler conventions P_t^σ(0)=1/γ(t), exactly the required raw tree
weight. Formula (2) works over Q at all q, but over the arbitrary R here
we only use it at q≤p. The next-order obstruction below is already
denominator-cleared, not an invocation of (2) at q=p+1.

## Extrapolation with no extra inverses

For two distinct n,m in 1,…,p the difference z_n−z_m=(m−n)/(mn) is a unit.
The Lagrange coefficients evaluating at zero at these nodes are

    λ_n = Π_{m≠n} (−z_m)/(z_n−z_m)
        = (−1)^(p−n) n^(p−1) / ((n−1)! (p−n)!).

All divisions in this expression are by units. The Vandermonde
determinant is their product of pairwise differences and is a unit, so
evaluation on the p nodes is injective on polynomials of degree below p
over R, including when R has zero divisors. Therefore

    Σ_{n=1}^p λ_n P(z_n) = P(0)   (deg P < p).                     (3)

Put the corresponding blocks on the diagonal of a single A and use
weights λ_n z_n in block n. The stage recursion stays in its block, so
the overall raw read is Σ λ_n w_n^σ(t). By (2) and (3) this equals
1/γ(t) for every q≤p, and hence the actual HasOrder p equations hold.

Both constructions before compression have p(p+1)/2 stages.
The backward blocks are lower triangular with every diagonal entry
z_n∈R^×. When p≥2 this particular tableau is even nonconstant-diagonal:
z_1=1 and z_2=1/2 differ by a unit. In the forward blocks all p first
rows are zero, so those origin stages have identical stage column
values (1 for a leaf, 0 for any nonleaf). Merge these origins into one
zero row, redirect each incoming reference, and add their b weights.
Induction on trees shows all other stage columns and every output are
unchanged. Each other branch row refers only to earlier rows of that
branch or the common origin. The compressed tableau is explicit and
has p(p+1)/2−(p−1)=1+p(p−1)/2 stages.

## Certified failure at order p+1 without dividing by (p+1)!

Use the (p+1)-vertex tall tree as the witness. In the forward method,
each original block has n≤p, so no p-step strict descending label
chain is possible; its tree read is zero. The denominator-cleared
residual, defined as (p+1)! times raw read minus 1, is exactly −1.
Origin compression preserves it.

For the backward block the integer number of weak chains with p+1
vertex positions and n labels is binom(n+p,p+1) by stars and bars. The
following is an integer counting identity before taking the ring
image; it never needs a factorial inverse:

    (p+1)! · binom(n+p,p+1) = n(n+1)···(n+p).

After multiplication by z_n^(p+1), the denominator-cleared tall
read of this block is E(z_n), where

    E(z) = Π_{r=0}^p (1+r z),   E(0)=1,   coeff(z^p) E = p!.

Subtract the leading term and apply (3) to the rest. The monic
interpolation remainder identity, or (3) applied to
X^p−Π_{n=1}^p(X−z_n), gives

    Σ λ_n z_n^p = −Π_n(−z_n) = (−1)^(p+1)/(p!).

Consequently the backward tableau's denominator-cleared tall output
at order p+1 is 1+(−1)^(p+1), and its residual is exactly
(−1)^(p+1)=(−1)^(p−1). Both residuals are units and nonzero in every
nonzero ring. This proves exactness even when (p+1)! is a nonunit or
zero in R, or when −1=1.

## Positive characteristic

For characteristic N>0, a scalar integer a is a unit of R iff gcd(a,N)=1:
Bezout supplies its inverse when coprime; otherwise a annihilates the
nonzero scalar N/gcd(a,N), so cannot be a unit. Thus the exact possible
positive orders (with no stage limit) are 1≤p< the least prime divisor
of N. In a field of characteristic ℓ>0 this says exactly p<ℓ. In
characteristic zero the condition is not automatic for rings: Z itself
allows order one but no higher order. These consequences do not claim
anything about the sharp stage floor at a given admissible order or
about a common diagonal.

For an exact-order construction with any [prescribed common diagonal](PRESCRIBED-COMMON-DIAGONAL.md), the same unit condition suffices.
