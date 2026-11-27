# Refunding terminal rows in coupled strict SDIRK bridges

The certified 15-row movable-port stem cannot make an order-15,
33-stage method in the grouped, whole-column-paid architecture
with one shared forward port disjoint from all old reverse
terminal means. This holds for **any number of terminal means or
scalar sites**, even with signed weights and an arbitrarily
redesigned reverse top space. The analogous 11-row coupled stem
cannot make a 25-stage order-13 method in the same architecture,
also without a reverse rank assumption. These are conditional
construction obstructions. They do not raise the unrestricted
order-13 or order-15 minimum or supply a new upper bound.

## Actual interface and why order forces the mixed pairing

Work in unit-diagonal normalized coordinates with forward clocks
$x_i$, reflected clocks $y_i=1/\gamma-x_i$, distinct scalar sites,
and nonzero aggregate weights $W_i$. Let $L$ be the actual
reverse triangular bank and $M$ take actual weighted means on
each site. The old reverse prefix has $s_r$ rows. Its dense
linear decoder $D_r$ is paid on all words in its actual
multiplication and primitive matrices through length $r-1$,
returning a polynomial of degree at most $r-1$. There are $t$
distinct terminal sites at which the actual old means are already
truthful through word length $r$ and agree with the full means.
All other sites receive one new representative. The full physical
reverse bank satisfies
\[
 ML=E_yJD_r+S(M-E_yD_r)
\]
with $J$ integration from zero; at a terminal, the relevant
row of $S$ is the corresponding unit coordinate row.
On word length $r$, write $K=P-D_r\mathbf v^{\rm old}$ for the
polynomial discrepancy and $V$ for their span. The site means
of the extended bank are exactly $E_yP$ through this length, by
induction using the grouped identity, exact return at the
preceding length, and multiplication by the site clock. Their
next primitive discrepancies are
\[
 \boldsymbol\delta(K)=(SE_y-E_yJ)K.
\]
In particular $K$ vanishes at every terminal clock, and its next
primitive discrepancy there is $-(JK)(y_i)$.

For the [15-row forward stem](../real-sdirk15-movable-port/README.md),
the decoder is exact through size six, with one size-seven
missing direction $Q$. Putting $r=6$ gives the same word
budget as the forward-response proof for the
[11-row size-six coupled stem with $r=5$](../real-sdirk13-coupled-one-defect/README.md).
The forward tail matrix $B$ is the actual reversed weighted
transpose of $L$, with the usual incoming block
$(E_xJ-BE_x)D_f$. Assume the **whole** column
$(E_xJ-BE_x)Q=0$ is paid. Actual tail profiles are then
locally pure through size $r+2$. Unary attachment gives
\[
 \mathbf e_{[u]}=B\mathbf e_u-(E_xJ-BE_x)H_u,
 \qquad H_u=P_u-D_f\boldsymbol\Phi_u^{\rm old}.
\]
A same-root leaf mark multiplies by the actual clock diagonal.
Through order $2r+3$ at most one imperfect primitive child
can occur at a root, since its size is at least $r+2$.
At output the lower exterior words through length $r-1$ are
paid by the required quadrature precision $2r+2$, the old
reverse return, and integration by parts. Start with any
actual size-$r+2$ tree, attach a unary root, then append any
word of $r$ unary attachments or leaf marks. Other source
terms have fewer exterior letters. Exact ordinary order
$2r+3$ therefore forces
\[
   \sum_i W_i H(x_i)\delta_i(K)=0
\]
for every actual size-$r+2$ residual $H$ and every $K\in V$.
Reflection replaces the forward clock letter by the reflected
clock letter plus a constant; the resulting shorter words
have already been paid. The same pairing vanishes on $Q$ by
the whole-column equality, weighted transpose and scalar
integration by parts. At the respective certified stems the
actual size-$r+2$ residuals together with $Q$ span **all**
polynomials of degree at most $r+1$ vanishing at the shared
forward clock $v$. Thus this is a necessary test on actual
rooted contexts, not an assumption inferred from a small
sample of successful word equations.

## Clock separation refunds a full grade at some terminals

Let $N$ be the number of scalar sites. Exact ordinary moments
through degree $2r+2$ require $N\ge r+2$: the moment Hankel
matrix of size $r+2$ is nonsingular, while an $N$-site moment
matrix factors through $N$ coordinates. Nonsingularity follows
from the standard rational Hilbert matrix, with nonzero
diagonal scalings for the normalized interval. No positivity
of individual weights is needed.

Delete the protected $v$ site only from the **test frame**.
On the other $N-1$ sites the $(r+1)$-dimensional frame
$H=(X-v)G$, $\deg G\le r$, is injective by the root bound.
Hence the weighted discrepancies
$(W_i\delta_i(K))_{i\ne v}$ live in a subspace of dimension
at most $N-r-2$. All old terminal sites are disjoint from
$v$, so their primitive errors together have rank at most
$N-r-2$, irrespective of the number of strict central
entries or the rank of $V$. At least
$d=\max(0,t-(N-r-2))$ independent linear combinations of
actual old terminal means are therefore exact on every next
primitive letter. Each terminal mean was individually exact
through length $r$ and supported at a single clock, so
next multiplication letters are already exact before taking
combinations. The $d$ combinations are exact through word
length $r+1$. If $t\le r+1$, their evaluations are
independent on the degree-at-most-$r+1$ model space by
interpolation. If $t\ge r+1$, the degree-at-most-$r$ space
$V$ already vanishes on at least $r+1$ distinct clocks and
is zero, so all means pay the next grade; select $r+1$
independent evaluations rather than using an overcomplete list.

Apply the [paid commutator packet](../sdirk-nonhomogeneous-kernels/PAID-DONOR-BAND-MINIMUM.md)
to the **old** reverse word bank. It applies directly to
words: the physical commutator
$\Theta=CL-LC-L^2$ is invertible with diagonal $-1$, and its
formal polynomial action $XJ-JX-J^2$ is zero. Choose the
first block among clock monomials of degree at most $r+1$
to separate the refunded observations. The remaining blocks
are all monomials of degrees $<r,<r-2,\ldots$ carried by
successive powers of $\Theta$. In a relation separate the
leading block by its actual observations, divide by $\Theta$,
then separate the rest by the dense lower return. This
proves $s_r\ge L(r)+d$, where
$L(r)=\lfloor(r+1)^2/4\rfloor$, or
$s_r\ge L(r)+r+1$ in the saturated case. In the first case
the actual physical count is therefore
\[
   s_f+s_r+(N-t)-1\ge s_f+L(r)+r+1;
\]
in the saturated case the same follows from the existence
of the disjoint forward representative. These numbers are
$15+12+7=34$ and $11+9+6=26$.

The [native proof](../../lean/evidence/sdirk-grouped-terminal-refund-20261127/README.md)
checks clock injectivity, the annihilator dimension and exact
next-word payment, the paid four-block linear-independence
lemma, and both count specializations. This module is not
itself a Lean reconstruction of the algebraic stems or of
the ordinary rooted mixed-pairing derivation above.

## Scope and affordable changes to the model

For a protected **old reverse terminal** at $v$, this first rank
argument sees $t-1$, not $t$, of its old terminals. The
[protected-coordinate continuation](../real-sdirk15-overlapping-terminal/README.md)
uses that actual old coordinate to rule out equality as well
for these two stems. Different forward seeds, dropping the
whole-column payment in favor of signed cancellation, or
changing the physical bridge are not covered.

The signed-cancellation route has its own actual order
condition. Let $\mathbf h=(E_xJ-BE_x)Q$. For some size-$r+1$
tree its old discrepancy is a nonzero multiple of $Q$, and
its actual tail profile is locally pure. The unary attachment
with $r+1$ leaf marks pays the linear term from $\mathbf h$.
Putting two copies of that child at a common root at order
$2r+3$ consequently requires
$\sum_i b_i h_i^2=0$ on actual weighted stages, not on
aggregate means. In particular positive physical output
shares force whole-column payment on their support. Signed
physical shares evade that implication, not the quadratic
condition. The comparison leaves the archived real upper
endpoints unchanged.
