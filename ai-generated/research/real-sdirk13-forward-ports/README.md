# Two physical forward ports for the real strict SDIRK order-13 frontier

An explicit real-algebraic 12-stage lower triangular common-unit-diagonal
tableau decodes the complete ordinary derivative polynomial through tree
size six. Its last two actual rows are individually exact through size
seven, at clocks $v=7.1035943079931809704\ldots$ and
$w=0.2641004031625698958\ldots$. The preceding observation is actually
exact through size six at $z=0.3316872447846752020\ldots$.
Twelve is the general dense-decoder lower bound
$\lfloor(6+1)^2/4\rfloor$. This is a **forward bank**, not an order-13
tableau or an improved unrestricted upper bound. A compatible scalar
rule and a causally paid reverse bank at the same input are still needed.

## The nine-row closed prefix

Work with common diagonal one. Let $Jf(X)=\int_0^X f(Y)\,dY$,
$T=J-\mathrm{Id}$, and $W_k=k!T^k1$ (the monic Laguerre polynomials).
Let $D_5$ be the [minimum cache](../sdirk-nonhomogeneous-kernels/DENSE-POLYNOMIAL-DONOR-MINIMUM.md)
at cap five, physical widths $(1,2,3,2,1)$. Select the second and third
increasing roots $\alpha,\beta$ of $W_4$, and the second root $\theta$
of $W_5$. All physical rows are reconstructed in the replay.
Write $P_t=X^{|t|-1}$ for the model of the normalized rooted column
$\boldsymbol{\Phi}_t$, and $E_x$ for evaluation at $x$.

At size six, every old error $P_t-D_5\boldsymbol{\Phi}_t$ belongs to
\[
 U=\operatorname{span}\{W_5,Q_5,\widetilde Q_4\},\qquad
 Q_4=W_1+aW_2+bW_3,\quad Q_4(\alpha)=Q_4(\beta)=0,
\]
where
\[
 Q_5=W_3-\frac{W_3(\theta)}{W_4(\theta)}W_4,\qquad
 \widetilde Q_4=Q_4-\frac{Q_4(\theta)}{W_4(\theta)}W_4.
\]
Indeed, up to layer three there is no caching. At layer four the
actual and nominal samples agree at size six because all strict child
data agree through size five, and the self coefficient separately
uses smaller child trees. By the [nominal error band](../sdirk-nonhomogeneous-kernels/CAUSAL-RECEIVER-CUT-AND-MINIMAL-CACHE.md)
only the cached $W_1$ coefficient can first differ at size six. The
difference vanishes at the two actual samples and so is a multiple of
$Q_4$. At layer five the nominal error is a multiple of $W_5$.
Only the cached $W_3$ can newly differ there; its contribution and
the inherited $Q_4$ must each be lifted to vanish at the actual last
sample $\theta$. The sole high mode $W_4$ gives the two displayed
lifts. This proves the error-space inclusion independently of numerical
rank. The first-excess bound $9+\dim U\ge12$ shows this size of
error space cannot be avoided at the nine-stage cost.

## Three actual chronological rows

Put $\mu_x=E_xT$. Give each appended stage its own diagonal one.
If a marked stage at $x$ has been computed, write
$\boldsymbol{\eta}_x$ for its actual unit observation minus
$E_xD_5$ on the old nine rows.

1. Append at $z$ using strict row $\mu_zD_5$. It is actually exact
   through size six by induction on children.
2. At $(v,z)$ the exact two polynomial equations give
   $\mu_v|_U=\lambda E_z|_U$, with separated pivot $E_z(W_5)$.
   Append at $v$ using strict row
   $\mu_vD_5+\lambda\boldsymbol{\eta}_z$.
3. Let $Q$ span $U\cap\ker E_z\cap\ker E_v$; it is produced by the
   cross product of their two evaluation rows. The isolated root $w$
   of $\mu_wQ$ has $Q(w)\ne0$. Thus
   $\mu_w|_U=\rho E_z|_U+\sigma E_v|_U$.
   Append at $w$ using
   $\mu_wD_5+\rho\boldsymbol{\eta}_z+\sigma\boldsymbol{\eta}_v$.

For either of the last two rows the correction evaluates the exact
old model discrepancy against its shifted primitive for every child
of size at most six. The separate unit diagonal supplies the missing
identity term. Induction on the rooted constructor now proves
actual size-seven local exactness. The evaluation rows at $z,v,w$
are invertible on $U$; applying their inverse to the three actual
signed contrasts and adding the result to $D_5$ returns all
polynomials through size six. The [Lean package](../../lean/evidence/five-ladder-thirteen-20261127/README.md)
checks the reusable paid-jet append and residual-image payment
theorems. It does not assert a native check of this instantiated
real-algebraic bank. Multiplying the stage matrix and all its clocks
by any nonzero real-algebraic common diagonal rescales the polynomial
decoder and preserves these local sizes.

## Exact algebraic certificate

Run `python3 check_two_ports.py`. It uses only standard-library
Python and outward 256-bit dyadic intervals. The Laguerre roots and
the final one-variable root have strict rational sign brackets
and nonvanishing derivatives. For $(v,z)$ an exact dyadic matrix
$L$ preconditions the two polynomial equations; the verifier proves
$(v,z)\mapsto(v,z)-L\mathbf F(v,z)$ is a strict self-map and
contraction on a rational square. Uniformity over the enclosed
Laguerre parameters is checked. The fixed point solves both original
equations. Its nonzero Jacobian proves an isolated real-algebraic
solution (equivalently, apply real-closed-field transfer inside the
rational box). Every actual coefficient and all 85 ordinary
rooted profiles through size seven are additionally reconstructed
in directed intervals. The exact identities follow from the
analytical proof above, not from residual containment alone.

## Why the simpler five-new-pivot lift cannot give 25

In a two-order order-11 to order-13 Newton lift with cutoff $q=7$,
five pivots add exactly five new rows only if all earlier virtual
rows are literal copies of old stages paid through size eight.
The unrelaxed tail prescribes reflected sites $(2i-1)\gamma$,
$i=1,\ldots,5$. The [characteristic-zero Lean certificate](../../lean/evidence/five-ladder-thirteen-20261127/README.md)
excludes seven-site precision 12 with all five prescribed. In
fact the monic hull $F_5$ of the ladder and the remaining monic
quadratic $H_2$ would satisfy $I(F_5H_2X^j)=0$, where
$If=\int_0^1 f(X)\,dX$. The two 3-by-3 Hankel minors at row sets
$(0,1,2)$ and $(0,1,3)$ have an exact integer Bézout identity with
nonzero constant. Over the reals the square of the nodal hull
excludes fewer than seven contributing sites. Thus the unrelaxed
lift needs $h\ge3$ distinct copied head sites.

The four old moments $I(X^j\,\cdot)$, $j=0,\ldots,3$, and evaluations
at the $h$ head sites have combined rank at least seven on degree
at most seven. For $h\ge7$ this is direct. Otherwise the moment
polynomial $Q$ of any linear dependence has degree at most three
and annihilates $H_h X^i$ for $0\le i\le7-h$, where $H_h$ is
the head hull. By the full precision-12 rule this is a Vandermonde
test of rank $8-h$ on the five pivot sites after multiplying
by their nonzero factors $w_aH_h(x_a)$. Evaluation at those
five sites is injective on $Q$. The head coefficients are uniquely
determined by $Q$, so dependence has dimension at most
$5-(8-h)=h-3$, and the combined rank is at least seven.

This rank is paid on the actual size-eight prefix inputs (old
order eleven pays the four weighted moments). Apply the
commutator tower at size caps $12,10,8,6,4,2$ with ranks
$0,2,7,6,4,2$. In a relation among
$\Pi^j P(C)\mathbf 1$, divide by the least power of the invertible
$\Pi=CA-AC-A^2$ and apply that level's probes; all positive
commutator powers have zero model since $XJ-JX=J^2$. This forces
at least **21 actual old stages**, not at most 20. The one-spare
version needs the entire size-eight decoder and hence at least
22 old rows. These are restrictions of the five-pivot architectures,
not new lower bounds for arbitrary order-13 SDIRK methods.
