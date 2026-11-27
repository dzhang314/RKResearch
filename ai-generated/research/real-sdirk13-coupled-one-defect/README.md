# Coupled one-mode payment at the real strict SDIRK13 frontier

An actual 25-stage common-diagonal tableau can pay the missing
size-six mode of the fixed 11-row forward prefix in its physical
tail. It has **order 12, not order 13**: the new coupling leaves a
strictly nonzero size-13 tall-tree defect. In fact, the two-terminal
mixed obstruction survives this coupling on any eight-site grid
with the specified forward prefix and reverse residual rank.
This is not a new unrestricted stage bound.

## The 11-row prefix and its one actual missing direction

Start with the [certified 12-row bank](../real-sdirk13-forward-ports/README.md)
and remove its last pure row at $w$, retaining the actual prefix ending
at the pure stage at $v$. Let $D_{11}$ read the old 11 stage columns
by substituting the original size-five decoder's value at $w$ for
the missing physical coordinate of the 12-row decoder $D_{12}$.
This is a literal linear read of the closed prefix. With $\boldsymbol\Phi_t$
the numerical rooted column and $P_t$ its exact polynomial, it decodes
through size five. Every size-six residual lies in $\operatorname{span}(Q)$,
where $Q$ has degree five and is obtained by the cross product of the
two actual size-six observation rows at $z,v$ on the original
three-dimensional error space. The functionals $E_zD_{11},E_vD_{11}$
are literally the two physical observations even above the paid cap.
Both $v$ and $w$ are roots of $(J-I)Q$, $Q(v)=0$, and $Q(w)\ne0$.

The exact branch replay factors $Q$ by its three known linear
factors at $z,v,\theta$. It brackets the real roots of the remaining
quadratic, if any, and proves no other real root of $Q$ kills $JQ$.
On the fixed eight-site geometry only the two advertised representative
clocks kill $(J-I)Q$. These are exact properties of the same algebraic
branch, not proximity to a sampled zero.

## The actual column payment and its completion identity

Use unit-diagonal coordinates, the forward sites $x_i$, reflected
sites $y_i=1/\gamma-x_i$, and scalar weights $\mathbf W$. The physical
reverse bank is $L$; $M$ takes actual site means, with individual
nonzero physical shares; $\Pi_r$ is the old reverse decoder. All but
the two paid terminal sites receive one new representative. Its
actual grouped rule is
\[
 ML=E_yJ\Pi_r+S(M-E_y\Pi_r),\qquad S=I+S_{\mathrm{str}}.
\]
The two old terminal means are already exact through reverse word
length five. The other rows of $M-E_y\Pi_r$ have distinct new physical
representative coordinates and are independent. For an off-diagonal
entry into a representative, the strict coefficient in $S$ is zero
unless that representative occurs earlier. The protected old forward
port at $v$ has no strict outgoing reverse coefficient on its
representative column. The forward tail $B$ is the reversed, weighted
transpose of this actual $L$.

Set $R(y)=Q(1/\gamma-y)$ and $R^*(y)=(JQ)(1/\gamma-y)$. The equality
$BE_xQ=E_xJQ$ is equivalent, by the actual weighted transpose and
the grouped rule, to
\[
 \sum_i W_i R(y_i)S_{ij}=W_jR^*(y_j)
\]
on each nonterminal representative column. The old-decoder
terms cancel by the scalar quadrature and integration by parts:
$J$ raises degree by one and the reverse lower return has degree
at most four. Thus all moments used are within precision twelve.
The terminal columns have zero contrast. In particular, the latest
nonprotected representative $t$ must satisfy $(J-I)Q(x_t)=0$:
any later protected representative is at $v$, where $Q(v)=0$.
Since $x_t\ne v$, the common-root test gives $Q(x_t)\ne0$.

After transferring the literal $v$-representative into the old
$v$ row, the earliest unprotected forward row at $x_t$ has no
other earlier suffix input. Its actual strict row is
$E_{x_t}(J-I)D_{11}$, even if it could have read the transferred
$v$ row: the redirected coefficient cancels against
$E_vD_{11}$. Moving this physical row into the closed prefix
completes the decoder by
\[
 D_{\rm new}=D_{11}+\frac{Q}{Q(x_t)}(e_t-E_{x_t}D_{11}).
\]
For every remaining forward row $i$, deleting the $t$ column
from its tail feed leaves left-hand polynomial coefficient row
$\ell_i=E_{x_i}J-\sum_{j\ne t}B_{ij}E_{x_j}$.
The paid column says $\ell_i(Q)=B_{it}Q(x_t)$, so using
$\ell_iD_{\rm new}$ is literally the same physical feed.
This is a row identity, not a change to numerical stages.
[Lean checks this algebra](../../lean/evidence/sdirk13-coupled-one-defect-20261127/README.md).

## The mixed obstruction is necessary on actual rooted contexts

For a tree $t$ write $H_t=P_t-D_{11}\boldsymbol\Phi_t^{\rm old}$
and let $\mathbf e_t$ be its actual tail error. A unary attachment
gives
\[
 \mathbf e_{[t]}=B\mathbf e_t-(E_xJ-BE_x)H_t.
\]
A leaf mark at the existing root multiplies this error by the
physical clock diagonal. The coupling kills every incoming
size-six error and all smaller errors are zero. Root induction
therefore gives actual tail purity through size seven.

With size at most thirteen there can be only one imperfect
primitive child (its size is at least seven); other child
primitives are exact clock powers. Thus any output error decomposes
into a single-spine sum of the unary sources above, transported
by words in the tail matrix and clock diagonal. Under weighted
transpose, the reflected words with length at most four have
both their site profiles and their next primitive exactly paid.
Scalar quadrature and integration by parts cancel all these
sources. This proves all order conditions through size twelve.

For necessity at order thirteen, choose any actual size-seven
tree $t$, attach one unary root, and then any word of five
unary attachments or leaf marks. Of the resulting sources,
only the first one can have five exterior letters; later sources
have at most four and have already canceled. The first source
tests exactly the mixed bilinear form with $H_t$ and the actual
size-five-word residual $K$ returned by $\Pi_r$. Reversing
the clock letter uses the affine identity between $x$ and $y$;
lower word terms have already been paid. Consequently ordinary
order thirteen of this architecture would imply
\[
 \sum_iW_iH(x_i)\big[(SE_y-E_yJ)K\big]_i=0
\]
for all actual $H$ in the size-seven error span and $K$ in the
reverse top residual span. This is a necessary test on actual
rooted contexts, not just a sufficient template for construction.
The additional direction $Q$ is also tested at zero because its
entire incoming column response is zero.

The span of the forward size-seven errors together with $Q$ is
**all** degree-at-most-six polynomials vanishing at $v$. To
see this, project along $Q$ by imposing vanishing at $w$.
The projected space is exactly the certified rank-five size-seven
residual of the 12-row completion, and the kernel is the missing
line. Take the degree-six polynomial vanishing at every
nonterminal site (including the protected forward site). This
is therefore an allowed test. It kills the whole central term
except at the two separately paid reverse terminals $a,b$.
When the reverse residual rank is four, its space is all
degree-at-most-five polynomials vanishing at $a,b$. The two
tests $(X-a)(X-b)$ and its first clock mark overdetermine the
remaining two primitive payments by the
[exact determinant](../../lean/evidence/sdirk13-two-terminal-20261127/README.md).
If either terminal is zero, its primitive vanishes, and the
quadratic test has nonzero primitive at the other terminal.
The two scalar prefactors are nonzero because both weights
are nonzero and the forward hull omits exactly those sites.

This excludes this fixed 11-row prefix in the stated grouped
coupled architecture on any eight-site companion with two
disjoint paid terminals and rank-four reverse top residual.
It does not exclude a reverse redesign having an extra paid
high functional (rank three), a different forward prefix, or
a fundamentally different ordinary tableau.

## Literal 25-stage below-order-13 replay

On the joined-interface grid, take the same actual nine-row
reverse bank. Order the distinct new representatives with $w$
last among the nonprotected and $v$ last overall. Use only
$S_{{\rm str},w,j}$ to pay the missing-mode column, dividing by
$W_w Q(w)$, with the already zero columns at $v,w$ unchanged.
Build all physical strict rows, take the actual weighted transpose,
then redirect the whole strict duplicate of $v$ into the old
forward $v$. This gives $11+9+6-1=25$ physical rows and nonzero
common diagonal $\gamma$. The exact interval replay separates a
size-13 tall-tree defect with absolute value at least one in the
normalized readout, and independently checks all 7,813 ordinary
rooted profiles through size twelve. The analytical argument
above gives the exact lower order; equality is not inferred
solely from intervals containing zero.

```sh
# From this directory, with the two previous packets as sibling directories.
join="$PWD/../real-sdirk13-joined-interface"
work="$(mktemp -d)"
python3 "$join/refine_ports.py" "$work"
python3 check_coupled.py "$work" "$join" --full
```
