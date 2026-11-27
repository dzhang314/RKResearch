# Joining the two-port forward bank to a paid reverse interface

The previous [12-row forward bank](../real-sdirk13-forward-ports/README.md)
has two actual size-seven pure rows. We certify an eight-site scalar rule
meeting both rows and an actual nine-row reverse bank with two exact
terminal means on the same input. This pays the scalar, lower forward,
and lower reverse parts of a putative 25-stage order-13 bridge. The
actual top mixed condition is **nonzero**, so this is **not an order-13
witness and does not change the upper bound**.

## The seven-site obstruction

A real seven-site rule integrating polynomials through degree 12
has monic hull proportional to $P_7+tP_6$, where $P_j$ are shifted
Legendre polynomials. For the usual reverse arithmetic progression
$\gamma,\gamma+d,\gamma+2d$ with $d\ne0$ as its first three labels, put
\[
 F(g,x)=\frac{P_7(x)P_6(g)-P_7(g)P_6(x)}{x-g}.
\]
The two needed polynomial identities are $F(g,g+d)=0$ and
$[F(g,g+2d)-F(g,g+d)]/d=0$. Their exact resultant in $d$ has degree 96
in $g$; removing the inadmissible factors with $P_6(g)=0$ or $g=0$
leaves the degree-90 necessary polynomial. Adjacent Legendre
polynomials have no common root, so this removal is legitimate.
Exact Sturm isolation and independent interval evaluation on all
42 real candidate boxes exclude **either** certified forward port:
neither reflected label $1-gv$ nor $1-gw$ passes the full undivided
cross-polynomial test. This also excludes a coincident label. The
absolute bounds for both tests are at least $2^{-7}$. The alternative
initial bank at $\gamma$ and the two scaled quadratic Laguerre roots
is excluded even without a forward port: the corresponding two
polynomials in $\gamma$ are coprime over $\mathbb Q(\sqrt2)$.
These are tests of these reverse starts, not of every possible
seven-site rule.

## Genuine matching scalar and reverse rows at eight sites

Take $\gamma=1/(1+v)$ and $h=1-\gamma w$ so that the first reverse
clock $\gamma$ and $h$ are the reflected physical labels of the two
true forward rows. Isolate $d\approx-0.02880497$ by the four-node
determinant in the columns $P_5,P_6,P_7,P_8$ at
$(\gamma,h,\gamma+d,\gamma+2d)$. Invert the three lower columns
on the first three of those nodes; the resulting degree-eight
hull $P_8+\lambda_7P_7+\lambda_6P_6+\lambda_5P_5$ also vanishes at
the fourth, by the exact determinant equation. Isolate all other
roots in separated intervals. Interpolatory cardinal weights
give precision 12 by polynomial division and orthogonality to
degree at most four. Every weight is nonzero, one is negative,
and $\lambda_5\ne0$ proves failure at degree 13 by testing the
hull times $P_5$.

Use increasing physical mesh labels $0,\dots,7$ and scale those
clock values by $1/\gamma$ to build the unit-diagonal reverse
matrix $L$. Its first seven rows have clocks with labels
$(3,2,1,4,5,6,7)$. Define
\[
 \mathbf g=L\mathbf c-\mathbf c^2/2,\qquad
 \mathbf d_k=L\mathbf c^{k-1}-\mathbf c^k/k,\qquad
 H=\operatorname{diag}(\mathbf c).
\]
The first three points form an exact arithmetic progression;
the construction imposes $L\mathbf g=\mathbf g+(H-I)\mathbf g/\eta$
with $\eta=g_2/g_1$ (one-based). Substitution of those first
three rows gives $\mathbf d_3=(2/3)(L+H)\mathbf g$ there; subsequent
rows impose that identity by a linear solve. At degree four impose
$\mathbf d_4\in\operatorname{span}(\mathbf g,H\mathbf g,
H^2\mathbf g,LH\mathbf g)$, with its coefficients fixed by the first
four rows. These are all error directions: at each next word
length, the letters $L,H$ apply $L,H$ to the previous pure
directions, and $L$ on the exact monomial additionally creates
$\mathbf d_k$. This proves the claimed all-word closure through
length four. Linear elimination against the first four defect
rows therefore gives three exact signed observations
$\psi_5,\psi_6,\psi_7$ of polynomial profiles through degree four.

The sixth row has a free physical tap $f$; $\psi_6(f)$ is affine.
The seventh row has two free taps. Use prospective terminals
$a=y_6$, $b=y_4$, and $\mu_x=E_x(J-I)$. First set $f$ by the
affine determinant
\[
 \det(\psi_5,\psi_6(f),\mu_a,E_a,\mu_b)=0
\]
on degree at most four. Then choose the two seventh-row taps by
an invertible 5-by-5 linear system making its observation a
linear combination of $\psi_5,\psi_6,\mu_a$ with nonzero
$\mu_a$ coefficient. The replay checks all ranks and denominators.
Thus $\mu_a$ is in the true old three-row observation span and
$\mu_b$ is in that span plus $E_a$.

At site $a$ append a row whose strict part is twice the available
coefficient row for $\mu_a$ minus the previous physical strict
row at $a$, padded chronologically. With its separate unit
diagonal, the two true occurrences have arithmetic mean
$\mathbf m_a$ with $\mathbf m_aH=a\mathbf m_a$ and
$\mathbf m_a L=\mathbf m_a+\boldsymbol{\theta}_a$. Induction on
the actual reverse words proves mean evaluation through length
five. Repeat at $b$, now able to use $\mathbf m_a$. These are
nine actual rows, not nine virtual scalar functionals. The five
clean observations are invertible on degree at most four and
give the dense lower reverse decoder. The replay also checks
all 63 words through length five.

Changing the split between the two actual occurrences at each
terminal does not change the top residual on this architecture.
With two nonzero shares the same weighted mean equation determines
the new physical strict row. The first seven word data remain
unchanged, and the two exact mean responses to all words through
length five are independent of that split. The five observations
used by the lower reverse decoder therefore give the same
top residual. Free terminal reweighting is not a hidden fit parameter.

## Why the physical count does not yield order 13

With two old terminal means, adding a representative to each
of the other six sites and merging the two true forward rows
would cost $12+9+6-2=25$. That counting is conditional on
the actual mixed error equation. Here the forward first-excess
space $U$ has exact rank five (all degree-at-most-six polynomials
vanishing at the two forward marks). The reverse first-excess
space $V$ has exact rank four (all degree-at-most-five polynomials
vanishing at $a,b$). Exact nonzero minors in the replay give
the lower ranks, and the actual forward and reverse purity
give the matching upper ranks.

Choose the monic degree-six polynomial in $U$ that vanishes
at all six nonterminal forward labels. The two forward
protected labels are among its roots. This test kills all four
physical central correction rows, even allowing noncausal
entries there. What remains of the required mixed test is
\[
 u(JK)(a)+v(JK)(b)=0 \quad(K\in V),
\]
where $u,v$ are nonzero (the actual scalar weights times nonzero
values of the six-root polynomial). The pairs $K=(X-a)(X-b)$
and $XK$ have primitive determinant $a^2b^2(a-b)^3/24$, nonzero
here. This is independently checked in [Lean](../../lean/evidence/sdirk13-two-terminal-20261127/README.md).
The actual replay also finds a concrete reversed word whose
terminal-only mixed witness has absolute value at least $2^{22}$
in these normalized units. This failure does not depend on
which of the four correction rows is paid first. Reducing
the dimension of either top residual or changing the construction's
support may avoid it; arbitrary strict SDIRK tableaux are not
excluded by this argument.

## Exact finite census of this reverse architecture

On this same eight-site rule, vary the order of the four last old bank
labels over four-element permutations from the five labels not in the
initial progression. At each ordering, try every ordered pair of
distinct earlier terminal labels not among the two protected forward
sites. These are 2,640 physical choices. For each, the exact dyadic
census verifies the arithmetic sections, constructs the actual nine
rows, certifies reverse top residual rank four and obtains a strictly
nonzero terminal-only mixed witness. There were no unseparated
pivots or unresolved candidates. This covers the stated equations
on this scalar geometry, not arbitrary reverse tableaux or
other eight-site quadratures.

## Replay

```sh
# From this directory. SymPy is needed only for the exact seven-site elimination.
python3 check_ap_port.py
work="$(mktemp -d)"
python3 refine_ports.py "$work"
python3 check_reverse_bank.py "$work"
# Optional: whole exact census (about eight minutes on the recorded machine).
python3 exact_census.py "$work"
```

The refinement stages a scratch copy of the unchanged parent
checker with 235-digit rational centers on the exact same branch
and narrower boxes. It re-proves every root inclusion. Its decimal
centers are not used as exact real algebraic coordinates. Both
eight-site and nine-row checks use only directed integer dyadic
arithmetic after that point. The archived high-precision centers
can be regenerated numerically if desired, but no numerical
solver is needed for certificate replay.
