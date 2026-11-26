# Keeping prescribed output support, and when the earlier field grows

This addendum is separate from the exact higher-budget criterion.

## The supplied terminal rule need not be replaced

Let q_*=ceil(p/2). The real-algebraic width construction for a fixed
negative γ, or an order-dependent small or large positive γ, does not
need to change a larger prescribed terminal rule. Assume it already
has distinct real algebraic nodes and pays the degree-(p−1) moments.
Keep its q nodes and weights literally. At a nonterminal cut s with
ceil((2s−1)/3)<q_*, use the earlier orthogonality construction. At any
other nonterminal cut use a q_*-point Gaussian hull. This hull kills
every paid difference: after including the quotient and ancestor test,
the product with the hull has degree ≤p−1 and vanishes at its own
Gaussian nodes. Its rule is exact through degree p−1. No reference to
agreement with the supplied terminal nodes is needed. At h=0 use the
singleton as before. When D=p−1, the count equals the minimal-terminal
formula plus q−q_*. The caveat about allowing the added real algebraic
hidden-node coefficients still applies.

## A family forcing field enlargement at a robust cut

For infinitely many r≥3 we have an odd prime l=2r−1. Take p=2r,
D=p−1 and the penultimate cut d=1, hence s=2r−1 and b=r−2≥d
when using r nodes. Fix rational γ<0 and keep an existing rational
q=p−1 terminal rule that pays degree p−1 (for example the rational
rules from the published quadratic stage bound). Thus the old
full-column construction can remain over Q, and the attempted new
cut uses r instead of q=s nodes. Alternatively q=p arbitrary distinct
rational terminal nodes with cardinal weights give an elementary
signed exact rule without using that existence result.

For the new cut the exact local gate is the full unweighted
orthogonality through degree p−1−r=r−1. It forces the unique monic
shifted Legendre hull of degree r. This hull splits into distinct
interior real algebraic roots, but does not split over Q. Here is an
elementary proof for the chosen infinite family. The polynomial

    F_r(X) = (1/r!) (d/dX)^r [X^r(X−1)^r]
           = Σ_(k=0)^r (−1)^(r−k) C(r,k) C(r+k,k) X^k

has integer coefficients and constant (−1)^r. Repeated integration
by parts proves its orthogonality through degree r−1: every relevant
boundary term vanishes, and the r-th derivative of a lower-degree
test is zero. Its normalized monic version is therefore the forced
hull.

For k<r−1, C(r+k,k) is a unit at l because r+k<l. For k=r−1,r,
it has l-adic valuation exactly one because l≤r+k≤2r<2l
and k,r<l. The coefficients C(r,k) are all l-units as well.
Thus G_r(X)=(−1)^r X^r F_r(1/X) is monic integral with nonzero
constant of l-adic valuation one, and its reduction modulo l is
divisible by X² but not by X³. If G_r split over Q, all its roots
would be integers by monicity. Exactly two roots counted with
multiplicity would reduce to zero mod l. Their product, hence
the constant, would be divisible by l², a contradiction. Taking
reciprocals proves the claimed failure of rational splitting.

Therefore the same rational terminal rule can be retained, but this
robustly reduced internal cut really can require an extension beyond
the previous coefficient field. The example uses a larger rational
terminal rule and does **not** show that an extension is necessary
for every minimal-Gaussian-terminal implementation.
