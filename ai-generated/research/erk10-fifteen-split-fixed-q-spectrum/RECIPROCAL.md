# A true nonlinear exclusion for an entire rational late slice

In the fixed-\(q\) split host ordinary-pair
geometry, set the normalized reverse clocks
\[
                       c=1/2,\qquad g=2/3,\qquad R=1/4 .
\]
Then **no solution exists for any rational
\(d,e,a,b\)** compatible with the actual guards,
not merely for a selected grid of head clocks.
The exclusion is a one-slice theorem, not a
general rational fifteen-stage lower bound.

## Eliminate the physical pair and the host from the residual

Use the exact head reduction in
[HEAD-SYMMETRY.md](HEAD-SYMMETRY.md).
Put \(\widehat A_0=\widehat A/\tau\),
where \(\tau=de\ne0\).
It is an affine polynomial depending on
\(c,g,R\), not on the head clocks.
For this slice the true rational values are
\[
 h=19/20,\quad f=22/39,\qquad
 \widehat A_0(y)=-337/5241600+(1909/15724800)y .
\]
In particular \(A(1)\ne0\) is forced.
There are no zero-score ordinary singletons
other than \(R\): if \(u_z\ne0\),
\(w_z\eta_z=Q(z)u_z\) and the only possible
roots of the nonzero \(Q\) are \(R,1\).
If \(u_z=0\), the simultaneous score zero
was already excluded by the rational
[Jacobi argument](../erk10-fifteen-split-host-weighted/README.md#the-unscored-host-necessarily-has-nonzero-grade-two).
This is why a reciprocal score calculation
is legal in this slice.

Let \(D_7\) denote the monic polynomial on
\(a,b,d,e,f,g,h\), and \(F=(y-c)(y-R)D_7\).
The ten-site scalar polynomial is
\(\mathscr P=y(y-1)(y-c)D_7\);
let \(\mu_z=I(\mathscr P(y)/(y-z))\)
at each of these seven sites.
All \(\mu_z\ne0\) by the actual score guard.
We have \(u_z=\lambda\widehat A_0(z)/[(1-z)F'(z)]\)
for a single nonzero scale \(\lambda\), and
\(Q(y)=q_0(y-R)(1-y)\) with \(q_0\ne0\).
The cardinal weight formula and \(w_z\eta_z=Q(z)u_z\)
then give
\[
                  \eta_z=-\lambda q_0\,
                      \frac{z(1-z)\widehat A_0(z)}{\mu_z}.
\]
The actual four \(\boldsymbol\eta\)-pairings
against \(\boldsymbol u{\cal P}_3\) imply
\[
      \sum_i (y_i-c)(y_i-R)y_i^j\eta_i u_i=0
                                     \qquad(j=0,1).
\]
The factors kill both physically repeated
\(c\)-rows and the unscored host, so after
cancelling \(-\lambda^2 q_0\ne0\) they yield
\[
      \sum_{z\in\operatorname{roots}(D_7)}
             \frac{z^{j+1}\widehat A_0(z)^2}
                        {\mu_z D_7'(z)}=0
                                     \qquad(j=0,1).       \tag{1}
\]
This is a nontrivial consequence of the
genuine nonlinear rooted contact; it is not
just a scalar quadrature condition.

Represent the cardinal masses by the
polynomial \(\widetilde\mu(y)\) of degree
at most six
\[
 \widetilde\mu(y)= I_z\!\left[
        z(z-1)(z-c)\frac{D_7(z)-D_7(y)}{z-y}\right].
\]
It equals \(\mu_z\) at the actual scalar
nodes, so is invertible modulo \(D_7\).
For \(U=\mathrm{rem}_{D_7}(y\widehat A_0^2/
\widetilde\mu)\), the first equation (1)
kills its degree-six coefficient by the
seven-site divided difference. Then the
second equation kills the degree-five
coefficient (multiplication by \(y\)
needs no further reduction now).
Therefore the true residual forces an
actual polynomial \(U\) of degree at most
four with
\[
                     U\widetilde\mu
                          \equiv y\widehat A_0^2\bmod D_7. \tag{2}
\]

## Exact rank certificate for all rational inner clocks

The primitive determinant of the symmetric
head solve is the following quadratic
(up to nonzero scale):
\[
        \Delta=75070945\tau^2+19738654\tau-1418496 .
\]
Its discriminant \(815565802526596\) is
strictly between \(28558112^2\) and
\(28558113^2\), so no rational pivot-zero
branch remains. This is the determinant of
the two actual independent columns; it is
not the identically vanishing three-row
consistency determinant.
Consequently the roots \(a,b\) have the
prescribed rational sum and product as
functions of \(\tau\), and the pair \(d,e\)
has sum \(c-\omega\tau\), product \(\tau\).
No rational splitting assumption is used
to compute the following coefficient
minors, though a true candidate would
of course have these rational roots.

Use the coefficient columns in \(y\) of
\(\widetilde\mu,\ y\widetilde\mu,\ldots,
y^4\widetilde\mu\bmod D_7\) and \(y\widehat A_0^2\).
Equation (2) forces all seven \(6\times6\)
minors of this \(7\times6\) matrix to vanish.
They are computed without any rational-function
inversion. Set \(D_{\rm num}=\Delta D_7\),
\(U_0=\Delta\widetilde\mu\); recursively take
\[
       U_{i+1}=\Delta y U_i-[y^6]U_i\, D_{\rm num},
                   \qquad 0\le i<4 .
\]
Then \(U_i\) is exactly \(\Delta^{i+1}\)
times the indicated reduced column, and
has degree at most six in \(y\).
The companion last column is already literal.
Nonzero constant normalizations of \(\Delta\)
have no effect on the rank test.

The exact minor gcd over \(\mathbb Q[\tau]\)
has degree \(23\). Removing powers of the
rationally rootless pivot (and any zero-clock
factor \(\tau\)) leaves precisely the primitive
cubic
\[
\begin{split}
  &107600091571325\tau^3-32692496039640\tau^2\\
  &\hspace{35mm}-4342746664868\tau+362024293632 .
\end{split}
\]
Its projective residue is
\(2a^3+5a^2b+12ab^2+b^3\) modulo \(13\),
with no nonzero projective root, including
the class at infinity. Hence there is no
rational \(\tau\), contradicting the
necessary true nonlinear residual (2).
The gcd and the two scalar arithmetic
gates are each independently replayable.

## Replay and native scope

    python3 -B reciprocal.py | diff -u reciprocal-audit.txt -

From an overlay or repository root:

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10SplitReciprocalScalars.lean

The two native core checks concern the
integer discriminant bracket and the
finite projective cubic only. The exact
minor GCD and algebraic tableau implications
are mathematical/replayed, not a native
end-to-end Lean exclusion.

## Seven additional exact slices

The same reciprocal rank proof closes seven further
rational triples, all with \(A(1)\ne0\) and with
no rational root of their respective head pivot:

| \(c\) | \(g\) | \(R\) | Last rational \(\tau\) from the reciprocal minor GCD |
|---|---|---|---|
| \(1/2\) | \(1/4\) | \(2/3\) | none |
| \(2/3\) | \(1/2\) | \(3/4\) | \(489/4342\), forcing \(ab=0\) |
| \(2/3\) | \(3/4\) | \(1/2\) | \(1137/10690\), forcing \(ab=0\) |
| \(1/2\) | \(1/3\) | \(2/3\) | none |
| \(2\) | \(1/2\) | \(3/4\) | none |
| \(-1\) | \(1/2\) | \(3/4\) | none |
| \(-2\) | \(-1\) | \(1/4\) | none |

Here the possible product-zero survivors cannot
be present, since neither earliest ordinary clock
is the endpoint \(0\). Their rejection uses
the exact two-row rational solve, not a height
bound. Replay all eight slices with

    python3 -B multi_reciprocal.py | diff -u multi-reciprocal-audit.txt -

The separate [29-adic map](RESIDUE-29.md) broadens
the center slice to a full rational residue class.
