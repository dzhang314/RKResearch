# Complete mod-29 projective census for a nonlinear ERK10 split-host chart

This is a census of **necessary modular conditions**
for rational width-eleven raw split-host data with
the sole ordinary pair and the earned reverse head
\(0,a,b,c,c,d,e,f,g,h,R\). It uses the exact
[fixed-q spectrum framework](../erk10-fifteen-split-fixed-q-spectrum/README.md),
but its nonexistence conditions are common necessary
data for either old host. The actual existence
example is specifically the fixed-\(q\) constructor;
no new result is asserted for the free-contact \(p\)
opening itself.

All \(30^3=27{,}000\) outer triples \((c,g,R)\)
in \(\mathbb P^1(\mathbb F_{29})^3\) are covered.
Every internal clock/projective head denominator
case is retained, rather than treating poles as
nonzero affine residues. If a moment quotient has
indeterminate reduced numerator and denominator,
all possible projective residues are enumerated.
The other arithmetic is exact mod \(29\).

The resulting map rules out **15,369** outer
projective triples in both affine-cofactor branches,
including **14,385** fully finite outer triples.
The remaining outer triples are split, by
priority, into four disjoint cases: a regular
fully finite distinct scalar geometry; a finite
distinct geometry only with arithmetic losses;
no finite distinct geometry but a projectively
distinct survivor requiring a pole; or only
collisions and lost scales. The exact log
gives branchwise counts as well. A surviving
residue is not asserted rationally liftable.
In fact one regular survivor was reconstructed
as a literal exact [fixed-q F29 tableau](../erk10-fifteen-fixedq-f29/README.md)
and has a separate [all-power lift](../erk10-fifteen-fixedq-29adic/README.md).
Thus no total mod-29 or 29-power exclusion
is possible in this architecture.

## Primitive projective clock data

Write \(c=C/D,\ g=G/G_D,\ R=R_N/R_D\), each
with primitive integer numerator and denominator.
For any such coordinate \(z\), let
\(P_z(y)=z_Dy-z_N\). This is a nonzero
rational multiple of \(y-z\) before reduction.
Use \(M^*=y^2P_c^2\); the two late quotients are
\[
 h=\frac{I[y(1-y)JM^* P_g P_R]}
         {I[(1-y)JM^* P_g P_R]},\qquad
 f=\frac{I[y(1-y)M^*P_gP_hP_R]}
         {I[(1-y)M^*P_gP_hP_R]}.
\]
When both moments in a ratio reduce to zero,
the quotient may reduce to any projective
point; all 30 are tested. This handles
outer poles using primitive linear forms.
Every formal moment here or below has
denominator at most 14, a 29-unit.

Set \(T_3^*=P_fP_gP_h,\ S^*=(1-y)P_gP_hP_R\),
and
\(\Omega=210 C^3-336 C^2D+168 CD^2-28D^3\).
For primitive \([\tau_N:\tau_D]\) with \(\tau=de\),
the inner pair polynomial has exact clearing
\[
 P_{de}^*=\tau_D D^3 y^2+
               (-\tau_D C D^2+\tau_N\Omega)y+\tau_N D^3 .
\]
It can reduce to zero if all its coefficients
lose scale; this case is specifically retained.
For the head use \([s:p:z]\in\mathbb P^2\)
for \(s_h=a+b,\ p_h=ab\) (actual rational
normalization \([s_h:p_h:1]\)), and
\(P_{ab}^*=zy^2-sy+p\).
Both quadratics must split projectively:
use the homogeneous discriminant-square test.
It permits coincident roots, one root at
infinity, or both roots at infinity.
A rational factorization of a primitive
quadratic reduces to a projective split.
No rational distinctness is replaced by
distinctness after reduction.

## Cleared head solve and cofactor

Define
\[
\begin{aligned}
 W^*&=y(y-1)P_c T_3^*P_{de}^*,&
 E_0^*&=I(W^*),& E_1^*&=I(yW^*),\\
 k^*&=I(y(y-1)P_c^2P_R T_3^*),&
 J^*&=I(S^*P_f\,yP_c [D^3+\Omega y]).
\end{aligned}
\]
The first exact head row on \([s:p:z]\) is
\[
\begin{split}
 &E_0^* R_N C^2-2\tau_N C D^3 k^*,\\
 &-E_0^* R_N CD-E_0^*R_D C^2+E_1^* R_D CD
                       +4\tau_N D^4 k^*-\tau_N CD\,J^*,\\
 &-E_1^* R_N C^2+\tau_N C^2 D^2 k^* .
\end{split}
\]
The other head row is
\((-I(y\Phi^*),I(\Phi^*),I(y^2\Phi^*))\), where
\[
 \Phi^*=(y-1)P_c P_{de}^*
   [\,T_3^*(0)V_c^*(y)-V_c^*(0)T_3^*(y)\,],\qquad
 V_c^*=D^3 V_c .
\]
There is no division by \(T_3^*(0)\).
At rank two use the cross product of these
rows; at rank zero or one enumerate the
whole projective kernel. The exact symbolic
audit checks the common scales in the first row.

The exact head cofactor \(A_0=\widehat A_0\)
has the polynomial multiple
\[
 \mathcal A(y)=C D^2 k^*+(C J^*-2D^3k^*)y .
\]
Its scale is nonzero before reduction.
If \(\mathcal A(1)\) has nonzero residue,
the exact origin-root branch is impossible.
Otherwise both the exact origin-root
case and the possible reduction of a
generic \(A(1)\ne0\) case are tested.
A lost affine scale \(\mathcal A=0\)
is retained.

## Nonlinear ranks without actual reciprocals

Let \(\mathcal D=P_{ab}^*P_{de}^*T_3^*\);
over \(\mathbb Q\) it is a nonzero
multiple of \(D_7\) on \(a,b,d,e,f,g,h\).
Interpolate \(\boldsymbol\eta\) at its
seven true singleton sites by
\[
                      U(z)=-\eta_z A_0(z)/(1-z).
\]
The two true tests against
\((y-c)(y-R)\boldsymbol u\) and its mark
force the coefficients of degrees six
and five of \(U\) to vanish by the
seven-site Vandermonde. Hence \(\deg U\le4\).
No inversion of any score is used.

The actual scalar cardinal relation and
\(\boldsymbol w\odot\boldsymbol\eta=Q\boldsymbol u\)
give congruences modulo \(D_7\):
\[
 \begin{array}{ll}
 U\mu=\lambda\,yA_0^2,& A(1)\ne0,\ \lambda\ne0,\\
 U\mu=y(1-y)(q_0+q_1y),& A(1)=0,\
                                      (q_0,q_1)\ne(0,0).
 \end{array}
\]
Here \(\mu\) is the true cardinal polynomial
on the seven sites. These equations are
valid at zero scores: after factoring
\(Q(y)=(y-R)Q_1(y)\), the cleared equation is
\(\mu_z\eta_z=-zA_0(z)Q_1(z)\) up to common scale.
Multiply by \(-A_0(z)/(1-z)\).
In the generic branch \(Q_1\) is proportional
to \(1-y\); in the origin branch \(A_0\) is,
which cancels the denominator.

For a divisionless representation let
\(J_j(y)=I_x[x(x-1)P_c(x)x^j
(\mathcal D(x)-\mathcal D(y))/(x-y)]\).
The five coefficient columns
\[
       V_j(y)=J_j(y)-
         \sum_{i=0}^{j-1}y^{j-1-i}
                   I_x[x(x-1)P_c(x)x^i\mathcal D(x)]
               \quad (0\le j\le4)
\]
are the exact remainders of \(y^j\mu\)
times a single common scale.
Indeed \(J_j-yJ_{j-1}\) is the stated
constant modulo \(D_7\), and all
remainders have degree at most six
before taking any residues.
These formulas do not divide by the
head determinant, \(\mu_z\), or a leading
coefficient of a reduced polynomial.
They remain applicable when \(\mathcal D\)
drops degree or the head has a pole.
The reduced rank must be at most five
for the 7-by-6 columns \(V_0,\ldots,V_4,y\mathcal A^2\)
in the generic branch, and at most six
for the 7-by-7 columns
\(V_0,\ldots,V_4,y(1-y),y^2(1-y)\)
in the origin branch.
Exact minors vanish before reduction
regardless of the unknown coefficients'
denominators. A rank drop in the first
five columns is explicitly retained.

## Additional true host phase

The remaining \(\boldsymbol\eta\cdot\boldsymbol u\)
moment with \(y-c\) gives
\(U(R)=-A_0(R)/(1-R)\) by partial fractions.
At \(f,g,h\) the true dirt is the actual
terminal interpolant \((1-y)V_c(y)/C_\nu\)
where \(C_\nu=(1-R)V_c(R)\).
Thus the quartic satisfies
\[
                      C_\nu U=-A_0 V_c+\sigma(y-R)T_3 .
\]
Substitute in the two nonlinear congruences.
At each of the seven true singleton roots,
the resulting system in \(\sigma\)
and the one or two weighted coefficients
has necessary augmented rank at most two
(generic) or three (origin).
The census evaluates every row homogeneously
at degree ten in the site's projective pair.
It retains repeated projective roots and
does not apply this extra phase when the
\(d,e\) polynomial lost all scale.
It also checks the generic three tail ratios'
affine alignment with the **fixed** \(\mathcal A\),
not just arbitrary affine collinearity.
These are necessary filters, not sufficient
conditions for lifting.

## Reproduction

    c++ -O3 -std=c++17 -Wall -Wextra -pedantic census.cpp -o /tmp/rk-census29
    /tmp/rk-census29 | diff -u census29.txt -
    /tmp/rk-census29 --map | grep '^MAP ' | diff -u map29.txt -
    python3 -B audit_homog.py | diff -u homogeneous-audit.txt -

Each map line has the outer indices \(c,g\)
followed by 30 hexadecimal digits indexed by
\(R=0,\ldots,28,\infty\); index 29 means infinity.
The bits from low to high indicate generic
survivor, origin-root survivor, regular generic
survivor, regular origin survivor.
Digit zero is a proved exclusion of that
rational residue under the stated architecture.

The fully distinct finite literal experiment
is separate: stream the output from
    /tmp/rk-census29 --regular
to literal29.py with the fixed-q spectrum
directory and the flag --first.
The first recovered actual literal agrees
with the independently audited F29 publication.
The modular census is exact executed C++
with an independent symbolic row-scale check;
no full native Lean census or unrestricted
stage bound is asserted.
