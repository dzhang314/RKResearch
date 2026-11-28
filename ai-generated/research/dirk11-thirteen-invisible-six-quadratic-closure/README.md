# Excluding all quadratic carriers in the α=0 invisible DIRK11/13 chart

**Result.** No normalized no-late invisible-six DIRK11/13 candidate
with \(\alpha=0\) has a quadratic ghost profile \(U\). This closes the
full finite macro from the [earlier quadratic packet](../dirk11-thirteen-invisible-six-quadratic/README.md),
including all regular parameters, both new one-sided leading drops,
and singular and regular carriers above the subresultant pivot.
It uses the already excluded double-leading-drop case \(q=-3/10\)
and fixed Lobatto pencil \(\lambda=0\). A cubic profile is not excluded in
the relevant chronology counts; the unrestricted real stage
interval is **13–14**.

The setup is actual order 11, literal lower triangle, normalized
\(C(2),D(1),D(2)\) and grade-six surplus, with the signed
\(r=0,d=z_{\rm count}=6\) skeleton. After that skeleton has been
derived, the exclusion holds over any characteristic-zero coefficient
field. No new arbitrary-ring or positive-characteristic bound is
claimed. All forward clean and backward cubic profiles below
are from the original tableaux.

## 1. A forward split with no clock ordering in its first projection

Use the notation of the preceding quadratic proof: forward \(b,a\)
are the first two nonorigin clean stages. The quadratic carrier and
supported mark are normalized together so that \(U=X^2+sX+t\)
is monic and \(\phi=U(c)-g\). The preceding degree-six argument gives
\[
 F_b-rH=X(X-b)(\ell X+\mu)U,\quad
 F_b=I[X(X-b)U],\quad H=XJ_4,\quad q=42r\ne0 ,
\]
where \(I\) is the scalar primitive from zero,
\(\ell=1/5-q,\ \mu=q/(42bt)\), and \(b,t,U(a),U(b)\ne0\).
The actual diagonal at forward \(a\) is \(d_a=\ell a+\mu\).
The nonzero \(U\) values follow from the reciprocal clean head:
its amplitude cannot be zero for a quadratic, because the
three distinct old reverse clean cubic samples are live.

Let \(S_6=X(J_5+\lambda J_4)/132\) be the monic hull of the six
nonterminal clean forward clocks. Let
\(F_{ab}=I[X(X-a)(X-b)U]\).
The actual grade-seven primitive of \(C(C-a)(C-b)\phi\) vanishes
at every ghost and at \(a,b\): all possible literal donor entries of
that signal are zero. By the exact \(F_7\) shape of the
[constant carrier proof](../dirk11-thirteen-invisible-six-constant-exclusion/README.md)
(a rank shape not requiring constancy), the affine coefficient \(L\)
of its scaled terminal head has
\[
 L(a)=F_{ab}(a)/H(a),\qquad L(b)=F_{ab}(b)/H(b).
\]
Moreover \(F_{ab}-HL\) and \(S_6\) are proportional **modulo \(U\)**:
the degree-at-most-six ghost-zero polynomial
\(F_{ab}-HL+UQ_4\) is a multiple of the monic ghost hull, and
that ghost hull is \(S_6-UQ_3\) by exact \(E_6\).
The usual clean barycentric identity makes \(H(a),H(b)\ne0\).

The two exact primitive identities are
\[
 \begin{split}
 (1+\ell)F_{ab}(X)&=[X-(1+\ell)a-\mu] F_b(X)-r\,I H(X),\\
 I H(X)&=H(X)J(X)+(77/5)S_6(X),\qquad
           J(X)=-X/5+7(1-\lambda)/60 .
 \end{split}                                                   \tag{1}
\]
The first is integration by parts and the \(F_b\) identity.
The second is an exact coefficient calculation in \(X,\lambda\),
checked independently in Lean. Put \(M=X-(1+\ell)a-\mu\).
At \(a\), \(M(a)=-d_a\) and
\(F_b(a)-rH(a)=a(a-b)d_a U(a)\); at \(b\), \(F_b(b)=rH(b)\).
Consequently the exact two samples of the affine polynomial give
\[
 (1+\ell)L=r(M-J)-\sigma(X-b),\qquad
 \sigma=d_a^2 a U(a)/H(a).
\]
Reduce (1) modulo \(U\), subtract the preceding head, and take
the two-coordinate determinant with \(S_6\bmod U\).
Since initially \(F_{ab}-HL\) was proportional to \(S_6\), this
forces \(\sigma\) times the determinant of
\((X-b)H\bmod U\) and \(S_6\bmod U\) to vanish.
There is **no division by \(1+\ell\)**. No division by a
primitive value or the contact factors \(2a-b,2b-a\) occurs.

Multiplication by \(X(X-b)\) in the quotient by \(U\) is
invertible, since \(U(0)U(b)\ne0\), even if \(U\) has a repeated
root. Cancel it from the two remainder columns. There are
two exhaustive alternatives:

* **Zero literal diagonal** \(d_a=0\). Then \(\mu\ne0\)
  implies \(\ell\ne0\), \(a=-\mu/\ell\), and \(a\) is a root
  of the deflated ordinary quartic.
* **Remainder gate.** The coefficient vectors of
  \(J_4\bmod U\) and the deflated ordinary quartic modulo \(U\)
  have determinant zero. This gate depends only on \(b,q,t\),
  not on the choice or order of \(a\). Neither remainder
  is required to be individually nonzero.

## 2. Exact carrier guards and finite reconstruction

As in the earlier packet, the remaining two coefficients of
\(F_b-rH=X(X-b)(\ell X+\mu)U\) are the two \(t\)-cubics.
Their resultant is a nonzero constant times
\(b^4q^5(10q+3)\Gamma(b,q)\).
Its \(q\)-leading coefficient is \(2250000 J_4(b)^3\),
nonzero at the live ordinary clean clock. The nonzero \(t\)-cubic
leaders, up to nonzero powers of \(b\) and constants, are
\((10q+3)(20q+1)\) and \((10q+3)(15q+2)\).
Thus \(q=-1/20,-2/15\) are the two named one-sided contacts.
The replay specializes the equations **before** taking
subresultants at each, giving degree-three and degree-six
equations for \(b\) and linear unit-guarded recovery of \(t\).
The quadratic/linear degree changes are exact. The two-sided
\(q=-3/10\) is already excluded independently.

Away from these contacts, the linear \(t\)-subresultant has
coefficients \(L_0,L_1\). Strip from \(L_1\) only factors of
\(b,q,10q+3\). Its \(q\)-resultant with \(\Gamma\) is a
nonzero constant times \(b^{44}J_4(b)^6 E_7(b)^2\), where
\[
 E_7=3150b^7-11970b^6+18669b^5-15429b^4+7254b^3
                -1916b^2+255b-12 .
\]
Thus no physically admissible \(t\)-pivot fails outside
\(E_7(b)=0\). Over the exact irreducible degree-seven field on
\(E_7\), the gcd of \(\Gamma,L_0,L_1\) is monic linear in \(q\),
and the two \(t\)-cubics at that \(q\) have monic quadratic gcd.
This covers every singular \(t\)-pivot. For **regular** carriers
above the same \(E_7\), remove the linear common factor of
\(\Gamma,L_1\) twice, exactly in that degree-seven field. The
remaining monic degree-four \(q\) is coprime to \(L_1\), and
\(t=-L_0/L_1\) applies. There is no missing regular residue at
this base, nor an assumption that every \(E_7\) carrier is singular.

Outside those branches, work exactly in
\(\mathbb Q(b)[q]/\Gamma\): invert \(L_1\) to reconstruct \(t\)
and compute \(s,\ell,\mu\) as in the previous proof. Use the
deflated quartic with its known scalar leader,
\[
 D_4(X)=\frac{J_4(b)J_5(X)-J_5(b)J_4(X)}{X-b}.
\]
It is a polynomial; its monic normalization is the ordinary
quintic deflated by \(b\).
For the remainder branch, form the determinant of the two
remainders \(J_4,D_4\bmod U\). For the diagonal-zero branch,
homogeneously evaluate \(D_4\) at the pair
\((-q,42bt\ell)\), which encodes \(a=-\mu/\ell\).
No unknown numeral is rounded. The coefficient denominators
of the reduced expressions have only the known \(b,J_4,E_7\)
factors, verified exactly by the source.

The two resultants in \(q\) give the following exact
non-guard factors in \(b\). Guard factors are either \(b=0\)
or \(J_4(b)=0\) (inadmissible), \(E_7\) (separate checks),
or \(2b-1\) (the prior fixed Lobatto closure since \(J_5(1/2)=0\)).
The remainder gate has degrees \(2,3,3,12\) with
multiplicities \(1,2,3,1\); the diagonal-zero gate has one
degree-60 factor. These are **exact rational resultants**,
not inferred from modular degree. In each retained factor,
the linear subresultant in \(q\) gives a unit-guarded recovery
of \(q\). Repeated factors and branch overlap are harmless.
All ordinary choices of \(a\) in the remainder or pivot chart
are retained by one monic quartic. In the diagonal chart
\(a\) is already furnished by \(-\mu/\ell\).

## 3. Unordered actual three- and four-column marks

For each reconstructed \(a,b\), the remaining three ordinary
reverse clocks form a monic cubic \(R_3\), obtained by deflating
the ordinary quintic by \(b,a\) in forward clocks, then reflecting.
These clocks are the consecutive literal old prefix \(v,u,w\)
after the terminal. No order among them need be chosen for the
following test. The next literal clean is \(A=1-a\), and
\(\alpha=0\) ensures there are no ghosts through that row.

For a regular site \(y\), use the normalized cubic shape
\(\widehat k(y)=yJ_4(y)/U(1-y)\); the genuine \(G_y/b_y\)
is \(\kappa \widehat k(y)\) with one nonzero \(\kappa\).
In the unordered triple quotient reduce
\[
 m=J_4(Y)/U(1-Y)\bmod R_3 .
\]
The representative has degree at most two. Put \(P=Ym\),
and \(P_1=Y(Ym\bmod R_3)\). They are cubics of zero constant
representing \(\widehat k\) and \(Y\widehat k\) on the three
old labels and the physical terminal. Let
\[
 r_0=I P/P\bmod R_3,\qquad r_1=I P_1/P\bmod R_3 .
\]
The live old cube allows these divisions.

To see the actual marks behind these formulas, a weighted
transpose tap row applied to
\(c_1Y+c_2Y^2+c_3Y^3\) reads its formal primitive plus
\((c_2+c_3L_1^\mathrm{rev}(y))G_y/b_y\), by the genuine paid
first three positive moments and affine fourth-cubic multiplier.
Here \(L_1^\mathrm{rev}\) is the reverse primitive profile,
not the scalar subresultant coefficient. The correction is
affine times the genuine cubic. Hence on \(v,u,w\),
the affine \(NG\) profile forces \(r_0\) to have zero quadratic
coefficient. The \(N(YG)\) profile pays the analogous quadratic
quotient \(r_1\). At the next regular \(A\), only the own
literal diagonal contributes the difference between the old
interpolating polynomial and the actual sampled mark.
Consequently the three exact necessary residuals are
\[
 \begin{split}
 [Y^2]r_0,\qquad
 I P(A)-\widehat k(A)r_0(A)
       +d_a(\widehat k(A)-P(A)),\\
 I P_1(A)-\widehat k(A)r_1(A)
       +d_a(A\widehat k(A)-P_1(A)).
 \end{split}
\]
This uses only the first three actual scalar moments at that
row. It does not assume or impose any extra order on a
restricted reverse tableau. Using the unordered triple rather
than its splitting algebra reduces the main rank by six.

## 4. Exact unit arithmetic and scope

For every finite factor listed below, the source proves
the linear combination of the last-three residuals with
coefficients \(1,2,3\) is a unit modulo 101.

| Branch | Main finite-free rank |
| --- | ---: |
| \(q=-1/20,-2/15\) | 12, 24 |
| \(E_7\)-singular, \(E_7\)-regular | 56, 112 |
| remainder degrees 2, 3, 3, 12 | 8, 12, 12, 48 |
| diagonal-zero degree 60 | 60 |

The interpolation by \(R_3\) uses a transient monic cubic
over each main ring; its three-nodal residue coefficients
return to the main ring. The inverse receipt counts this
transient ring separately. The replay reconstructs all
polynomial factors and checks every divider by multiplication
back to one in its residue algebra. Lifting is over
\(\mathbb Z_{(101)}\): a residue-invertible multiplication
matrix on a finite-free module has unit determinant, hence
an inverse by its adjugate before reduction. This applies at
each divider and monic adjunction. At a hypothetical char-zero
tableau, the formal quotients specialize by the exact polynomial
and subresultant identities just described. The three paid
residuals would be zero, which cannot happen to the final unit.
There is no hypothesis that any unknown tableau, ghost clock,
or stage coefficient reduces modulo 101.

Run \(\texttt{python3 replay.py}\) with SymPy, using the
adjacent earlier quadratic and constant-exclusion computational
packets. The Lean module checks the Jacobi primitive identity,
guarded nondivisive coefficient split, true weighted moment
scalar adapter, affine interpolation and the fourth-column
identity. The full chronology/finite-field composition remains
an exact reproducible mathematical source proof rather than a new
end-to-end Lean tableau endpoint.
