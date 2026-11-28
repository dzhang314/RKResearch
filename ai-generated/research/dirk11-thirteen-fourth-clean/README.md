# Excluding the normalized `(r,d,z,k)=(1,5,4,2)` DIRK11/13 face

**Result.** The remaining one-active-label, five-physical-dirty-label case
of the [low-dirty census](../causal-profile-reduction/dirk-order11-thirteen-zero-one-low-dirty.md)
is impossible. This closes \(r=1,d\ge4\) under the normalized 13-stage
hypotheses; the older census handles \(d=2,3\), but \(d=1\) is separate.
The invisible \(r=0\) and high-support \(r=9\) cases are not treated here.
The unrestricted real numerical stage interval remains **13–14**.

The actual rooted-order assumption is eleven, the array is literal lower
triangular with forward `C(2)`, genuine reflected `D(1),D(2)`, and the
ordinary grade-six surplus. The proof enters the signed skeleton and
true rank data of the cited census and the
[earlier one-active macro reduction](../dirk11-thirteen-one-active-macro/README.md).
The final arithmetic proof is valid over any characteristic-zero field
**given those signed-skeleton, weighted support and paid rank premises**.
No ordered structure is needed after those premises are in place. For
real tableaux the independent interval replay gives the same conclusion.

## 1. A true grade-six ordinary head for the paid reverse rows

Keep the earlier notation: \(N=A^{\mathsf T}\) in reversed physical
chronology, \(Y=\operatorname{diag}(y)\) with \(y=1-c\), \(B\) the actual signed active
pair restricted weight, \(D=NB\), and \(j\) the latest active nonunit
stage. Its numerical reflected clock is \(V\ne0\) and \(A_{jj}=V/2\).
The reverse chronology starts with the actual terminal, \(j\), then the
clean regular stages of distinct live clocks \(u,v,w\). Denote the next
two distinct non-endpoint clean clocks in reverse physical order by
\(a,b\). They may be exterior to the integration interval; no coefficient
or weight positivity is assumed. The physical origin, possibly unweighted,
comes last in reverse. It is never normalized by its weight.

By the earlier rank proof, \(U_0=E_6^\perp=\langle B,D\rangle\) and
\(Z_5=E_5^\perp\cap\{T=0\}=\langle B,D,YD\rangle\). Every actual ghost
has its individual \(D_i\ne0\), the earlier dirty pair member has
\(D_i-(V/2)B_i\ne0\), and \(D_j=(V/2)B_j\). All four ghosts have distinct
labels, different from the pair label. These support facts account for
both types of nonregular stages below.

Let \(K(X)=(X-1)\prod_{s\in\{u,v,w,a,b\}}(X-s)\), the monic hull of the
six nonterminal clean coordinates in the reflected variable. Take \(H\)
supported at exactly those six sites with values a common nonzero
multiple of (1/K'(s)); it is zero at all dirty and terminal coordinates.
Then, exactly,
\[
 Z_6:=E_4^\perp\cap\{T=0\}=\langle B,D,YD,Y^2D,H\rangle.
\]
Indeed \(E_4=\mathcal P_4(c)+g\mathcal P_1(c)\) has dimension 7, and
the terminal cardinal is outside it by degree-four vanishing on the
six distinct other clean sites. \(Y^j D\) for \(0\le j\le2\) are in \(Z_6\)
by true grade multiplication, and independent modulo \(B,H\) at the
four distinct \(D\)-live ghost clocks. The single clean barycentric row
annihilates degree four by Lagrange interpolation and annihilates \(g\)
and (Cg) by support. \(B\) and \(H\) have disjoint nonempty supports.
This gives all five dimensions, not just a containment. No sign or
invertibility of the full diagonal weight matrix is used.

Scale \(H\) so that \(H_s/b_s=h(s):=sJ_4(s)\) at all five regular
non-endpoint clean sites, where \(J_4=42X^4-84X^3+56X^2-14X+1\).
To see the common scaling, write \(L_s(X)=K(X)/[(X-1)(X-s)]\), monic
degree four. The integral of \(X(1-X)L_s(X)J_4(X)\) is the same nonzero
constant \(\kappa=(1/42)\int_0^1 X(1-X)J_4(X)^2\,dX\) at every \(s\),
by orthogonality of \(J_4\). This is a nonzero rational, so it is
nonzero also over a characteristic-zero field. The actual degree-ten
ordinary rule gives \(b_s s(1-s) L_s(s)J_4(s)=\kappa\). Thus
\(1/[b_s K'(s)]=-sJ_4(s)/\kappa\), as needed. Nonzero \(b_s\) is supplied
only at the interior clean sites, not at the origin.

The two new genuinely paid rows are
\[
 G_6=N W(X^5)-W(X^6/6),\qquad N(YD),\qquad W(P)=bP(y).
\]
The reflected degree-six row \(G_6\) is paid against \(E_4\) (grade
\(6+4=10\)); \(N(YD)\) is paid because \(YD\) annihilates \(E_5\) and
\(A E_4\subset E_5\). Both have true terminal coordinate zero, from the
zero terminal column and primitive at \(y_T=0\). Consequently write
\[
 G_6=c_0 B+R_2(Y)D+c_1 H,\qquad
 N(YD)=d_0 B+F_2(Y)D+d_1 H,\qquad \deg R_2,\deg F_2\le2.
\]
The proof uses these weighted rows in the original tableau. It does not
assert order, even of a single tree, for a transposed or projected RK
method.

## 2. The literal compensation, including an intervening stage

Put \(Q_*=V(V-u)\ne0\), and \(k_s=Q_*D_s/b_s\) at each live regular
site. For its true inclusive regular donors \(r\), let
\(L_{s,r}=b_r N_{s,r}/b_s\), and shift only the tap at \(u\) by
(k_s/[u(V-u)]); denote it by \(\bar L_{s,r}\) after the shift. This
is a change of read variables, not a change to \(A,b\). For a nonregular
stage \(i\ne j,T\), define
\[
 \widetilde D_i=D_i-(V/2)B_i,\qquad
 e_{i,s}=Q_*\widetilde D_i N_{s,i}/b_s.
\]
The first is nonzero on every such actual ghost or earlier pair stage.
We explicitly retain the second even if it vanishes. All
nonregular stages except the active dirty pair carry zero \(b\), so every
weighted scalar read has the *aggregate* dirty tap \(V^m D_s\) at power
\(m\ge1\), whether or not the earlier pair member is a donor.

Define \(b_0(s)=(s^2/2,s^3/3,s^4/4,s^5/5)\) and
\[
 \ell(s)=\left(0,-1,-3u/2,-9u^2/5-
             \frac{3(u-v)^2(s-u)}{5(2u-v)}\right),\quad
 f(s)=\frac u2+\frac{u^2-4uv+v^2}{2(u-2v)(2u-v)}(s-u).
\]
For \(m=1,2,3,4\) the moments of the regular row \(\bar L\) are
\(b_0(s)_m+\ell(s)_m k_s\). This uses the paid `D(2)`, \(G_3,G_4,G_5\),
and the same first-two calibration as the previous macro packet. In
particular, the fourth coefficient is
\((\nu(s)-V^4+u^3V)/Q_*\), with \(\nu\) the earlier affine \(G_5\)
coefficient. Substitution of its two known values gives the displayed
\(\ell_4(s)\) exactly. The \(G_6\) extension gives
\[
 \sum_r \bar L_{s,r} r^5=s^6/6+\rho_2(s)k_s+\chi h(s),
 \quad \rho_2=(R_2-V^5+u^4V)/Q_* ,\quad \chi=c_1.
\]
For the two marked grades, the exact weighted equations at a clean \(s\)
are
\[
 \begin{split}
 \sum_r k_r \bar L_{s,r}+\sum_i e_{i,s}&=f(s)k_s,\\
 \sum_r r k_r \bar L_{s,r}+\sum_i y_i e_{i,s}
     &=f_2(s)k_s+\theta h(s),\quad \deg f_2\le2.
 \end{split} \tag{1}
\]
In the first line use \(ND\in Z_5\), and subtract \((V/2)NB=(V/2)D\)
from \(ND\) before shifting. In the second use the displayed \(Z_6\)
form and subtract \((V^2/2)D\) from \(N(YD)\), since \(YB=VB\).
The shifts add \(k_u/[u(V-u)]\) and \(k_u/(V-u)\) respectively to the
polynomial multipliers. The first multiplier is then \(f(s)\) from
the first-two Cramer reads; the second is \(f_2(s)=F_2(s)-V^2/2+k_u/(V-u)\)
and \(\theta=Q_*d_1\).

There is a second crucial *literal* use of these same equations. Take a
first nonregular stage \(i\) after \(m\) regular stages and before the
next one, with no other nonregular stage since \(j\). Write \(z=y_i\)
and \(d_i=A_{ii}\). For each of the \(m\) available nonzero regular
clocks \(r\), define
\[
 \sigma_r=\frac{b_r N_{i,r}/\widetilde D_i+[r=u]V/u}{Q_*}.
\]
The genuinely paid equations on this column give
\[
 \sum_r \sigma_r r^k=\ell(z)_k\quad(k=1,2,3,4),\qquad
 \sum_r \sigma_r r^5=\rho_2(z),                         \tag{2}
\]
\[
 \sum_r k_r\sigma_r+d_i=f(z),\qquad
 \sum_r r k_r\sigma_r+z d_i=f_2(z).                     \tag{3}
\]
For a ghost, \(b_i=B_i=H_i=0\), and the actual unshifted no-dirty
weighted moments are
\((-V,-V^2,\mu-V^3,\nu(z)-V^4,R_2(z)-V^5)\widetilde D_i\).
For the **earlier active pair member** we have \(z=V\), possibly equal
to a clean numerical site. For each genuine scalar read at degree
\(k=1,\ldots,5\), calibrate the coefficient of \(B\) at \(j\), where
\(N_{jj}=V/2\) and \(D_j=V B_j/2\). Subtract the dirty aggregate
\(V^k D_i\) on the actual earlier column. The same five unshifted
formulae then result with \(\widetilde D_i=D_i-VB_i/2\), not with
\(D_i\) by itself. For the two marked equations calibrate the \(B\)
coefficients in \(ND\) and \(N(YD)\) at \(j\) in just the same way;
\(N_{jj}D_j=VD_j/2\) and \(N_{jj}VD_j=V^2D_j/2\). The remaining
nonregular contribution is its own diagonal times \(\widetilde D_i\)
or \(z\widetilde D_i\), respectively. Dividing by the live \(\widetilde D_i\)
and shifting gives (3). This treats both physical kinds of optional stage
and never assumes they contribute a nonzero **tap** into a later clean
column. It allows the actual site to coincide numerically with a clean
site.

## 3. Eliminate any optional stage before the fourth regular

At \(u,v,w\), the exact \(k_u,k_v,k_w\), taps, and clocks are those of
the preceding macro gate. The paid \(Z_6\) equations (1)–(2) now
calibrate two more functions. For \(s=u,v,w\) set
\[
 p_s=(\textstyle\sum r k_r\bar L_{s,r})/k_s,\quad
 q_s=(\textstyle\sum r^5\bar L_{s,r}-s^6/6)/k_s,\quad
 h_s^*=h(s)/k_s .
\]
All three divisions are certified in the finite certificate below.
Let \(I\) denote interpolation by degree at most two through \(u,v,w\).
Then \(f_2=I p-\theta I h^*\) and
\(\rho_2=I q-\chi I h^*\).

If an optional nonregular stage lies between \(w\) and \(a\), the earlier
macro proof gives **one such stage at most**, with exact
\(z=w+M/[6(u-v)^2]\) and literal \(d_i=z-w\ne0\). In particular it is the
first nonregular after the three clean stages, so (2)–(3) apply, and the
three regular \(\sigma\) taps are given by the Cramer reads using the
first three entries of \(\ell(z)\). With
\[
 p_z=\sum r k_r\sigma_r+z(z-w),\qquad q_z=\sum r^5\sigma_r,
\]
the two interpolation fits at \(z\) determine \(\theta,\chi\):
\((I p(z)-p_z)/I h^*(z)\) and \((I q(z)-q_z)/I h^*(z)\).
The evaluation denominator is certified nonzero at every candidate.
At \(a\), the first four moments solve the four regular taps in the
form \(\alpha_r+\beta_r k_a\). The fifth moment is a **linear** equation
for \(k_a\) with the already calibrated \(\rho_2,\chi\); its coefficient
is also certified nonzero. Finally subtract \(z\) times the first line
of (1) from the second. The only possible unknown optional contribution
cancels identically. Its resulting equation on the four regular taps
has a certified nonzero residual for every possible macro and \(a\).
This contradicts the optional-before-fourth chart, with no assumed
nonzero optional tap into \(a\).

## 4. Both fifth chronologies lead to coprime quadratic equations

There is now **no** nonregular stage through \(a\) except \(j\) and the
terminal. The same four taps at \(a\) are \(\alpha_r+\beta_r k_a\). The
first line of (1) with no \(e_i\) gives the quadratic
\[
 \beta_a k_a^2+
 (\alpha_a+\sum_{r=u,v,w}k_r\beta_r-f(a))k_a+
 \sum_{r=u,v,w}k_r\alpha_r=0.                             \tag{4}
\]
This quadratic is monic after dividing by the certified nonzero
\(\beta_a\). The same \(p_s,q_s,h_s^*\) constructions now at \(s=a\)
fit \(\theta,\chi\) by the fourth regular sample, using denominator
\(h_a^*-I h^*(a)\). The certificates include this guard and \(k_a\ne0\)
for every root of (4) in the monic quotient. Thus both quadratic
polynomial profiles are fixed throughout each remaining branch.

* If any nonregular stage is before \(b\) after these four regular
  samples, take the **first** such stage (so no need to suppose there is
  only one). Its unknown clock \(z\) is unrestricted, including possible
  numerical cross-color coincidences. Equation (2) with \(k\le4\) fixes
  the four regular \(\sigma\) taps affine in \(z\). Its fifth read gives
  \(\sum r^5\sigma_r(z)-\rho_2(z)=0\). Subtracting \(z\) times the first
  equation in (3) from the second also gives
  \(\sum(r-z)k_r\sigma_r(z)-f_2(z)+z f(z)=0\). Both are polynomials of
  degree at most two in the same \(z\). Their Sylvester determinant is
  a unit in the finite certificate, so there is no such stage.
* If there is no such nonregular stage, the \(b\)-row has exactly the
  five inclusive regular donor clocks \(u,v,w,a,b\), plus the already
  accounted-for \(j\) and terminal. Its first five scalar moments
  solve the five taps affine in \(k_b\) by Cramer, including the
  calibrated fifth scalar read. The two equations (1), with no \(e_i\),
  now give two quadratics in \(k_b\). Their Sylvester determinant is
  again a unit. This closes the other chronology.

No supposition about the order of the unused earlier dirty stages or
about an early forward ghost column is used for this exhaustive split.

## 5. Exact finite certificate; why it lifts to characteristic zero

The only remaining scalar input is the earlier exact macro reduction:
\(t=v/u\) satisfies the primitive degree-60 factor \(F_{60}(t)=0\) of its
Jacobi resultant; \(u\) is the ratio from the degree-one subresultant.
The two possible next clean clocks are the two remaining roots of
\(J_5+\lambda J_4\); knowing \(u,v,w,\lambda\) gives their exact sum and
product via the two top monic coefficients. Thus impose a single **monic
quadratic** for \(a\); the other root is \(b=\mathrm{sum}-a\). Both choices
are retained. Then impose the **monic quadratic** (4) for \(k_a\), after
checking all divisions. It is immaterial if any of these algebras
factors or has nilpotents after reduction.

`replay_mod101.py` recomputes the rational degree-96 resultant and its
factorization, and exactly evaluates the requisite functions in the
rank \(60,120,240\) monic quotient bases. It verifies:

1. Every division in the base and the two extension calculations is by
   a unit modulo 101 (including all nonzero sample taps divided by,
   interpolation/Cramer denominators, and the leading coefficient of
   (4)). Each computed inverse is multiplied back and checked.
2. The optional-fourth residual is a unit in the 120-dimensional quotient.
3. The two fifth Sylvester determinants are both units in the full
   240-dimensional quotient, covering every root of both quadratics,
   including candidates that are not real.

The lift is over \(\mathbb Z_{(101)}\), not a claim that an unknown tableau
reduces at 101. Initially divide \(F_{60}\) by its 101-unit leading
coefficient to make the base polynomial monic. Its quotient is finite
free of rank 60. For an element whose residue is a unit, its
multiplication matrix is invertible modulo 101, so its determinant is
an exact unit of \(\mathbb Z_{(101)}\), and its adjugate gives an inverse
in the original finite free ring. Apply this argument to **each** internal
divider before adjoining \(a\), and then similarly before adjoining
\(k_a\); the monic adjunctions preserve finite freeness. The same unit
argument applies to the three final contradiction scalars. Every
characteristic-zero candidate in the signed skeleton would evaluate the
relevant quotient into its coefficient field, where a unit cannot become
zero. No other field choice or integrality of \(A,b,V\) is required.

The separate `replay.py` gives a rational outward-rounded interval audit
of the **real** slice. It isolates all 12 macro ratios, excludes all 24
optional-fourth choices, and rejects 16 of the 24 no-optional choices by
negative discriminant. For both quadratic roots of each of the eight
remaining choices it rigorously tests both fifth determinants. Diagnostic
decimals are never used as evidence; all assertions use exact integer or
rational bounds.

The accompanying Lean/Mathlib 4.36 scalar module checks the two quadratic
eliminations, cancellation of a same-column intervening tap and the
discriminant implication using only standard axioms. The rooted
order-to-signed-skeleton and \(Z_6\) deductions above remain a written
mathematical proof; the finite quotient replay is exact independent
arithmetic, not an end-to-end Lean theorem about `HasOrder 11`.
