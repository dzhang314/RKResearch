# No linear cubic-defect profile in the normalized invisible-six DIRK11/13 chart

**Result.** The normalized invisible-six, no-late-ghost chart cannot have a
linear forward cubic-defect profile. This closes the linear cases of
\((\alpha,\beta,\gamma)=(1,2,3),(2,1,3)\). It does not exclude their
quadratic or cubic profiles. The unrestricted real DIRK11 stage interval
stays **13–14**.

The starting hypotheses are a literal triangular thirteen-stage tableau
of actual rooted order 11, forward \(C(2)\), genuine reflected \(D(1),D(2)\),
order-six surplus, and \(r=0,d=z_{\mathrm{count}}=6\) in the signed census.
There are six physical zero-weight dirty stages at distinct clocks,
and seven distinct clean clocks including the actual origin and terminal.
The five nonendpoint clean weights and the terminal weight are live.
Use the true spaces from the
[paid](../dirk11-thirteen-invisible-six-paid/README.md),
[no-late count](../dirk11-thirteen-invisible-six-no-late/README.md),
[forward masks](../dirk11-thirteen-invisible-six-prefix/README.md),
and [constant closure](../dirk11-thirteen-invisible-six-constant-exclusion/README.md)
packets, not any rank of an invented tableau. Given those inputs,
the argument applies over every characteristic-zero coefficient field.

## 1. True shapes and the forward pole

Write \(C=\operatorname{diag}(c)\), \(y=1-c\),
\(Y=\operatorname{diag}(y)\), \(N=A^{\mathsf T}\) in literal reverse
order, and \(W(P)=bP(y)\) for the weighted row. The actual spaces are
\[
\begin{split}
 E_6&=\mathcal P_5(c)+g\mathcal P_3(c)+Ke_T,\quad
 E_7=\mathcal P_5(c)+g\mathcal P_4(c)+Ke_T,\\
 F_6&=g\mathcal P_3(c)+K(e_T-H_T(c)),\quad
 F_7=g\mathcal P_4(c)+(e_T-H_T(c))\mathcal P_1(c),\\
 Z_4&=G\mathcal P_1(y),\quad Z_5=G\mathcal P_2(y),\quad
 Z_6=G\mathcal P_3(y)+KH_{\rm bary},\qquad
 H_T(X)=30b_T XJ_4(X).
\end{split}
\]
Here \(g,G\) are the genuine cubic defects, \(G\) live on every ghost
and the first three regular reflected rows. Scale the forward defect
by its nonzero leading coefficient so that \(U(X)=X-\rho\) is its
profile on ghosts. Then \(\phi=U(c)-g\) is a true grade-three column
supported on clean rows. The reciprocal profile gives
\(G\phi=\tau H_{\rm bary}\). Since \(G\) is live on the distinct
old regular triple, \(\tau=0\) would give three roots of linear \(U\).
Thus \(U\) is live on each nonterminal clean clock (and on ghosts);
\(\rho\ne0\). At each regular nonendpoint row
\(G_i/b_i=\kappa k(y_i)\) with a single \(\kappa\ne0\) and
\[
 k(Y)=Y J_4(Y)/(1-\rho-Y).
\]
There is no evaluation of this rational expression at the true
terminal, whose reverse clock is zero. In particular \(\rho=1\)
is allowed up front, as is a ghost of reverse clock zero.

The reverse chronology is \(T,v,u,w,[\alpha],A_0,[\beta],B_0,
[\gamma],O\), with brackets denoting dirty blocks. The previously
proved \(\gamma\ge3\), \(\gamma\le\deg U+2\), and linear \(\alpha=0\)
exclusion give \(\gamma=3\), \(\alpha\in\{1,2\}\).
Write \(a=1-A_0,b=1-B_0\) for the second and first regular forward
clocks. This scalar \(b\) is distinct from the weight vector.
Ordinary order-ten quadrature puts the five ordinary nonendpoint
forward clocks on the monic \(T_5=(J_5+\lambda J_4)/132\), with
\[
 J_4=42X^4-84X^3+56X^2-14X+1,\qquad
 J_5=(2X-1)(66X^4-132X^3+84X^2-18X+1).
\]
Set \(s=a+b,p=ab,Q_2=X^2-sX+p,S_6=XT_5,H=XJ_4\).
Let \(R_3^{\rm fwd}=T_5/Q_2\) and \(R_3(Y)=-R_3^{\rm fwd}(1-Y)\)
be the old forward and reverse monic cubics. The \(E_6\) decomposition
of \(S_6(c)\) has no pure degree-five component, since it would
vanish on six distinct nonterminal clean clocks. Thus the monic hull
of all six dirty clocks is \(R_6=S_6-UQ_3\) with \(\deg Q_3\le3\).

The true grade-six input \(C(C-a)(C-b)\phi\) is zero on every
inclusive donor to a ghost or the rows \(a,b\): the only possible
clean donors are \(O,b,a\), and all dirty entries of \(\phi\) are
zero. Thus \(A\) of that column vanishes at all those rows. Put
\(F=I[XQ_2(X)(X-\rho)]\), with \(I\) the zero-constant primitive.
Its actual grade-seven error is in \(F_7\). Absorb \(30b_T\) into the
affine terminal coefficient \(L=L_0+L_1X\). At \(a,b\), \(L=F/H\),
where both denominators are live. On the six ghost clocks
\(F+UQ_4-HL=0\), for one polynomial \(Q_4\) of degree at most four.
The degree is at most six and the top coefficient is \(-42L_1\);
hence this polynomial equals \(-42L_1R_6\), also when \(L_1=0\).
At \(\rho\) it gives
\[
 F(\rho)-H(\rho)L(\rho)+42L_1 S_6(\rho)=0. \tag{1}
\]
As a polynomial in \(\rho\), the degree-seven coefficient cancels.
It is divisible by \(\rho Q_2(\rho)\): zero is automatic, and \(a,b\)
are roots by the interpolation and pencil identities. All three
factors are nonzero at an actual pole. The quotient \(F_\rho\) has
degree at most three; its leader may vanish on exceptional fibers.

## 2. Unordered first-gap paid equations

Set \(P_0=YR_3(Y)\), \(t=1-\rho\),
\(m=J_4(Y)/(t-Y)\bmod R_3\),
\(P=Ym\), and \(P_1=Y(Ym\bmod R_3)\).
Both \(P,P_1\) have zero constant and degree at most three.
They evaluate to \(k,Yk\) on the old triple and to zero at the true
terminal. Write \(r_0=IP/P\bmod R_3\), \(r_1=IP_1/P\bmod R_3\),
\(w_0=IP_0/P\bmod R_3\), represented by quadratics or less.
The old denominators \(P\) are live. Use the common rescaling
\(\bar G=G/\kappa\).

The actual primitive \(W(IP)-NW(P)\) and \(N\bar G\) are in \(Z_4\).
On the old regular rows \(NW(P)=N\bar G\): each inclusive donor is
old regular or the terminal with both values zero. Thus \(r_0\)
is affine, as its three values are a sum of affine multipliers.
For \(P_1\) the matching old tap is \(N(Y\bar G)\in Z_5\),
so together with the genuine cubic primitive it supplies \(r_1\).
At the first gap ghost \(z\) the only missing tap in each of the
two reads is its own diagonal, once unmarked and once multiplied
by \(z\). Both \(W(IP)\) and \(W(IP_1)\) are zero there, but
\(\bar G_z\ne0\). In these normalized reads the diagonal is \(r_0(z)\)
and \(r_1(z)-z r_0(z)=0\).
The quartic primitive \(W(IP_0)-NW(P_0)\in Z_5\) has zero tap term
on all old rows and every ghost in that first gap. The old reads
determine its multiplier \(w_0\), hence at the first ghost
\[
 w_0(z)=0,\qquad r_1(z)-z r_0(z)=0. \tag{2}
\]
This uses no clock division at a ghost and allows ghost/clean
clock coincidences. Its quadratic Sylvester determinant is necessary
even at changes of the two polynomial degrees.

## 3. Exact pair projection, guard factors and contacts

In the symmetric monic rank-four pair algebra over \(\mathbb Q(s)\),
the relation is the constant-leading quartic \(F_{\rm pair}(s,p)\)
verified by
\[
 (a-b)F_{\rm pair}(a+b,ab)=J_5(a)J_4(b)-J_5(b)J_4(a).
\]
Recover \(\lambda\) using \(-J_5/J_4\bmod Q_2\); compute \(L\) for
(1) by \(F/H\bmod Q_2\). The norm of \(H(a)H(b)\) is proportional
to \((s-1)^4 E_J^2 E_H\), where
\[
 E_J=63s^4-252s^3+357s^2-210s+43,\qquad
 E_H=66s^4-144s^3+108s^2-32s+3 .
\]
These factors mark **possible** specialization failures of the
symmetric division; they do not remove physical sums.

For the numerator of (2), take
\[
 m_{\rm num}=J_4(Y)\frac{R_3(t)-R_3(Y)}{t-Y}\bmod R_3 .
\]
The quotient here is a polynomial difference quotient, at contacts
too. Use this numerator in \(P,P_1\); then multiply the numerator
primitive, after canceling its polynomial factor \(Y\), by
\((t-Y)(J_4^{-1}\bmod R_3)\). The Jacobi inverse uses the fixed
Bézout identity of \(J_4,J_5\) and \(J_5(Y)=\lambda J_4(Y)\)
on the reflected old cubic. This gives
\(r_{j,\rm num}=R_3(t)r_j\) at every actual profile. The same
primitive factorization gives \(w_{\rm num}=w_0\) with no
\(R_3(t)\) factor. Exact coefficient cross-multiplication in
the symmetric algebra proves \(r_{0,\rm num}[Y^2]\)
proportional to \(F_\rho\). In the regular chart its nonzero
leader allows this coefficient to be dropped at \(F_\rho=0\).
Compute the quadratic determinant of \(w_{\rm num}\) and
\(r_{1,\rm num}-Y r_{0,\rm num}\) with that cubic term removed;
it has degree eight in \(\rho\).

The two resulting polynomials are cleared of scalar denominators
whose nonconstant factors are only \(s-1,E_J\). Pseudo-reduce
the ghost determinant by \(F_\rho\) to the quadratic \(B_\rho\),
and form the \(3\times3\) Bézoutian determinant. The norm of the
cleared \(F_\rho\) leader is proportional to
\((s-1)^4 E_J^6 E_{12}\), with \(E_{12}\) of degree twelve.
After thirteen exact polynomial divisions by this leader in the
pair algebra (using the adjugate of its \(4\times4\) multiplication
matrix) and scalar content proportional to
\((s-1)^{20}E_J^{20}\), let \(B(s,p)\) be the resulting necessary
pair polynomial. Every removed factor is live on the regular chart.
Its exact norm, after removing the listed guards, has factors of
degrees \(6,30,42\) with multiplicities \(6,2,2\).

The exceptional sums are handled without those generic divisions:

* **Sum one.** Symmetry of \(J_4\) and antisymmetry of \(J_5\),
  their two samples and nonzero \(J_4\) give \(\lambda=0\).
  The pair cannot contain the equal central root, so
  \(66p^2-18p+1=0\). Direct exact reduction gives the monic pole
  cubic \(\rho^3+(-4p/7-106/77)\rho^2+(5p/7+142/231)\rho
  +p-41/231\).
* **Each quartic \(E_J,E_H\).** In the exact quartic sum field
  remove only the pair factors where \(H(a)H(b)=0\).
  Each removes one linear factor in \(p\), leaving a monic
  cubic. Rebuild (1) with the actual pair inversion and a
  cubic leader that is a unit in the residue algebra.
* **Leader factor \(E_{12}\).** The exact gcd with the
  cleared pole leader is linear in \(p\); the complementary
  factor is cubic. The first fiber has exactly zero cubic
  leader and a unit quadratic leader modulo 101; the
  other has a unit cubic leader.

For each of these fibers the original Sylvester determinant (2)
is a unit modulo 101 in the corresponding finite clock algebra.

For the regular factors, reconstruct \(p\) and, when needed, \(\rho\)
from an exact linear cofactor relation. For polynomials of degree
bounds \(m,n\), take rows of shifts of the first through
\(0,\dots,n-2\) and the second through \(0,\dots,m-2\), descending
columns. Cofactors of the columns above linear give one row
combination surviving in the constant and linear columns. Both
coefficients are determinants with the same sign convention.
That is a necessary linear relation at a common root also if a
leading coefficient drops; the measured pivot is checked separately.

* **Degree six.** Reconstruct \(p\) from \(F_{\rm pair},B\).
  Exact homogeneous evaluation in the degree-six sum field gives
  both coefficients of \((J_5-J_4)\bmod Q_2\) zero.
  Thus \(\lambda=-1\) and the pencil has the extra root 1,
  impossible since it has five distinct nonendpoint roots.
* **Degree thirty.** The exact norm in \(p\) of the
  \(\rho\)-Bézoutian of \(F_\rho,R_3^{\rm fwd}\) has this precise
  primitive degree-thirty numerator. Its denominators are guarded
  and its pole leaders do not vanish there. Thus at each such \(s\)
  there is, over an extension, a formal pair root \(p\) and a pole
  \(\rho\) equal to an old forward clock. At that contact
  \(R_3(t)=0\), \((t-Y)m_{\rm num}=0\bmod R_3\);
  hence \(P_{1,\rm num}=tP_{\rm num}\) and
  \(r_{1,\rm num}=t r_{0,\rm num}\). Also \(w_{\rm num}(t)=0\)
  by its explicit factor \(t-Y\) before reduction. The exact
  affine-coefficient identity makes this a root of the **main**
  pair and pole gates with \(z=t\). In the degree-thirty sum algebra
  both linear leading pivots (first for \(p\), then from
  \(F_\rho,B_\rho\) for \(\rho\)) are units modulo 101. Therefore
  all characteristic-zero solutions at that \(s\) agree on \(p,\rho\),
  including after the field extension. Every actual solution would
  therefore have this forbidden \(U=0\) at an old regular stage.
  No modular equality is inferred as an exact equality.
* **Degree forty-two.** Both linear pivots are units too.
  Adjoin the monic quadratic \(a^2-sa+p\) and set \(b=s-a\),
  preserving both orders. The following two additional actual
  checks are in that rank-84 algebra. No ordering of the old
  triple is imposed.

## 4. The two decisive degree-forty-two marks

Let \(F_b=I[X(X-b)U]\), \(e=F_b(b)/H(b)\).
The true grade-six error of \(C(C-b)\phi\) has normalized
terminal coefficient \(e\) from its zero tap at \(b\).
At \(a\) the only nonzero inclusive donor is its own diagonal,
so
\[
 d_a=\frac{F_b(a)-eH(a)}{a(a-b)U(a)} . \tag{3}
\]
The denominators are live; the replay independently tests all
used inverses for unit reduction.

**One first-gap ghost.** Five ghosts precede \(a\) in forward order.
The grade-six input after multiplication by \(A\) is zero there,
so they are roots of \(F_b-eH+UQ\) for one \(\deg Q\le3\).
If \(e=0\), the polynomial has degree at most four and is
identically zero, so \(U\mid F_b\). But \(F_b(0)=F_b(b)=0\) and
\(F_b'=X(X-b)U\), giving two distinct double roots at which \(U\)
is live; this is impossible for \(F_b/U\) of degree three.
So \(e\ne0\) and the five-ghost monic hull is
\((F_b-eH+UQ)/(-42e)\). Write \(\xi\) for the remaining forward
ghost, \(D=F_b(\rho)-eH(\rho)\). From \(R_6(\rho)=S_6(\rho)\),
\[
 (\rho-\xi)D=-42e S_6(\rho),\qquad
 (1-\xi)D=(1-\rho)D-42e S_6(\rho).
\]
In fact \(D\ne0\) since \(S_6\) is live at \(\rho\).
Use this cleared location of the reverse ghost in the two
quadratics (2), homogenizing to degree two. The first residual plus
twice the second is a unit modulo 101, with no division by \(D\)
or \(1-\xi\).

**Two first-gap ghosts.** Both are roots of \(w_0\) by the quartic
mark and have distinct clocks. This \(w_0\) is nonzero, because
otherwise \(IP_0\) and its derivative \(P_0\) vanish at the three
old clocks and zero, four distinct double roots of a degree-five
primitive. Thus \(w_0\) is exactly quadratic at a candidate.
The genuine grade-six row \(W(I[YP_0])-NW(YP_0)\) is zero at
both ghosts (all inclusive weighted donor values vanish).
Write its \(Z_6\) expression as \(\bar G Q+qH_{\rm bary}\).
Its effective clean polynomial \(Q_{\rm eff}\), after division
by \(\bar G\) only on the clean sites, is cubic or lower since
\(H_{\rm bary}/\bar G\) there is a fixed nonzero scalar times
\(U(1-Y)\). Interpolate it at the old three and \(A_0=1-a\),
where only the inclusive diagonal (3) contributes to the tap.
At both ghosts \(Q\) is zero. The remainder of \(Q_{\rm eff}\)
modulo \(w_0\) is therefore proportional to \((1-\rho)-Y\).
The first tested residual is its pseudo-remainder evaluated
at \(1-\rho\).

A second true row is \(\mathcal R^{\mathsf T}W(P_0)\in Z_6\), where
\(\mathcal R=CA-AC-A^2\). The true polynomial product/primitive
rule puts \(\mathcal R E_4\subset F_6\), with total pairing budget
\(4+6+1=11\). By the inclusive cut the row is zero on old and
first-gap ghost stages. At \(A_0\) it is
\(-d_a^2 b_a P_0(A_0)\), since the transpose commutator has
diagonal \(-d_a^2\) and there are no other inclusive nonzero donors.
The effective clean polynomial is a multiple of \(R_3\),
vanishing at all old sites, with multiplier a live scalar times
\(d_a^2\). The same remainder argument gives
\(d_a^2\) times the pseudo-remainder of \(R_3\) at \(1-\rho\).
In particular \(d_a=0\) is not divided out. The first residual
plus twice this second is again a unit modulo 101.
All ghost/clean coincidences are maintained, including ghost
clock zero; only the two genuinely distinct ghost roots are used.

## 5. Replay and Lean scope

Run `python3 replay.py` with SymPy. It exact-checks the
symmetric identities, norms, guards and contacts in `project.py`
and then performs the residue checks. It imports the arithmetic in
the sibling [constant closure](../dirk11-thirteen-invisible-six-constant-exclusion/replay.py);
`--arithmetic PATH` is available for an isolated scratch layout.
No precomputed large coefficient projection is required.

The residue tests concern finite-free \(\mathbb Z_{(101)}\) clock
algebras and their monic adjunctions, never an integral model of an
unknown tableau. Each coefficient inversion or pivot asserted to
be a unit is checked in the *whole* residue algebra before it is
used. The relevant multiplication determinant is then a unit
over the localized integral algebra, so its adjugate gives the
inverse there. Any characteristic-zero candidate supplies an
evaluation from these algebras into its coefficient field, and
a final unit cannot evaluate to zero. This also justifies the
consecutive cofactor pivots in the exact contact branch. Nothing
requires reduction of a ghost clock, arbitrary weight, or diagonal.

The exact symbolic and finite arithmetic above have independent Python
replay. The [Lean companion](../../lean/RKCert/ReviewedNative/DIRKOrderElevenInvisibleSixLinear.lean) certifies seven scalar identities, including the undivided pole contact, first-ghost mark, and two affine two-gap gates. The [Lean/Mathlib 4.36.0 audit](lean-audit-4.36.0.txt) reports ordinary mathematical axioms only. The rooted transfer and finite elimination are not an end-to-end Lean nonexistence theorem.
