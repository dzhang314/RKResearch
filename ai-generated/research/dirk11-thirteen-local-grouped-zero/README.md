# The grouped-zero fourth-head face is empty in normalized DIRK11/13

This excludes the last *grouped-zero* active part of the single-physical-
dirty-clock case. Use the [normalized signed cubic census](../causal-profile-reduction/dirk-order11-thirteen-signed-cubic-census.md):
actual rooted order eleven and literal lower triangulation, forward
\(C(2)\), genuine reflected \(D(1),D(2)\), and true grade-six surplus.
All physically nonzero \(g=Ac^2-c^3/3\) occur at one numerical clock
\(\xi\); the active dirty values are the same nonzero value; and
\(h=(A-\xi/2)g\). Assume that the **grouped** row \(\beta h\) has
zero aggregate at each label, but is physically nonzero at at least
two distinct exterior numerical labels. The cases of fewer exterior
labels and of variable active cubic were already
[excluded](../dirk11-thirteen-local-active/README.md).

The proof works in characteristic zero with the explicit normalization
and rank hypotheses; no unknown coefficient or clock is ordered.
The remaining active one-local case has **nonzero grouped \(\beta h\)**,
not merely nonzero individual entries. The real **13–14** stage
interval is unchanged.

## 1. Actual stage census with grouped-zero \(h\)

Use the one-local band \(F_4=\langle g,h\rangle\),
\(F_5=\langle g,h,Ch\rangle\), and
\(U_4=\langle g,h,Ch,C^2h\rangle\) of dimension four. The true terminal
alias argument from the [local-active note](../dirk11-thirteen-local-active/README.md)
gives
\[
 E_6=\mathcal P_5(c)+U_4+K e_T .
\]
Here \(K\) denotes the coefficient field. The literal origin and terminal
are \(g=h=0\), at 0 and 1 respectively. Let \(B\) be the row of actual
weights on the active dirty stages, zero elsewhere. Its ordinary
aggregate is zero and its support lies at \(\xi\). By \(g\) constant
nonzero on all active dirties and the true \(\beta gh=0\), their
aggregate \(h\)-weighted mass is also zero.

Set \(Y=\operatorname{diag}(1-c)\), \(N=A^{\mathsf T}\) in reverse
chronology, \(D=NB\), and \(V=1-\xi\ne0\).
The genuine cubic is \(G_3=(V^3/6)B\) and
\(U_0=E_6^\perp=\langle B,\beta h\rangle\); the latter follows since
the paid grade-four weighted row \(\beta h\) annihilates \(E_6\) and
is nonzero outside the core. In particular **no nonzero covector in
\(U_0\) can be supported just on one exterior numerical label**,
as it would force both independent coefficients zero.

The literal \(c^6\) column gives a monic sextic \(M\) with
\[
 M(c)=qg+L_2(c)h+\kappa e_T,\qquad \deg L_2\le2 .
\]
Aggregate this on each numerical clock using the actual weights.
The grouped \(g,h\) contributions are zero (all weighted \(g\) is
at \(\xi\) with zero sum). Thus \(M\) vanishes at every non-endpoint
label with nonzero ordinary mass. There are at least five such
labels, since otherwise the ordinary exact-through-degree-ten rule
contradicts the nonsingular fixed rational \(X(1-X)\,dX\) Gram
matrix on degree at most four by a nodal-hull test. In addition
\(M(0)=0\) at the literal origin. Therefore there are exactly five
non-endpoint ordinary labels, plus the actual endpoint labels
0 and 1. The six roots exclude 1, so \(M(1)=\kappa\ne0\), and
the aggregate ordinary mass at 1 is \(b_T\).

On an exterior fiber other than the actual terminal, all \(E_6\)
evaluations depend only on \(1,h\); the same is true on the \(g=0\)
subfiber at \(\xi\). Three rows there would give a nonzero local
annihilator independent of \(B\), impossible since \(\beta h\)
has two different exterior live labels. Nor can two such rows
share the same \(h\) value, by the same local contrast argument.
Consequently a nondirty live \(h\) fiber needs exactly **two active
rows with distinct nonzero \(h\)**, because its weighted \(h\)
aggregate is zero (also at \(\xi\), separately from the dirty
part). Its ordinary mass is nonzero, and its \(h^2\) aggregate
is nonzero. The latter follows by subtracting one \(h\) value
times the linear moment from the quadratic moment. At clock zero
there cannot be such a pair, since the actual origin is already
one \(g=h=0\) row of the class. At clock one all nonterminal rows
would have the same nonzero \(h\) by \(M(1)\ne0\); their individually
zero total weighted \(h\) would need an impossible repeated
signature. Thus every doubled live-head class is one of the five
ordinary non-endpoint labels.

On the active dirty rows themselves \(E_6\) depends only on
\(1,h\) since \(g\) is constant; only \(B\) is allowed to be
supported on those rows. Therefore their number \(k\) is at most
three. If \(k=2\) the two active dirty \(h\) values coincide by
their two signed sums. If \(k=3\), the \(h\) values are all
distinct: if two values occurred, the two vanishing signed
moments in \(1,h\) would require at least two members of each
class, and if all three values agreed there would be two
independent local contrasts. This also gives nonzero total
dirty square moment in the latter case by Vandermonde.

There are at least four distinct numerical labels with nonzero
grouped \(\beta h^2\), by its genuine moments in powers \(0,1,2\)
and the nonzero exterior square aggregates just established.
There are seven mandatory ordinary physical rows including
endpoints, \(k\) additional active dirty rows, and one extra
nondirty row for each doubled head class. With thirteen slots,
the only possibilities are:

* \(k=2\), four doubled ordinary non-endpoint head classes
  (possibly one at the numerical core but \(g=0\) there), and
  every other ordinary class singleton.
* \(k=3\), three doubled ordinary head classes outside \(\xi\);
  the fourth nonzero square aggregate is the actual active
  dirty core. Every other ordinary class is singleton.

All physical rows are charged in both cases, so there are no
ghost dirties or spare heads. The physical origin weight may
still be zero. At the least three distinct exterior head labels
a doubled class is made of two live rows with genuinely
different \(h\); hence their normalized \(D_i/b_i\) differ
since \(D\) is a nonzero linear combination of \(\beta h,B\)
with nonzero fourth-head coefficient. The coefficient is
nonzero by the genuine first regular read: it has no cubic
read on that row and a single later dirty clock \(V\), which
requires a nonzero aggregate dirty tap. Equivalently use
the first-clean reverse cutoff if \(D\) were purely core.

## 2. Lift the true class-sum head in the grade-six flag

The ordinary seven-label quadrature gives the same Jacobi pencil
\(J_5+\lambda J_4\) as the [earlier macro reduction](../dirk11-thirteen-one-active-macro/README.md).
Work in the reflected numerical variable. Set \(K_6(X)=(X-1)\)
times the monic hull of the five ordinary non-endpoint labels.
On each clean ordinary nonterminal label, distribute the
barycentric mass \(1/K_6'(s)\) among its one or two physical
rows proportional to their actual weights divided by their
ordinary aggregate mass \(\mu_s\). At the physical origin use
its literal singleton entry directly, even if unweighted.
Set the row to zero on the dirty core and at the terminal.
It annihilates \(\mathcal P_4(c)\) by class sums and barycentric
interpolation and annihilates \(g,h\) by literal support and
the grouped \(h\) read; this includes a clean clock that
coincides numerically with the dirty core. Rescale once to call
the row \(H\). For every live non-endpoint ordinary physical
row \(i\) of label \(s=y_i\),
\[
 H_i/b_i=s J_4(s).
\]
The proof is the same fixed \(X(1-X)J_4\) monic-cardinal
quadrature formula as in the [grade-six packet](../dirk11-thirteen-fourth-clean/README.md),
using \(\mu_s\) rather than an individual physical weight.

The genuine terminal-out annihilator of \(E_4\) is now exactly
\[
 Z_6=\langle B,D,YD,Y^2D,H\rangle .
\]
Indeed \(D,YD,Y^2D\) are independent **on the exterior classes**
by at least three distinct live \(h\) clocks. Their clean
class sums are zero (as are those of \(B\)), while \(H\) has
nonzero class sums. They all lie in the actual terminal-out
annihilator of dimension five. The previous
\(Z_5=\langle B,D,YD\rangle\), its paid \(G_5\) and \(ND\)
rows, and the new \(G_6,N(YD)\) in \(Z_6\) therefore give
exactly all the compensated scalar and marked formulas of
the grade-six packet.

## 3. Remove repeated physical debuts without losing any donor

Call a dirty stage **effective** if \(D_i-(V/2)B_i\ne0\).
This is only a label for its contribution to the compensated
marked reads: ordinary weighted taps from all actual dirty rows
are still included in their aggregate \(D\) at clock \(V\).
The latest active dirty stage \(j\) has diagonal \(V/2\) and is
silent in these reads. If \(k=2\) the earlier dirty row is also
silent, because the active pair has common \(h\) and the
coefficient is calibrated at \(j\). If \(k=3\), both earlier
dirty stages are effective (their \(h\) differ from that at
\(j\)), and have the same numerical clock \(V\).

Take \(u,v,w,a,b\) to be the successive first appearances of
the five distinct live ordinary nonzero non-endpoint reflected
clocks. No physical ordinary unit duplicate is present from
the stage census. At \(u\), the usual two true positive-power
moments fix \(u\ne V\), \(D_u/b_u\), and the genuine quartic
coefficient \(\mu=V(V-u)(V-u/2)\). Every live \(u\) row
before the first different ordinary \(v\) has the same
normalized \(D/b\) by those two literal moments. More
generally the cubic test \(P=Y(Y-u)(Y-v)\) at either \(u\)
or \(v\) through the strict prefix before \(w\) reads
\((P(V)-\mu)D_i=b_i I P(y_i)\). At the first \(v\), this
proves \(v\ne u/2\), since otherwise \(P(V)=\mu\) forces
\(v=2u\). Hence each \(u,v\) can occur physically only once
before \(w\): any repeat has distinct \(h\), so distinct
normalized \(D/b\), impossible. The same polynomial test
excludes any **effective** dirty before \(w\), after its
actual calibration at \(j\); it would again give \(P(V)=\mu\).
The \(D_v=0\) contradiction via \(ND\) thus has exactly one
regular \(u\) donor, and the common polynomial mask
\(bP(y)-P(V)B\) retains its first nonzero regular pivot at \(w\)
(silent dirty rows do not enter it). Its genuine Volterra
row vanishes from its \(j,u,v\) entries in \(Z_5\), forcing
\(A_{ww}=0\). The undivided fourth moment and diagonal
identity give the same \(J=0\), so the degree-60 macro
reduction applies.

It remains to exclude physical repeats **after \(w\)**,
without silently pretending donors at a repeated label are
distinct. Use the shift notation of the grade-six packet:
\(k_i=V(V-u)D_i/b_i\) at every live ordinary column \(i\).
The compensated scalar moment targets at \(s=y_i\) for
degrees \(1,\dots,4\) are \(m_n(s)+\ell_n(s)k_i\);
degree five adds \(\rho_2(s)k_i+\chi h_{\rm macro}(s)\)
to \(s^6/6\), where \(h_{\rm macro}(s)=sJ_4(s)\) is the
value of \(H_i/b_i\), **constant on each ordinary fiber**.

Before \(a\), all possible nonzero regular donor labels form
the set \(S_3=\{u,v,w\}\), even if a physical row repeats a
label. At each receiver, aggregate its actual taps by these
labels, assigning zero to absent donors, and shift the one
\(u\) aggregate. These are the three Cramer taps for the
first three compensated scalar moments, hence affine in
the receiver's \(k_i\): write their coefficients
\(\alpha_r(s),\eta_r(s)\). The fourth scalar moment fixes
\(k_i\) if
\[
 \Lambda_4(s)=\sum_{r\in S_3} r^4\eta_r(s)-\ell_4(s)\ne0.
\]
This coefficient is a unit at \(s=u,v,w\) in the checked
degree-60 algebra. The original first receiver of label \(s\)
also obeyed exactly this equation on the same possible
donor set, padding its then-absent taps with zeros.
Consequently a repeat of any such \(s\) before \(a\) would
have the same \(k\) as its first physical occurrence, contrary
to its two distinct forward \(h\) values.

Thus the existing fourth-regular argument applies. If any
effective dirty precedes \(a\) after \(w\), the scalar quartic
test forces all such rows to have the same \(z=w+M/[6(u-v)^2]\)
of the macro packet. Calibrate at the **first** such row:
with no repeated ordinary rows intervening, its literal
Volterra diagonal is \(z-w\). If a silent dirty could
intervene, its true first three zero regular moment targets
kill its \(w\) tap exactly as in the local-active transfer;
in these two counted profiles no effective case needs that
extra omission. At \(a\) the difference of the two marked
reads cancels **all** possible effective taps, since they
have the same numerical \(z\), so the previous
prime-101 optional-fourth residual excludes them as before.

There is now no effective nonregular before \(a\).
The first four actual regular \(k\) values fix the two
quadratic profiles \(f_2,\rho_2\) and head coefficients
\(\theta,\chi\) exactly as in the closed grade-six packet.
Before \(b\), use the possible numerical donor set
\(S_4=\{u,v,w,a\}\). The first four scalar moments give
aggregate taps affine in \(k_i\), and the fifth fixes it if
\[
 \Lambda_5(s)=\sum_{r\in S_4}r^5\eta_r(s)-\rho_2(s)\ne0.
\]
The scalar offset \(\chi h_{\rm macro}(s)\) is the same at
*every* physical receiver of \(s\), which used the actual
class-sum lift above. The extra check proves all four
\(\Lambda_5\) are units through both fourth-tap roots in
the degree-240 algebra. Thus no repeated physical regular
receiver can be before \(b\) either. All these scalar
repeat tests are independent of any intervening effective
dirty taps, as those were included in the ordinary
aggregate \(D_i\). Now take the first effective dirty
after \(a\) and before \(b\), if one exists: the original
fifth-optional Sylvester determinant excludes it. If none
exists, the fifth-regular determinant excludes its actual
\(b\) receiver. This exhausts the literal chronology.

## Exact verification

The independent seven repeat guards use prime **103**, not
101. The executable replay imports only the frozen quotient
arithmetic and macro constructors from the neighboring
grade-six packet. Every divider and each checked guard
has its inverse multiplied back to one in the residue ring.
The same finite-free multiplication determinant lift over
\(\mathbb Z_{(103)}\) as in that packet proves
characteristic-zero nonvanishing; it is not a reduction of
an unknown tableau. The earlier contradictions still use
their independent prime-101 certificate.

The accompanying Lean scalar module checks the exact
uniqueness implication for a common affine moment read
and the nonzero quadratic aggregate from two distinct
live \(h\) entries with zero linear aggregate. The
underlying true rooted grading, block counts, and
chronology are proved in the text; the arithmetic replay
is not an end-to-end axiomatic HasOrder theorem.
