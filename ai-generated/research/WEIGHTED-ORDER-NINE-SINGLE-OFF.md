# The single-off shift-two weighted order-nine branch

A strictly explicit twelve-stage tableau with live last weighted output,
exact to rooted size nine for
\(\ell_2(P)=\frac12\int_0^1(1-X)^2P(X)\,dX\), cannot have a single
distinct nonzero-defect clock over any characteristic-zero field.
No ordering is assumed. The arithmetic that finishes both branches
is checked in Lean; the weighted forward-rank bridge below is
mathematical, not a new end-to-end theorem in the reviewed
ordinary `HasOrder` API.

In combination with the other weighted off-census notes, this
gives the **shift-two weighted size-nine stage floor of 13**
over characteristic zero. Inactive trailing stages are removed
by strict truncation; the old weighted floor requires at least
twelve active physical positions. This does not settle the
distinct shift-one problem or change the ordinary order-eleven
endpoint.

## Weighted inputs, and audit of the forward bootstrap

Use the exact ranks and terminal conclusions of
[FourTap](WEIGHTED-ORDER-NINE-FOUR-TAP.md) and
[Off Gates](WEIGHTED-ORDER-NINE-OFF-GATES.md).
Here \(g=Ac-c^2/2,\ h=Ag\), and \(a\) denotes the first nonzero
clock, which is the sole off clock; a clean row has \(g_i=0\).
The separated grade-four pure ranks are
\(\dim F_3=2,\dim F_4=3,\dim E_4=8\).
The last output is live at clock 1, \(3\beta A=\beta Y\),
\(Y=I-C\), and
\[
               H_i=E_i+Ke_{12},\qquad \dim H_5=10 .
\]
On \(E_4\) the first seven physical evaluations are independent.
The actual late vector \(v\in E_4\) zero there has \(v_8\ne0\),
\(\beta A^4v\ne0\), and \(c_8=c_9=\theta\ne1\) with
\((C-\theta)v\in K e_{12}\). In particular
\((C-\theta)(C-I)v=0\).

For clarity, the audited forward bootstrap uses the existing
`RKCert.ReviewedNative.OneOff*` source for purely algebraic lemmas,
not the ordinary order-nine endpoint or the ordinary
`one_off_impossible` interface. The weight-sensitive inputs
are replaced as follows.

1. **Constant amplitude and global normal form.**
   In `OneOffFirstH.first_h_of_actual`, the only uses of the
   ordinary order premise are separation through degree three
   and nonzero clock. Both hold already (the latter is also
   \(\beta c=\ell_2(X)\ne0\)). Thus the underlying forward
   `origin_of_single_off`, `quadratic_defect_form`,
   `rank_two_span`, and `first_h_split` produce the same
   Origin, rank-two form and FirstH. In
   `constant_amplitude_of_single_off_of_capacity`, the
   remaining jobs are precisely the three square branches
   `constant_amplitude_of_dependent_square`,
   `independent_square_on_first_impossible`, and
   `independent_square_off_first_impossible`; these use
   strictness, separated \(E_4\), ranks \(F_3,F_4\), and that
   forward data, not an output row. In particular the
   first \(h\)-receiver is clean at a nonzero clock \(d\),
   and \(g\) has amplitude \(-a^2/2\) on all off sites.
   The pure `global_normal_from_amplitude` then gives
   \(F_4=Kg+hP_{\le1}(C)\), the actual \(Ah=(d-C)h\),
   and the two polynomial primitive residuals used below.
   The pure `first_doubled_clean_clock` and
   `new_clean_clock_h` give three distinct clean labels
   with nonzero \(h\), one of them \(2d\). All these pure
   source lemmas can be used over characteristic zero
   with the weighted separation in place of the ordinary one.

2. **No identical physical rows, and the first four.**
   An identical incoming row could be contracted by taking
   the earlier row, moving all later-column contributions
   to it and adding the two output coefficients. Strict
   chronology is preserved, and induction on each tree
   preserves its stages on every surviving row and its
   output exactly. Hence this surgery also preserves the
   weighted row tests and contradicts the old weighted
   twelve-stage floor. This replaces the only ordinary-order
   inference in `no_repeat_in_first_chart_order9`:
   `prefix_equal_physical_rows` itself is pure. The
   explicit forward progression in `first_four_at_order9`
   then puts the first four physical features
   \((c,g,H)\), with \(H=h/a\), at
   \[
   (0,0,0),\quad(a,-a^2/2,0),\quad(d,0,H_0(d)),
        \quad(t,0,d^2),
   \qquad t=2d,\quad H_0(X)=X^2(X-t)/(4d).
   \]
   In that progression the first off row cannot be delayed
   past the origin copy, the first \(h\)-row cannot be
   delayed past the first two features, and the first
   doubled-clock feature cannot be delayed past the
   first three. The cited forward selector then gives the
   identical physical rows if there were a delay.

3. **Grade-five anchored alias, and defect separation.**
   The polynomial part of any grade-five numeric relation
   with zero polynomial defects, or any represented pure
   column, lies in the line \(KR_5\) where
   \(R_5=X(66X^4-120X^3+72X^2-16X+1)\).
   Indeed its value at the origin is zero and its exact
   \(\ell_2(X^k P)\) moments for \(k=0,1,2,3\) are zero.
   This is the weighted replacement for
   `wide_kernel_poly` and `normal_profile_defect_poly`
   (the unweighted Radau polynomial is **not** reused).
   To obtain \(gh=0\), use the eleven genuine coefficients
   of \(P(c)+\alpha g+hQ_2(c)+\tau gh\), all rooted through
   grade five. If \(E_5\) has rank at most nine, there is a
   nonzero relation also killing the fifth-degree polynomial
   coefficient; then its polynomial part is zero. If \(E_5\)
   has rank ten, \(e_{12}\in E_5\) because \(\dim H_5=10\).
   Its actual products with \(g\) and \(h\) pay the pure
   grade-seven/eight tests and give \(g_{12}=h_{12}=0\).
   Any relation then has polynomial part vanishing at 1,
   hence zero since \(R_5(1)=3\). In either case a nonzero
   relation \(\alpha g+hQ_2(c)+\tau gh=0\) has \(\alpha=0\)
   from the first off row, and \(Q_2=0\) from the three
   distinct clean nonzero \(h\) labels. Thus \(\tau\ne0\)
   and \(gh=0\). This supplies the precise replacement
   for the weighted steps in `OneOffDefectSeparation\).

4. **Fifth feature and the full grade-five chart.**
   The forward relations `four_feature_residuals` and
   `normal_clean_clocks` in the proof of
   `order9_fifth_feature` now apply: an off row repeats
   the first off feature by \(gh=0\), and at the three
   possible clean clocks \(0,d,t\), rows at zero and \(d\)
   are the earlier features. The just-proved physical
   no-repeat selector leaves the fifth row clean at \(t\)
   with its scalar \(H\)-value different from \(d^2\).
   The range \(U=P_{\le5}(c)+Kg+hP_{\le2}(c)\) has rank at
   least nine: a relation with degree-five coefficient zero
   has zero polynomial part by the weighted alias, then
   has zero remaining coefficients by the three clean
   \(h\) clocks and the first off row. If \(E_5\) were
   rank nine, \(U=E_5\), so the pure \(A(CH)\) would be
   represented in \(U\). On the two doubled rows at \(t\)
   its genuine intercept, linear in \(H\), is \(d^4/3\ne0\)
   (the forward `clockAg_doubled` calculation, divided
   by \(a\); also `doubledIntercept` in the new leaf).
   This intercept must equal the polynomial part at \(t\),
   so \(R_5(t)\ne0\). Any relation in \(U\) now has
   polynomial part zero from those doubled rows, hence
   all coefficients zero, contradicting rank nine.
   Thus \(E_5\) has rank ten. As above \(e_{12}\in E_5\),
   \(g_{12}=h_{12}=0\), and \(R_5(1)\ne0\).
   Any relation in \(U\) has zero polynomial part by
   the endpoint, and zero other coefficients. Therefore
   \(U=E_5\) of rank ten, and the same doubled intercept
   proves \(R_5(t)\ne0\) unconditionally. Also \(t\ne1\):
   representing \(e_{12}\) in \(U\) gives polynomial
   value zero at \(t\) from the pair but one at 1.

5. **No causal same-clock interpolation.**
   This replaces the ordinary reverse input in
   `OrderNineCausalInterpolation`. In the row annihilator
   \(T=E_5^\perp\) of dimension two, the nonzero seed
   \(h_2=4\beta YA-\beta Y^2\) and \(h_2 A,h_2Y\) all lie
   in \(T\). Its nonzero last preterminal coefficient
   was proved in the four-tap setup. No nonzero subspace
   \(W\subset T\) jointly invariant under right \(A,Y\)
   can exist. If it contains \(h_2\), the paid inverse
   clock interpolation \(Y^\dagger\) gives
   \(\beta Y-4\beta Y A Y^\dagger\in W\); nilpotence of
   \(A Y^\dagger\) then gives \(\beta Y\in W\), contrary
   to its nonzero constant read. If \(h_2\notin W\),
   \(T=W+Kh_2\) is itself invariant (the two images of
   \(h_2\) lie in \(T\)), the same contradiction.
   For a next stage whose predecessors' \(E_4\)
   evaluations are independent, a same-clock affine
   contrast killing \(E_5\) has its \(A\)-image supported
   on exactly those predecessors and killing \(E_4\),
   hence zero. Being a clock eigenrow, it generates the
   forbidden invariant line. This applies up to the
   seventh stage here because the first seven \(E_4\)
   evaluations are independent by the earlier weighted
   four-tap argument.

6. **Sixth feature.**
   Now the forward `cleanClockTest_action` of
   `OneOffSixth` applies exactly as in that source.
   The sixth row cannot be off (same feature as row two)
   or at \(t\) (affine interpolation between rows four
   and five at this clock), by the preceding causal
   contradiction. Its clean clock \(z\) satisfies
   \[
        0=z^2(z-2d)^2/4+(d/a)(2d-z)h_6,
        \qquad H_6=H_0(z) .
   \]
   The first equation uses the actual grade-three
   clean-clock test zero on all five predecessors.
   The too-small labels \(z=0,d\) would again interpolate
   an earlier feature, so \(z\notin\{0,d,t\}\).
   No ordinary endpoint formula is used here.

## A weight-independent seventh-row dichotomy

Let \(J=A(CH)\), \(V=Ac^4-c^5/5+2a^2h\), both pure of
grade five. At any clean row \(x=c_i\) whose predecessors
are among the first six features, their physical values
are the masked forward functions \(j(d,z,x,H_i)\) and
\(v(d,z,x,H_i)\) of `OneOffSeventhActions.order9_actions_seven`;
that lemma uses only the global normal form and the actual
allowed predecessor features. Explicitly put
\[
  m_1=x^2/2+2H,\quad m_2=x^3/3+(4d/3)H,\quad
  m_3=x^4/4+(2d^2-dx)H .
\]
The two functions are
\[
\begin{split}
j &= 2d(d-x)H +
        ((z-d)m_3-d(3z-2d)m_2+2d^2z m_1)/(4d),\\
v &= (3d+z)m_3-(2d^2+3dz)m_2+2d^2z m_1-x^5/5 .
\end{split}
\]
These come from interpolating \(CH\) and \(c^4\) on the
first six physical features, then using \(Ah\) and the
three pure normal-form primitive equations; the cited
source has no order premise in this action calculation.
Both functions apply to all early clean rows (including
the seventh if clean).

The single pure combination \(W=V-(4d/5)J\) avoids
any unweighted seventh-row endpoint arithmetic. Its
literal value in the action chart is
\[
  -\frac{4d}{5}(x^2-2d^2)H+
       \frac{(x-t)(x-z)(4dH-x^2(x-t))}{5}.
\]
This is the checked `masterResidual` after scaling by 60.
On the first doubled pair at \(t\) the literal intercept
of \(W\) is zero; its degree-five polynomial part in
\(U\) therefore vanishes at \(t\), so is zero since it
is a multiple of \(R_5\) and \(R_5(t)\ne0\).
On the three distinct clean nonzero-\(H\) labels \(d,t,z\)
its quadratic multiplier of \(H\) is then necessarily
\(-4d(X^2-2d^2)/5\) by interpolation. This is
the full value formula for pure \(W\) on every clean row.

The seventh row is clean (an off row repeats the
off feature and violates the causal no-interpolation
lemma) and cannot be at \(t\) by the existing doubled
pair. The two formulas for its value of \(W\) therefore
give either its clock equals \(z\) or its feature
has \(H=H_0(x)\). In the second case \(x\) cannot be
\(0,d\) by the same causal rule. If its clock is \(z\),
its \(H\)-value differs from that of row six by the rule.
This gives exactly the two required placements:
a new calibrated clean clock, or a true second doubled
clean fibre at \(z\).

## The tied terminal prefix and two exact scalar exits

Return to the late witness \(v\) from the four-tap theorem,
with its grade-four model \(P\) and actual form
\(P(c)+\alpha g+H Q_1(c)\), \(\deg Q_1\le1\).
Here \(P\ne0\) because \(\beta A^4v\ne0\).
The tied rows 8 and 9 must be clean: if row 8 were off its
\(v\)-value would equal row two, and if row 9 were off its
\(Av\)-value would equal row two by the degree-five chart.
Both equalities contradict the literal nonzero respective
values (the adjacent edge from 8 to 9 is live).
Also their common clock \(\theta\) did not appear at any
earlier clean row. Indeed that earlier row has \(v=0\)
while row 8 has \(v_8\ne0\), so the \(H\)-values differ
at that common clean clock. But \(Av\) is zero at all
earlier rows **and** at row 8, and its profile is affine
in \(H\) at each clean clock, forcing \(Av_9=0\).
The actual doubled pair at \(t\) gives \(P(t)=Q_1(t)=0\),
and origin gives \(P(0)=0\).

* **The seventh row is new, with \(H_0(x)\).**
  At the clean predecessor clocks \(0,d,t,z,x\),
  \(P+H_0 Q_1\) vanishes, including \(t\) where both parts
  vanish. Its degree is at most four, so \(P=-H_0 Q_1\).
  Since \(Q_1\) has root \(t\) and \(P\ne0\), \(P\) is a
  nonzero multiple of \(X^2(X-t)^2\).
  The numeric identity \((C-\theta)(C-I)v=0\)
  pays the three tests, after multiplying by \(X^k\),
  \(0\le k\le2\), for the monic cubic
  \((X-t)^2(X-\theta)\) against \(X^2(1-X)^3\).
  The paid degree-two Gram forces it to be the scalar
  normalization of \(33X^3-45X^2+18X-2\).
  That cubic is squarefree by
  \[
  (138-297X)C+(99X^2-91X+16)C'=12.
  \]
  This contradicts the double root at \(t\), without
  positivity or a real-root hypothesis.
* **The seventh row doubles \(z\).**
  Both doubled fibres force \(Q_1(t)=Q_1(z)=0\), hence \(Q_1=0\).
  The model \(P\) has the four distinct roots \(0,d,t,z\)
  and degree at most four; by scaling \(v\) take
  \(P=X(X-d)(X-t)(X-z)\). The same numeric identity
  pays the three zero \(X(1-X)^3\) moments of the monic
  internal polynomial
  \((X-d)(X-2d)(X-z)(X-\theta)\).
  The actual column \(Av\) in grade five has polynomial
  part \(JP+\lambda R_5\), since the difference from
  its formal model \(JP\) is a grade-five alias.
  Its two zero values at each of the earlier fibres
  force its polynomial part to vanish at \(t,z\).
  Hence the actual primitive minor is
  \[
                  JP(2d)R_5(z)-JP(z)R_5(2d)=0.
  \]
  No value of \(R_5\) is cancelled here.
  Multiply by 60 and remove only the factor
  \(2d z(z-2d)\), nonzero by the proven earlier distinct
  clocks and paid 2. The three weighted moments and the
  divided primitive minor admit an explicit integral
  certificate with nonzero constant
  \[
     D_{\rm fibres}=
     138826727020507759465570336482168183591197853507127031118116899043238017964154174903410273637500000 .
  \]
  `OneOffShiftTwoGate.twiceDoubledImpossible` checks
  the moment coefficients, the exact division identity,
  the integer coefficient certificate, and field transfer.
  No rational Gröbner computation is trusted by Lean.

The two cases exhaust the audited first-seven chart.
The arithmetic also works over finite paid fields with
\(11!\ne0\) and \(D_{\rm fibres}\ne0\) for the double-fibre
case (the new-clock cubic uses only paid constants).
The whole forward bootstrap here is asserted over characteristic
zero, matching the scope of the cited pure forward
normal-form lemmas; the finite arithmetic conditions alone
are not asserted to port those entire lemmas to every
positive-characteristic field.

## Remaining ordinary order-eleven work

The resulting shift-two bound applies to **any** actual weighted
row, not only \(\beta=bA^2\). The 17-row ordinary order-eleven
detector with \(g=5,L=5,k=11\) also uses **shift one** for the
reweighted size-nine output in its augmented branch; its
size-floor guard needs \(k+1<N_*\) at every such shift.
Even with both weights finished, the measured one-spare
rank-spike case needs a new argument (the current
reanchor would reduce \(L\) below five and raise the physical
cutoff), and a cutoff at eleven coordinates produces a
dense size-six decoder at its known **sharp** width 11.
Extra ordinary-tail structure or a sharper early cutoff
is needed. No separate inactivity check is needed for the
ordinary final row: strict truncation and the established
17-stage lower bound force it live at stage 17.
