# Finite clean geometry and an explicit late pivot in normalized DIRK11/13

This is a **finite necessary reduction, not an exclusion** of the normalized
one-active-dirty-label case. It uses the real, rooted-order-eleven,
13-stage, lower triangular `C(2),D(1),D(2)` and surplus hypotheses of
[the signed census](../causal-profile-reduction/dirk-order11-thirteen-signed-cubic-census.md).
It treats only the \((r,d,z,k)=(1,5,4,2)\) skeleton of the
[low-dirty census](../causal-profile-reduction/dirk-order11-thirteen-zero-one-low-dirty.md).
It says nothing about \(d=1\), the invisible rows, \(r=9\), or a tableau
without the stated normalization. The real numerical interval is still
**13–14**.

The five non-endpoint clean labels have at most six possible unordered
real sets. More precisely the ordered three latest interior labels are
among **12** real triples. One of these three literal diagonals is zero.
All candidate clock ratios below are roots of an exact irreducible
polynomial of degree 60; the same normalized skeleton over a
characteristic-zero field satisfying the displayed support assumptions
requires an element of degree 60 over \(\mathbb Q\). Existence of a
compatible full tableau at any of these points is **not** asserted.

## 1. Actual reflected rows and live ghost columns

Use reversed chronology, with \(N=A^{\mathsf T}\) in reverse order and
\(Y=\operatorname{diag}(y)=1-\operatorname{diag}(c)\). Write \(W(P)=bP(y)\).
The actual ghost dirties have \(b_i=0\), and the two actual active dirties
have opposite nonzero weights and equal \(g\) at one label \(\xi\). Write
\(B=b\) restricted to these two and zero elsewhere, \(V=1-\xi\), and \(D=NB\).
There are seven distinct clean physical rows including actual 0 and 1,
and all five non-endpoint clean rows are live, by the signed nodal-square
support test in the low-dirty census. The actual origin weight may be zero.

The genuine reflected cubic \(G_3=NW(Y^2)-W(Y^3/3)\) is a nonzero multiple
of \(B\). The latest active nonunit row is therefore one of the two dirty
actives, denoted \(j\), and \(V\ne0\). At this row the true first positive
power read gives \(A_{jj}=V/2\). Later active rows have reflected clock
zero and do not contribute to that read. It follows that
\(G_3=(V^3/6)B\) and \(D_j=b_jV/2\).

Put \(U=E_6^\perp\) and \(Z=E_5^\perp\cap\{v_T=0\}\), where \(T\) is the
actual terminal. Their dimensions are 2 and 3. Since \(B\) annihilates
\(E_7\), \(D\in U\). If \(D\) were proportional to \(B\), the subspace of
vectors whose two dirty coordinates agree would be invariant under \(A\)
and coordinate products. It contains every tree vector by induction.
Deleting the later forward member, adding its column to the earlier
member and merging their weights would preserve each tree output and
lower triangulation, contradicting the genuine thirteen-stage floor.
Thus \(B,D\) span \(U\).

In \(D\cdot g\), the five dirty clock aggregates annihilate degrees 0
through 3, since \(g\mathcal P_3(c)\subset E_6\). Either all five
aggregates vanish, or each is nonzero (four-point Vandermonde after
omitting any zero). The former would zero the ordinary \(D\) aggregate on
each dirty color-class, since \(g\) is constant and nonzero there. Then
annihilation of \(\mathcal P_5(c)\), the terminal-zero coordinate and the
six distinct nonterminal clean sites would force every clean \(D\) entry
zero, giving \(D\parallel B\). Thus \(D\) is nonzero at all four literal
ghost dirties and its aggregate at the active dirty pair is nonzero.
Cross-color coincidences of numerical clocks do not alter this argument.

Since \(YE_5\subset E_6\) and the terminal is zero in \(D\), \(YD\in Z\).
On two distinct \(D\)-live ghost coordinates, \(B=0\), so \(B,D,YD\) are
independent and span \(Z\). Therefore the actual, paid rows satisfy
\[
 \begin{split}
 G_4&=NW(Y^3)-W(Y^4/4)=aB+\mu D,\\
 G_5&=NW(Y^4)-W(Y^5/5)=a'B+\nu(Y)D,\quad \deg\nu\le1,\\
 ND&=a''B+(m+nY)D.
 \end{split}
\]
The first needs grade four against \(E_6\), the second grade five against
\(E_5\); unary extension gives \(ND\in Z\). Terminal zero uses the
literal terminal column and \(y_T=0\). These are not conditions of a
reversed RK tableau.

## 2. The literal suffix is \(T,j,u,v,w\) in reverse order

Let \(u,v,w\) be the first three distinct nonzero reflected clean labels,
chronologically; all three are physical live singletons. At the first
one, the only nonzero active donor labels are \(u,V\) (both dirty pair
members, if present, have label \(V\)). The true positive-power degree
one and degree two moments at \(u\) give \(u\ne V\) (otherwise a one-node
read requires half and third) and
\[
 d_u:=D_u/b_u=-\frac{u^3}{6V(V-u)}.
\]
The genuine \(G_4\) at \(u\), tested with \(Y(Y-u)(Y-V)\), gives
\(\mu=V(V-u)(V-u/2)\).

If a ghost occurs before the third regular \(w\), its only possible
nonzero ordinary donor labels are \(V,u,v\), allowing absent donors with
zero tap. At its zero-weight column the true first and second moment
are both zero, and the third is \(\mu D_i\). Apply
\(P=Y(Y-u)(Y-v)\): its only support contribution is \(P(V)D_i\), hence
\(P(V)=\mu\) because the ghost has \(D_i\ne0\).

The same equality would hold if the earlier forward member of the dirty
pair were before \(w\) in reverse. Its \(s=b_i V/2-D_i\) is nonzero since
\(D_i+D_j\ne0\) and \(b_i+b_j=0\). After removing all dirty taps at V,
its actual regular degree-one, two, three moments are
\(Vs,V^2s,(V^3-\mu)s\), respectively. This follows from \(G_3=(V^3/6)B\)
and calibrating \(a\) in \(G_4\) at \(j\), where its only nonzero donor
clock is \(V\) and \(D_j=b_j V/2\). Applying the same polynomial to the
remaining regular taps gives \((P(V)-\mu)s=0\).

In either event \(P(V)=\mu\) implies \(v=u/2\), since \(V(V-u)\ne0\).
But at the actual second clean \(v\), the same polynomial gives
\[
 (P(V)-\mu)D_v=b_v I P(v)=b_v\frac{v^3(2u-v)}{12}.
\]
Consequently \(v=2u\) as well, impossible. This proof also works if
\(V=v\) or a ghost shares a clean clock. It establishes both that no
ghost or early dirty precedes \(w\), and that \(u-2v\ne0\) without any
assumption that such a ghost exists. There are no other stages after
\(w\) in forward order beyond the five specified; the actual origin is
chronologically first and the terminal is a unique clean unit clock.

## 3. Undivided compensation and the third explicit diagonal

Set \(k_s=V(V-u)D_s/b_s\) for \(s=u,v,w\). The same true cubic test at
\(v\) gives
\[
 k_u=-u^3/6,\qquad k_v=\frac{v^3(2u-v)}{6(u-2v)}.
\]
In fact \(2u-v\ne0\): if zero then \(D_v=0\), and the genuine positive
moments on the regular donors \(u,v\) give a nonzero tap from \(u\) into
\(v\) in the reverse matrix (normalized tap \(-v^3/[6u(u-v)]\)). The
literal row \((ND)_v\) is then nonzero from that donor: the dirty donor's
tap is zero because only \(j\) occurs here, the terminal's \(D\) is zero,
and the own \(D_v\) is zero. This contradicts \(ND\in\langle B,D,YD\rangle\).
No division by \(D_v\) has been used before establishing this guard.

Use the genuine fourth-power reads \(G_5\) first at \(u\) and \(v\),
applying \(Y^4-(u+V)Y^3+uVY^2\) and \(Y(Y-V)(Y-u)(Y-v)\), respectively.
Their values give
\[
 \begin{split}
 \nu(u)&=(u+V)\mu+uV(V-u)(5V-3u)/10,\\
 \nu(v)&=(V+u+v)\mu+
     v^3(3v^2-5(V+u)v+10Vu)/(60d_v),\qquad d_v=D_v/b_v .
 \end{split}
\]
Thus \(\nu\) has fixed slope \(3V(u-V)(u-v)^2/[5(2u-v)]\).
At \(w\), put \(P_w=Y(Y-u)(Y-v)(Y-w)\). The read is
\((P_w(V)-\nu(w)+(u+v+w)\mu)D_w=b_w I P_w(w)\).
With
\[
 M=4wu^2-13wuv+4wv^2+u^2v+uv^2,\qquad
 L=3w^2-5w(u+v)+10uv,
\]
this is exactly
\[
 Mq=F,
 \qquad q=6k_w,
 \qquad F=w^3(2u-v)L.
\]
No division by \(M\) or \(k_w\) enters this equality.

For an actual regular reverse donor \(i\) of the clean column \(s\),
write \(a_{i,s}=b_iA_{i,s}/b_s\) with forward array indices. In each
column add \(k_s/[u(V-u)]\) just to the \(u\) tap (write the shifted taps
\(\bar a\)). The genuine degree-one, two, three moments on the now
ordinary donor set have targets
\(m_1=s^2/2\), \(m_2=s^3/3-k_s\),
\(m_3=s^4/4-3u k_s/2\), using only as many equations as donors at each
column. This is a linear change of the literal taps, rather than
discarding a stage. The actual \(ND\) relation implies
\(
 \sum_i k_i\bar a_{i,s}=(\alpha+\eta s)k_s
\)
for all three columns; the shift adds a common scalar to the affine
multiplier. This statement is **undivided**, even if \(k_w=0\).
At \(u\) and \(v\) the values of the affine function are respectively
\(u/2\) and \((u^3-3uv^2+v^3)/[2(u-2v)(2u-v)]\), by the two moment
Cramer reads. The three actual taps at \(w\) are given by the ordinary
three-node Cramer formula with the above compensating moments. The
resulting undivided affine test is \(A(q)=0\), where \(A\) is the
polynomial numerator checked in `replay.py` and the native scalar file.
An exact identity modulo \(Mq-F\) gives
\[
 M^2 A(q)=36w^4(u-w)^2(2u-v)(v-w)^2 J^2,
 \qquad J=wu^2-4wuv+wv^2+u^2v+uv^2.
\]
All factors outside \(J^2\) are nonzero by the true clean supports and
the proved guard. Therefore **\(J=0\)**, also when \(M=0\) or \(k_w=0\).

The literal third diagonal is unaffected by the shift at distinct \(u\).
Its Cramer numerator, times 12, is
\(S=3w^4-4(u+v)w^3+6uv w^2+(2v-u)q\). The second checked identity gives
\(MS=6w^2(u-w)(v-w)J\). Once the next section proves \(M\ne0\), this
forces \(S=0\) and \(A_{ww}=0\) in the literal array.

## 4. Exact finite Jacobi gate

The ordinary clock measure is exactly on the seven clean sites including
0 and 1, with possible zero origin mass. Its polynomial order ten
implies that the product of the five non-endpoint clean linear factors
is a scalar multiple of \(J_5+\lambda J_4\), where
\[
 J_4=42X^4-84X^3+56X^2-14X+1,\qquad
 J_5=(2X-1)(66X^4-132X^3+84X^2-18X+1).
\]
Indeed multiply the product by \(X(1-X)\) and the powers \(0,1,2,3\).
In degree at most five this four-condition kernel is exactly the span
of these two independent polynomials, by the positive moment Gram
matrix, and the degree-five coefficient is nonzero. The same assertion
holds after reflection \(X\mapsto1-X\) (or apply the rule directly in y).

Set \(x=u,t=v/u, d_*=4t-1-t^2\). The equality \(J=0\) yields
\(w=x t(1+t)/d_*\). If \(d_*=0\), then \(t(1+t)=0\), contrary to
\(t\ne0\) and \(d_*(-1)=-6\). The quotient \(d_*-t(1+t)\ne0\) as
\(w\ne u\). Define the polynomials
\[
 \begin{split}
 P(x,t)&=\frac{J_5(x)J_4(xt)-J_5(xt)J_4(x)}{x(1-t)},\\
 Q(x,t)&=\frac{d_*^{5}[J_5(x)J_4(w)-J_5(w)J_4(x)]}
                       {x[d_*-t(1+t)]} .
 \end{split}
\]
The divisions are exact polynomial factor cancellations, and their
values in our branch have nonzero denominators. The same clean
polynomial parameter at \(u,v,w\) forces \(P=Q=0\). The exact
\(x\)-resultant is a nonzero scalar times
\[
 t^{20}(t-1)^8(t-2)^8 F_{60}(t)
\]
with \(F_{60}\) irreducible over \(\mathbb Q\), reciprocal and of
degree 60. The first three factors are all excluded by the guards.
A linear subresultant has its leading coefficient coprime to
\(F_{60}\), so it determines exactly one possible \(x\) for each \(t\).
The exact rational isolation gives 12 real roots of \(F_{60}\), listed
in `replay.log`; hence **at most 12** ordered real triples. Swapping
\(u,v\) preserves \(J=0\), common \(\lambda\), and distinctness, and
replaces \(t\) by \(1/t\). The candidate solutions occur in unordered
pairs under this involution; this yields at most six unordered full
clean clock sets, since \(J_4,J_5\) are coprime and \(\lambda\) determines
all five non-endpoint clean labels. No claim is made that either order
of any pair satisfies the other tableau equations.

Finally \(M-J=3w(u^2-3uv+v^2)\), and the factor \(t^2-3t+1\) is coprime
to \(F_{60}\). Thus \(M\ne0\) on all possible triples. This closes the
potential zero-denominator branch **after** the undivided affine gate.
It also shows why neither divisions at an unknown dirty clock beyond
\(V(V-u)\) nor any good-reduction inference on a tableau is required.

## 5. Exact marked Volterra row and scope of verification

Let \(P=Y(Y-u)(Y-v)\) and \(W_C(P)=W(P)-P(V)B\), the actual polynomial
weight with the signed dirty pair removed. For
\(\mathcal R=CA-AC-A^2\), \(\mathcal R^\mathsf T=YN-NY-N^2\). The actual
primitive profiles give \(\mathcal R E_5\subset F_7\); ordinary pairing
with \(W(P)\) costs grade \(3+7=10\). Also \(B\) annihilates \(E_7\) and
\(\mathcal R E_5\subset E_7\); the terminal column is zero. Therefore
\(\mathcal R^\mathsf T W_C(P)\in Z\). This weighted input vanishes
strictly before \(w\) in reverse, and the diagonal at \(w\) in this
commutator is \(-A_{ww}^2=0\). Thus the row vanishes through \(w\),
including at \(u,v,j\). In \(Z=\langle B,D,YD\rangle\), the \(u,v\)
values kill the affine \(D\) multiplier, since \(D_u,D_v\ne0\); the
live \(B_j\) then kills the remaining coefficient. We obtain the literal
identity **\(\mathcal R^\mathsf T W_C(P)=0\)** on every physical row.

There is a further literal restriction before the **fourth** regular
stage in reverse. If a ghost or the earlier dirty-pair member lies
between \(w\) and that regular stage, its only available nonzero regular
donors are \(u,v,w\). Applying \(P_w=Y(Y-u)(Y-v)(Y-w)\) to its paid
moments gives
\[
 \nu(y_i)=P_w(V)+(u+v+w)\mu.
\]
For a ghost this uses \(D_i\ne0\). For the earlier dirty member remove
its dirty taps as in §2: calibrating \(a'\) at \(j\) supplies the fourth
regular moment \((V^4-\nu(V))s\), with the same \(s\ne0\). The nonzero
slope of \(\nu\) implies the exact prescribed reflected clock
\[
 y_i=w+\frac{M}{6(u-v)^2}.
\]
The available nonregular stages all have distinct numerical labels in
this segment, so at most one exists and it must be immediately after
\(w\) in reverse. Its actual tap from \(w\) is nonzero: if it vanished,
only \(u,v\) would contribute and the contradiction of §2 would apply
again. Therefore the global Volterra row, evaluated at \(i\), gives
\((y_i-w-A_{ii})N_{iw}\,b_w P(w)=0\), with the three factors after the
parenthesis nonzero. Its actual diagonal is thus
\(A_{ii}=M/[6(u-v)^2]\ne0\). This does not assert that the optional
nonregular stage actually exists.

`replay.py` independently expands the paid scalar identities, computes
the exact resultant/subresultant over the rationals, and performs
rational real-root isolation. No approximation, modular inference or
hardcoded tableau is used in its pass/fail conditions. The separately
reviewed Lean scalar module gives the core undivided affine and
explicit-diagonal polynomial identities plus the early-donor gate.
The group hypotheses and placement above are mathematical, and neither
this packet nor the grouped class closure is an unrestricted lower
endpoint change.
