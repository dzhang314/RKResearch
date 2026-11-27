# A Hadamard and tap obstruction at weighted order nine

This extends [the four-tap terminal calculation](WEIGHTED-ORDER-NINE-FOUR-TAP.md).
Let a last-active twelve-row explicit tableau be exact on all rooted
stage profiles through size nine for \(\ell_m(P)=\int_0^1(1-X)^mP(X)\,dX/m!\).
The coefficient field need only satisfy \((m+9)!\ne0\). Use \(d=Ac-c^2/2\),
call a state **off** if its quadratic defect is nonzero and **clean**
otherwise, and count distinct clocks separately on the two branches.
No stage floor needs nonnegative output coefficients.

**Results.**
* Exactly four distinct off clocks are impossible, for any such shift.
* With exactly five distinct off clocks, rows 8 and 9 are at the same clock
  but row 8 is off and row 9 is clean. The first eight physical rows contain
  all five off clocks, each carrying a nonzero aggregate for the third
  tap \(\beta A^3\). The stage-10 clock satisfies
  \((m+4)(1-c_{10})=(m+2)(1-c_9)\).
* For exactly five off clocks, there are not seven distinct clean clocks.
  At shift \(m=2\), five distinct clean clocks are impossible when
  \(65803293\ne0\) in the field, in particular over characteristic zero.
  The case of six distinct clean clocks, and the other off-clock counts,
  are not excluded.

This is a branch reduction of the weighted problem. It is not an improved
unrestricted order-nine stage bound, nor a new order-eleven endpoint.

## The true physical late spaces

The preceding four-tap result gives the live consecutive suffix 8–12,
\(c_{12}=1\), \((m+1)\beta A=\beta Y\) with \(Y=I-C\), and an actual
\(v\in E_4\) zero on rows 1–7 with \(U=\beta A^3v\ne0\) and
\(T=\beta A^4v\ne0\). Put
\[
 \eta_i=A^iv,\quad \mu_i=\beta\eta_i,\quad V=\mu_2,\quad
 a=U/T,\quad y=1-c_8=1-c_9=(m+4)/a,\quad y_i=1-c_i .
\]
Here the \(y_i\) in this note use physical one-based stage indices.
All four adjacent edges in this suffix are nonzero, so \(\eta_i\)
has leading index \(8+i\). The four-word result also says
\(y_{10}\ne y,\ y_{11}\ne0,\ (Y-y)v\in K e_{12}\),
\(yV=(m+3)U\), and \(y\mu_1=(m+2)V\).

Write \(H_j=E_j+K e_{12}\). On the part of \(H_4\) zero through row 7,
the no-top assertion gives \(\mu_3=a\mu_4\) as linear row restrictions.
The other exceptional identities, including support of \((Y-y)\),
then hold on the entire late space: they hold wherever \(\mu_3\ne0\)
with the same constants, and subtract the known visible vector from
its translate by a vector in the \(\mu_3\)-kernel. On that kernel the
top and penultimate reads, using the actual live paths, force
coordinates 8 and 9 zero. The clock relation forces coordinate 10
zero. The proportional first tap is also zero, forcing coordinate 11
zero using the live last edge. Consequently
\[
 H_4\cap\{\text{zero on rows 1--7}\}=\langle v,e_{12}\rangle .
\]
The [paid reverse counts](../lower-bounds/paid-beta/separated-pure/ZERO-OR-ONE-SPARE-DETECTOR-CUTOFF.md)
give \(\dim H_4=9,\dim H_5\le10,\dim H_6\le11\).
Thus the early seven evaluations have rank seven. Adding the independent
late pivots \(\eta_1,\eta_2\) supplies the exact subsequent late spaces
\[
 H_5^{\rm late}=\langle v,\eta_1,e_{12}\rangle,\qquad
 H_6^{\rm late}=\langle v,\eta_1,\eta_2,e_{12}\rangle.
\]
The reverse seed \(h_2=(m+2)\beta YA-\beta Y^2\) annihilates \(H_6\).
At row 11, \((m+1)\beta_{12}a_{12,11}=\beta_{11}y_{11}\) is nonzero,
so its coefficient there is \(-\beta_{11}y_{11}^2\ne0\).
It follows that \(H_6=\ker h_2\). The full first seed identity gives
\[
                    h_2=(m+1)(m+2)\rho-\beta Y^2,\qquad \rho=\beta A^2.
\]

## A third clock resonance from an actual rooted product

In the terminal Krylov basis, the earlier one-clock equations
specialize to
\[
 (Y-y)\eta_1=-\eta_2,\qquad
 (Y-y)\eta_2=(y_{10}-y)\eta_2+q\eta_3+q' e_{12},\qquad
 q=m+2-a y_{10}.
\]
For the first identity the \(\eta_2\) coefficient is
\(m+3-a y=-1\). The \(\eta_3\) coefficient is zero by
\(yV=(m+3)U\) and the word \(\beta AY\eta_1=(m+2)U\).
The endpoint coefficient is zero by \(y\mu_1=(m+2)V\)
and \(\beta Y\eta_1=(m+1)V\). The second identity only
uses the leading and first shifted coefficient of \(Y\eta_2\).

If \(q\ne0\), the actual coordinatewise product \(u=v\odot d\)
belongs to \(F_6\cap H_6^{\rm late}\). Its clock shift \((Y-y)u\)
is supported on row 12, since \((Y-y)v\) is. Comparing the
\(\eta_3\) and \(\eta_2\) coefficients in the displayed identities
makes the \(\eta_2\) and then the \(\eta_1\) coefficients of \(u\) zero.
So \(u=r v+s e_{12}\). The two paid pure tests \(\beta A u=0\)
and \(\beta u=0\), with \(\mu_1\beta_{12}\ne0\),
give \(u=0\). This is pointwise even at sites whose output weight is zero.
In particular row 8 is clean when \(q\ne0\).

Independently, \(\beta_9\) and \(\rho_9\) cannot both vanish. If they did,
\(h_2e_9=0\) would place \(e_9\) in \(H_6^{\rm late}\).
Write \(e_9=b_1\eta_1+b_2\eta_2+b_4e_{12}\); its leading
index forces \(b_1\ne0\). Its clock eigenvalue is \(y\), so
\((y_{10}-y)b_2=b_1\) and \(q b_2=0\).
Also \(\rho_9=b_1U+b_2T=0\) gives \(b_2=-a b_1\).
The two clock equations would give \(a y_{10}=m+3\) and
\(a y_{10}=m+2\), a contradiction.

For later use, in the full terminal basis write the actual \(e_9\)
as \(b_1\eta_1+b_2\eta_2+b_3\eta_3+b_4\eta_4\), \(b_1\ne0\);
then always \((y_{10}-y)b_2=b_1\).
If \(q=0\), this yields
\[
              2\rho_9=b_1 U,\qquad (\beta A^3)_9=b_1 T.
\]
If \(q\ne0\), the \(\eta_3\) coefficient in its clock equation is
\(q b_2+(y_{11}-y)b_3=0\); since \(b_2\ne0\), this also proves
\(y_{11}\ne y\).

## Off-state compression and the third-tap exclusion

Suppose there are \(N=4\) or \(5\) distinct off clocks. The exact
rank \(\dim F_4=3\) and independent Vandermonde columns
\(d,Cd,C^2d\) give \(F_4=dP_{\le2}(C)\). From \(d\odot d\in F_4\)
there is a quadratic polynomial \(G\) with \(d_i=G(c_i)\ne0\)
on off rows. Thus each element of \(E_4\) is constant at identical
states \((c_i,\mathrm{off/clean})\). This argument does not merge rows.

The pure moment tests \(\beta C^k d=0\) for \(0\le k\le6\)
cancel all \(\beta\) off aggregates. Likewise \(\rho C^k d=0\)
for \(0\le k\le4\) cancels every off aggregate of \(\rho\).
The remaining \(\beta\) scalar quadrature on clean nodes must have
at least \(M=5\) distinct clean labels, since the degree-four Gram
for \(\ell_m\) is nonsingular. Origin 0 is a clean label from the first row.
If there are exactly five, each has nonzero aggregate and their labels
cannot contain both 0 and 1: multiplying their degree-five node polynomial
by powers through degree three contradicts the nonsingular Gram
for \(X(1-X)^{m+1}\) after dividing out the two endpoint factors.

Now \(H_5\) contains the actual state-valued profile
\(P_{\le5}(c)+dP_{\le3}(c)\). If \(M\ge6\) its dimension is 10,
by testing a polynomial relation first on the clean clocks and
then on four distinct off clocks. Thus it equals \(H_5\).
If \(M=5\), the same calculation with polynomial degree four gives
dimension at least nine. The final node 1 must be off (the two-endpoint
argument), and has an earlier same-state copy because the final weight
is nonzero and its off aggregate is zero. So \(e_{12}\) is independent
of the state profile and \(H_5\) equals that profile plus \(K e_{12}\).
In either case \(Av\) agrees at same-state nonterminal coordinates.
Since \(Av\) first becomes nonzero at row 9, row 9 is a new state
and does not have the same state as row 8. If \(M\ge6\), this also
shows the final state is unique because \(e_{12}\) is state-valued;
it is then clean by off aggregate cancellation.

If \(q\ne0\), row 8 is clean by the Hadamard argument. Row 9 is then
off at the same clock. This state has no earlier occurrence and no
later occurrence: rows 10,11 and 12 all have different clocks
from row 9 in this branch. Thus both \(\beta_9\) and \(\rho_9\) are zero
by the aggregate identities, a contradiction.

Therefore \(q=0\). The identity \(2\rho_9=b_1 U\ne0\) forces row 9
to be clean: if off, it is the sole representative of its state through
row 10, the entire possible support of \(\rho\). Thus row 8 is off.
It has no earlier same-state copy because \(v_8\ne0\), while \(v\)
was zero earlier and \(E_4\) is state-valued. So \(\rho_8=0\)
as well. Also \(v_{10}=0\) from \((Y-y)v\in K e_{12}\).
For \(\sigma=\beta A^3\), the literal support restrictions now give
\[
 V=v_9\rho_9,\qquad U=v_8\sigma_8+v_9\sigma_9.
\]
If \(\sigma_8=0\), the two column read identities imply \(2V=aU\).
However \((m+4)V=(m+3)aU\), so this would force
\((m+2)aU=0\), impossible. In particular \(\sigma_8\ne0\).
The four zero moments \(\sigma C^k d=0\) for \(0\le k\le3\)
therefore require at least five off states with a nonzero \(\sigma\)
aggregate: otherwise the moment matrix on the active labels has full
column Vandermonde rank, while row 8 is the sole contributing site
of its state. Every such state occurs among the first eight rows because
\(\sigma\) ends by row 9 and row 9 is clean. This excludes \(N=4\);
at \(N=5\) it gives the claimed placement and \(q=0\) gives the
clock relation.

## Five off clocks, five or seven clean clocks

For \(M=5\), the clean aggregate weights of \(\rho\) are exactly
the clean aggregates of \(\beta Y^2/((m+1)(m+2))\): both rows pay
the same scalar moments through degree six, their off aggregates
vanish, and there are five clean labels to compare. All these clean
weights are nonzero because no clean label is 1 and all five original
aggregates are nonzero. Hence all five clean labels occur through
row 10. At least five of the first eight rows are off; consequently
rows 9 and 10 are new clean labels, and exactly three clean labels
occur through row 8.

For shift two, the clean node hull is \(X Q(X)/66\), where
\[
 Q(X)=66X^4-120X^3+72X^2-16X+1.
\]
Indeed any monic clean hull is \(X\) times a monic quartic whose four
moments against \(X(1-X)^2\) vanish. The paid nonsingular Gram gives
uniqueness; direct integration checks the four moments of \(Q\).
Both \(c_9,c_{10}\) are nonzero (the first eight contain the origin),
so \(Q(c_9)=Q(c_{10})=0\). Put \(z=1-c_9\). The resonance gives
\(1-c_{10}=2z/3\). Set \(g(z)=Q(1-z)\) and \(h(z)=27g(2z/3)\);
the latter is the integer polynomial
\(352 z^4-1152 z^3+1296 z^2-576 z+81\).
The certified identity
\[
\begin{split}
&(7243765760z^3-19604901120z^2+15591140352z-3132850032)g(z)\\
+&(-1358206080z^3+2194239600z^2-984229056z+116843869)h(z)
=65803293
\end{split}
\]
rules out the pair in the stated characteristic. The paid field
already inverts 3 and 66; the added nonzero constant excludes an
additional characteristic dividing \(65803293=27\cdot2437159\).

For \(M=7\), the ten-dimensional \(H_5\) state-valued chart applies.
The row \(h_2=(m+1)(m+2)\rho-\beta Y^2\) has zero off aggregates and
zero ordinary clock moments through degree six, so each aggregate on
the seven clean labels is zero as well. But \(M+N=12\) leaves no repeated
state, so \(h_2=0\), contrary to its live coefficient at row 11.
For \(M=6\), the same argument gives zero aggregates at every state
and the single repeated state must have its second physical site at
row 11, because \(h_{2,11}\ne0\), the final state is unique, and
\(M+N=11\). This leaves clean, distinct states at rows 9 and 10, but
their six-node quadrature no longer determines a fixed quartic.
It is not excluded here.

## Lean scope

The companion Lean file imports only Lean core. It checks actual
coordinatewise multiplication in the late span, the paired zero-read
test, the resonant half-read and the nonzero third tap. It separately
checks the four rational Radau moments and the exact identity for all
fields with a nonzero Bézout constant. The rank flag, finite off-state
interpolation, actual weighted rooted paid bridge and final branch
assembly are documented above, not asserted to be fully formalized.
