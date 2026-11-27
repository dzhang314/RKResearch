# A four-word exception and a necessary physical tail at weighted order nine

Let an actual row \(\beta\) of a strictly explicit tableau represent
\(\ell_m(P)=\frac1{m!}\int_0^1(1-X)^m P(X)\,dX\) on rooted stage
profiles of tree size at most 9. Work over any field where \((m+9)!\ne0\);
this is formal polynomial integration. Number physical stages from 1.

**Necessary condition.** If the last nonzero output is at stage 12,
then
\[
 (m+1)\beta A=\beta(I-C),\quad c_{12}=1,\quad c_8=c_9\ne1,\quad
 c_{10}\ne c_9,\quad c_{11}\ne1 .
\]
Every adjacent coefficient \(a_{9,8},a_{10,9},a_{11,10},a_{12,11}\)
is nonzero. There is a degree-four rooted vector \(v\) vanishing on
the first seven stages with \(\beta A^4v\ne0\) and
\((Y-(1-c_8)I)v\in K e_{12}\), where \(Y=I-C\).
The equation for the actual output is an equality of *full rows* of
this truncated tableau. These are necessary conditions, not the
nonexistence of a twelve-row tableau or an improvement to the
unconditional order-eleven endpoints.

## The missing four-word lemma

For a rooted \(v\) whose available word budget is 4 and whose support
lies on the final five sites, use local indices \(0,\ldots,4\),
\(y_i=1-c_i\) on them, and \(\mu_j=\beta A^jv\). The exact word
response for a word \(w\) of length \(d\le4\) in \(A,Y\) is
\[
 \beta w v=\mu_d\prod_{\text{letters }Y\text{ at position }j}(m+j).
\]
Here the leftmost letter is position 1. This follows by moving the
letters across the formal \(\ell_m\): integration increases the shift,
and multiplication by \(1-X\) both increases the shift and contributes
its new index. Terminal augmentation by \(e_s\) at clock 1 does not
change any positive word. Normalize nothing in the no-top case.

**No top tap.** Put \(u=A^2v,\ \rho=\beta A^2,\ U=\mu_3\).
Their support bounds give \(\mu_4=\rho_2 u_2\). If \(u_2=0\), then \(u\)
is supported on sites 3,4 and \(Au\) at 4. The paid four-letter reads
\(\beta YAu=y_4 U\) and \(\beta AYu=y_3 U\) both vanish.
Nonzero \(U\) would force \(y_3=y_4=0\), contrary to the paid
\(\beta Yu=(m+1)U\). If \(\rho_2=0\), then \(\rho\) is supported on
sites 0,1. Now \(\rho AYv=y_0 U\) and \(\rho YAv=y_1 U\) both vanish;
\(\rho Yv=(m+3)U\) gives the analogous contradiction. Thus
\(\mu_4=0\) implies \(\mu_3=0\) at either terminal clock.

**Top visible.** Set \(T=\mu_4\ne0,\ U=\mu_3,\ V=\mu_2\).
The sole four-edge physical path is nonzero, so \(v,Av,\dots,A^4v\)
form a full echelon basis of the suffix. Write \(\eta_i=A^iv\).
In this basis, for \(0\le i\le2\),
\(Y\eta_i=y_i\eta_i+z_i\eta_{i+1}+w_i\eta_{i+2}+\cdots\).
If \(y_i=y_{i+1}\), then \(z_i=0\): the operator is diagonal and
scalar on that physical two-coordinate subquotient. The one-clock
words at the two highest usable lengths say, for \(k=m+3-i\),
\[
 y_i U+z_i T=(k+1)T,\qquad
 y_i V+z_i U+w_i T=kU .
\]
For each \(i+2\le j\le4\), the two-clock word
\(\beta A^{4-j}Y A^{j-i-2}Y\eta_i\) gives
\[
 y_i\,pU+z_i\,pT+w_i\,y_j T=p(k+1)T,\qquad p=m+5-j.
\]
Indeed the first two terms are paid single-clock words, the third
sees only the diagonal \(y_j\) on its unique terminal path, and all
later terms are zero. Subtraction gives
\[
 y_j\big[y_i(U^2-TV)-UT\big]=0.                         \tag{1}
\]
If \(U\ne0\) and \(y_4\ne0\), (1) for \(i=0,1,2\) forces
\(y_0=y_1=y_2\). In particular \(z_0=z_1=0\), so the two highest
single-clock equations give \(y_0U=(m+4)T=(m+3)T\), impossible.
If \(U\ne0\), therefore \(y_4=0\). Also \(y_3\ne0\), since
\(y_3=y_4=0\) would give \(z_3=0\) and the last single-clock
equation \((m+1)T=0\). Application of (1) at \(j=3\) gives
\(y_0=y_1\ne0,\ y_0U=(m+4)T,\ y_2\ne y_1\) by the same adjacent
calculation.

In this exception \(z_0=0\). The two-clock equation at \(i=0,j=3\)
now forces \(w_0=0\) (subtract \(p\) times the high equation).
Writing \(h_0\) for the coefficient of \(\eta_3\) in \(Yv\), use
\(\beta A Y^2v=(m+2)(m+3)U\):
its expansion is \(y_0(m+2)V+h_0y_3T\); the low equation is
\(y_0 V=(m+3)U\). Hence \(h_0=0\) and \(Yv-y_0v\) is supported
only at the last physical site. Furthermore \(y_0\mu_1=(m+2)V\)
by \(\beta AYv=(m+2)V\).
The appearance of a repeated initial clock is essential; a general
budget-four penultimate-vanishing assertion is not proved.

## Why the nine-order extremum must use that exception

This is a mathematical deduction using existing paper lemmas, not a
claim of a native Lean rooted-order theorem. The estimates below refer
to [paid rank baseline (1)](../lower-bounds/paid-beta/01-PAID-GRADE-FIVE-SURPLUS.md)
and the [zero/one-spare cutoff proof](../lower-bounds/paid-beta/separated-pure/ZERO-OR-ONE-SPARE-DETECTOR-CUTOFF.md).


1. With \(r=9,g=4,L=4,s=12,k=7\), separation gives five polynomial
   dimensions and strict growth gives at least three pure ones. The
   reverse row flag \(R_3\) has dimension at least \(3+\epsilon\),
   \(\epsilon=[h_1\ne0]\), \(h_1=(m+1)\beta A-\beta Y\).
   If \(c_{12}=1\), the final coordinate is outside \(E_4\) by the
   paid endpoint Gram and is annihilated by the whole reverse flag.
   If \(c_{12}\ne1\), \(h_1\ne0\) from its terminal coordinate.
   Counting in 12 dimensions gives precisely the two cases
   \((\epsilon,[c_{12}=1])=(1,0),(0,1)\) and \(\dim E_4=8\).
   With the usual augmentation \(H_i\), \(\dim H_4=9-\epsilon\),
   and the spare parameter \(12-\dim H_4-(L-1+\epsilon)\) is zero.

2. Assume for contradiction that \(\mu_3\) vanishes on the late
   part of \(H_4\) (zero on stages \(1,\dots,7\)). Here is an index
   audit for the zero-spare proof at \(L=4\): the numerical lower bounds
   usually requiring \(L\ge5\) are replaced; the word budgets are not
   enlarged.
   * The reverse caps give \(\dim H_{4+j}\le \dim H_4+j\) for
     \(0\le j\le3\). For a diagonal clock-closure delay
     \(\delta\le2\), at most one nonendpoint charge remains on
     \(A^\delta v\); its known zero moment has exponent
     \(3-\delta\ge1\). In the descending induction at \(j<\delta\)
     there are at least \(3-j\) consecutive zero moments compared
     with \(\delta+1-j\le3-j\) distinct charges. The bare path bound
     has no minimum length. This is the *short clock closure*
     paragraph, not the separate five-cost localized-vector theorem.
   * For \(\delta\ge3\), flag equalities hold through grade 7. The
     terminal annihilator at grade 7 has dimension exactly
     \(\epsilon\in\{0,1\}\); hence the zero-spare branches are only
     the invariant terminal hyperplane, the single noninvariant
     detector, or the augmented detector. In the short-delay endpoint
     case the entire flag has been handled in the preceding bullet.
     A nonzero late read in a single clock component would contradict
     the assumed zero penultimate read, except at clock 1 where its
     positive reads vanish in any event. The consecutive vanishing
     detector moments therefore require **five** distinct sites for
     the full-tail noninvariant chart (stages 8 through 12), or
     **four** before the last stage (8 through 11) for the other
     two charts. In the endpoint chart \(h_2\) is a valid secondary
     detector since the genuine tap \(\beta A\) has size 8 and last
     position at least 10.
   * The [Newton calculation](../lower-bounds/paid-beta/06-ODD-EXPLICIT-STAGE-BOUND.md)
     uses detector index \(J=4\) in the full-tail chart and \(J=3\)
     otherwise. In the two one-detector charts the missing-shift test
     uses words of cost \(n+1\le J\) when the initial nonzero run
     has length \(n<J\). A trailing run shortens a genuine tap's
     support to at most \(k+1=8\), while the old paid baseline gives
     at least **10** for size 8 and **9** for size 7, at each
     applicable shift. With all shifts nonzero, the penultimate
     of the chosen detector output is the *same* original
     \(\beta A^3v\), including when that output is \(\beta A\).
     The single-clock word fixes every shift; the commutator is
     tested only for \(0\le j\le J-2\), leaving \(J-1\) consecutive
     vanishing reads on \(J\) distinct clocks. Reweighting preserves
     size 8 or 7 respectively and again cannot end by 8. In the
     remaining invariant hyperplane case \(J=3\): the terminal word
     from \(v_J\) costs 1, and an earlier missing-shift word costs
     at most \(4-j\) from \(v_j\). The two-distinct-endpoint
     contradiction and all its indices are unchanged. The
     [weighted version](../lower-bounds/paid-beta/07-WEIGHTED-DETECTOR-STAGE-BOUND.md)
     supplies the shift-dependent constants. No fifth-degree surplus,
     five-row path theorem, or ordinary size-nine stage count is
     imported here.

3. Consequently all four positive taps would factor on \(E_4\)
   through the first seven coordinates. For any rooted combination
   zero there, the model \(P=XQ,\ \deg Q\le3\) would satisfy
   \(\ell_{m+1}(P)=\cdots=\ell_{m+4}(P)=0\).
   The degree-three Gram with weight \(X(1-X)^{m+1}\) is nonsingular
   by the paid factorial determinant; its bound is \(m+9\).
   Hence the literal seven-row prefix would separate all degree-four
   models. It has at least \(5+3=8\) dimensions by strict pure growth
   on this separated prefix. This contradiction is independent of
   any dense-width theorem whose threshold is size six.

4. There is therefore a late vector with \(\mu_3\ne0\). A terminal
   augmentation changes none of its positive taps and is late, so
   take it in \(E_4\). The four-word lemma forces the nonzero top
   tap, hence the four physical edges, the final endpoint and the
   displayed clocks. The rank dichotomy gives \(h_1=0\).
   In particular the shift-two problem of a 12-row row exact for
   \((1-X)^2/2\) has the full-row identity \(3\beta A=\beta Y\).
   When the row actually is \(bA^2\) this reads \(3bA^3=bA^2Y\)
   on its physical prefix. Neither constraint by itself raises the unconditional
   stage floor.

## The budget-four obstruction is sharp as a local statement

Here is an exact physical five-site example at shift \(m=2\) where both
\(\mu_3=\mu_4=1\) survive. Use \(v=e_0\),
\(Y=\operatorname{diag}(6,6,1,2,0)\),
\(\beta=(5/18,29/120,-6,3/2,1)\) and
\[
 A=\begin{pmatrix}
 0&0&0&0&0\\1&0&0&0&0\\1/5&1&0&0&0\\
 3/4&14/5&1&0&0\\7/18&137/60&-7/2&1&0
 \end{pmatrix}.
\]
The moments from powers zero through four are
\((5/18,5/9,5/6,1,1)\). The companion Lean theorem checks all 31 words
of lengths zero through four against this physical \(A,Y,\beta,v\).
The diagonal can literally be made \(I-\operatorname{diag}(A\mathbf1)\)
by prepending an origin stage and feeding its outgoing column to the
five rows with coefficients \((-5,-6,-6/5,-111/20,149/180)\);
all words on the embedded \(v\) are unchanged. This is **not** a
weighted order-nine tableau, nor is \(v\) claimed to have a rooted
grade-four lift. It proves that local four-word equations, even with
a diagonal physical clock and strict chronology, cannot eliminate
the remaining pattern. A new constraint must use more information
than those equations on this one vector.

## What Lean checks and does not check

The companion source imports only Lean core. Over an arbitrary
`Lean.Grind.Field`, `FourTap.noTop` proves the unreduced physical
two-sided argument from the two definitions of \(\mu_3\) and six word
equalities. `FourTap.nonendpointKrylov` and
`FourTap.exceptionalKrylov` quantify over all 15 entries of the clock
matrix in the top-visible cyclic basis and consume its actual word
evaluations (length at most four), with the adjacent-equal-diagonal
rule. They prove vanishing and the exceptional normal form above.
They do not yet formalize construction of that cyclic basis from a
native RK tableau, the paid-word bridge, or the grade-four cutoff
application. The claimed twelve-stage condition depends on the
documented mathematical argument in addition to the checked local
lemma. No arbitrary-ring sign or universal stage improvement is implied.
