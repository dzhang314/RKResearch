# DIRK12/15: the actual early return on the nine-site invisible grid

Work in real ordinary DIRK order twelve, fifteen physical stages, \(C(2)\), \(f_5=3\), and invisible weighted forward cubic, with four distinct truly cubic-dirty ghosts and exactly nine distinct **nonterminal live** numerical labels. In the [high-site quotient](../dirk12-fifteen-rank3-invisible-four-ghost-variable-grid/README.md), work in physical reverse order, \(N=A^{\mathsf T}\) and \(Y=\operatorname{diag}(\mathbf y)\), \(\mathbf y=\mathbf1-\mathbf c\). The genuine cubic \(\mathbf G\) is centered on the unique live pair at the first nonzero reflected label \(d\). The genuine head \(\mathbf H=N\mathbf G-\frac d2\mathbf G\) has nonzero aggregate at all nine labels. In particular it is zero at the first \(d\)-row and **nonzero at the second**. The flags \(\mathcal B_4=\langle\mathbf G,\mathbf H\rangle\), \(\mathcal B_5=\langle\mathbf G,\mathbf H,Y\mathbf H\rangle\) are exact; ghosts and the literal terminal are zero in both, but no other singleton is assumed clean.

The following deductions constrain a real equality branch; they do not change the global interval **15–16**:

1. A zero-total-mass pair at \(d\) cannot have completed before the third distinct nonzero reverse live clock. No extra nonterminal live row at the reflected label zero can occur before that third debut, regardless of mass.
2. In a remaining early return, let \(v,u\) be the second and third distinct nonzero reverse live clocks. In the normalized variables \(r=v/d,t=u/d\),
   \[
                       (r^2-4r+1)t+r(r+1)=0 .
   \]
   The actual reverse diagonal at \(u\) is zero, including the exceptional quadratic \(r^2-3r+1=0\).

These are literal row deductions with only genuine grades three to five used in the early-return proof. A separate [mixed grade-six note](mixed-grade-six.md) uses the next true grade and narrows the explicit-diagonal branch further.

## Literal exclusion of a uniform early pair

Normalize a row tap to a given numerical label by summing the contributing actual coefficients of \(N\) times their nonzero source weights, divided by the current **live** row weight. The exact first two nonconstant weighted moments are at scalar inputs \(X\) and \(X^2\) when the true cubic error there is specified, and no division is made at an unweighted ghost.

Before the first nonzero label other than \(d\), the first two leading scalar moments imply that every observed \(d\)-row has normalized cubic amplitude \(\sigma_0=d^3/6\). Its aggregate tap to \(d\) is \(d/2\). Thus its normalized head is zero, ruling out the second \(d\)-row before the first \(v\)-row. Suppose the pair has zero mass and the second \(d\)-row is after \(v\) but before the first \(u\). Centering and opposite live weights give identical normalized cubic \(\sigma_0\) on the two \(d\)-rows. At the second \(d\)-row the actual nonzero scalar input labels are among \(\{d,v\}\). Its aggregate taps \(T_d,T_v\) satisfy
\[
 dT_d+vT_v=d^2/2,\qquad d^2T_d+v^2T_v=d^3/3+\sigma_0=d^3/2.
\]
Therefore \(T_v=0,\ T_d=d/2\), and \(N\mathbf G\) normalized at that row is just \(T_d\sigma_0\). This forces \(H=0\), contradiction. This is stronger than the earlier necessary resonance \(v=2d\): it excludes even that resonance when the mass is zero.

The same equations at a proposed **nonterminal live zero-clock row** before the third distinct nonzero label have right sides zero, so all earlier aggregate taps to \(d,v\) vanish (or just \(d\) if \(v\) has not appeared). If the second \(d\)-row has not yet occurred, this forces \(N\mathbf G=0\) and hence \(H=0\) at this singleton, contradiction. If there has already been an early return, it has nonzero mass by the preceding argument. Its two normalized \(\mathbf G\) amplitudes are therefore different. The actual cubic-input scalar error identity on the first two live nonzero labels is
\[
  \mathbf E_4=\frac{3d}{2}\mathbf G+\lambda\mathbf H,\qquad
             \lambda=3(v-d)(v-2d)/d^2.
\]
At the return, in terms of its normalized change \(\Delta=G_i/b_i-d^3/6\), the same-clock relation is \(\lambda H_i/b_i=(v-d/2)\Delta\). Both \(\Delta,H_i\) are nonzero; in particular \(v\ne2d\), so \(\lambda\ne0\). At the proposed zero live row, the vanishing aggregate taps make the scalar cubic-input discrepancy zero, since its actual source labels are all in \(0,d,v\). That discrepancy is also \(\lambda H_i\), since its own \(\mathbf G\) is zero. This is impossible. Ghosts contribute nothing in these weighted scalar or low pure reads.

It follows that in an early-return chart the first nonterminal live physical rows through the third nonzero debut are literally \(d_1,v,d_2,u\). The literal terminal is the only live input at numerical zero in this prefix; intervening zero-weight ghosts do not contribute. The two nonzero weights of \(d_1,d_2\) are signed and no positivity of their sum is assumed.

## Exact low reverse ratios from the first three live rows

For the rest of this note use normalized reverse clock \(y/d\) and normalized matrix \(N/d\); \(d\ne0\). Rescaling the genuine polynomial primitives gives the same formal primitive \(J\) in the normalized variable. Write \(1,r,1,t\) for the four nonterminal early rows, \(\sigma=1/6\), and \(h_x=H_i/b_i\) in this normalized system. The change at the second \(1\)-row is denoted by \(\delta=G_{i_2}/b_{i_2}-\sigma\ne0\). Set
\[
  \lambda=3(r-1)(r-2),\quad
  k=(r-\tfrac12)/\lambda,\quad
  h_r=r^3/[36(r-1)] .
\]
The necessary guards are \(r\ne0,1,2,1/2\). The first two follow from distinct nonzero clocks; \(r=2\) and \(r=1/2\) are each ruled out by the same-clock relation \(\lambda h_1=(r-\tfrac12)\delta\) at the second \(1\)-row and its nonzero \(h_1,\delta\). The physical quantities in the next equations depend on the actual normalized \(N\), without deweighting any ghost slot.

Let \(\varphi,\psi\) be the two affine scalar polynomials in the exact identities
\[
 \mathbf E_5=\tfrac95\mathbf G+\varphi(Y)\mathbf H,\qquad
 N\mathbf H=\psi(Y)\mathbf H.
\]
For \(\mathbf E_5=N\mathbf W(X^4)-\mathbf W(X^5)/5\), the \(\mathbf G\) coefficient follows at the first \(1\)-row with diagonal \(1/2\) and \(H=0\). In \(N\mathbf H\) the \(\mathbf G\) coefficient is zero by the same actual first row, because every preceding \(\mathbf H\) entry is zero. Both identities lie in genuine grade five.

At the first \(r\)-row, the normalized tap to \(1\) is \(r^3/(6(r-1))\) by its exact \(X,X^2\) reads, and its scalar diagonal \(a_r=r(2r-3)/(6(r-1))\). Thus \(h_r\) is the displayed weighted head from the tap to the first \(1\)-row. This read gives
\[
 \psi(r)=a_r,\qquad
 \varphi(r)=\frac{r^3/[6(r-1)]+a_r r^4-r^5/5}{h_r}.
\]
At \(1_2\), the scalar aggregate taps are \(T_1=1/2-\delta/(r-1)\), \(T_r=\delta/[r(r-1)]\); \(h_1=k\delta\). Its literal diagonal follows from \(N\mathbf G\) and the fact that only the current \(1_2\) source has the changed amplitude:
\[
 a_2=\tfrac12+\frac1{6(r-1)}+k .
\]
There is no additional earlier nonterminal live zero by the chronology proof. Computing the exact quartic-input read on \(0,1,r\) and subtracting \(\frac95\mathbf G\), and computing \(N\mathbf H\) with only \(H_r,H_{1_2}\) as sources, gives
\[
   \varphi(1)=\frac{r^2+r-4/5}{k},\qquad
   \psi(1)=a_2+\frac{h_r}{r(r-1)k}.
\]
The literal early rows thus fix both affine polynomials independent of the individual signed pair weights.

## Exact third ratio, including the zero leading pivot

At the next actual live row \(t\), let \(h=H_i/b_i\ne0\). Its genuine leading, cubic and quartic scalar reads determine the three aggregate taps \(T_1,T_r,T_t\) to nonzero scalar labels through cubic precision:
\[
\begin{aligned}
 T_1&=\frac{t^3(2r-t)/12+\lambda h}{(1-r)(1-t)},&
 T_r&=\frac{t^3(2-t)/12+\lambda h}{r(r-1)(r-t)},\\
 T_t&=\frac{t^2(3t^2-4(1+r)t+6r)/12+\lambda h}{t(t-1)(t-r)} .
\end{aligned}
\]
These are the true cubic Lagrange integrals plus the scalar cubic defect times the leading cardinal coefficients. The quartic nodal polynomial \(X(X-1)(X-r)(X-t)\) has zero actual numerical action there. Its scalar primitive gives the equation \(A h+B=0\), where
\[
  A=\varphi(t)-(1+r+t)\lambda,\qquad
  B=-t^3(3t^2-5(1+r)t+10r)/60 .
\]
Meanwhile \(N\mathbf G\) at \(t\) has value \(h\) and identifies the contribution \(\delta T_{1_2}=h-\sigma T_1\). Therefore the genuine \(N\mathbf H\) relation is
\[
                  (k+T_t-\psi(t))h+h_rT_r-k\sigma T_1=0.
\]
Write its left hand side as \(q_2h^2+q_1h+q_0\). The exact rational identity is
\[
q_2 B^2-q_1 A B+q_0 A^2=
 -\frac{3t^3(r-1)(r-t)(t-1)}
         {100(r-2)(2r-1)^2}
       \bigl[(r^2-4r+1)t+r(r+1)\bigr]^2 .
\]
Every denominator and displayed prefactor is nonzero by the literal clock guards. The left side is zero for any common root \(h\), even \(A=0\): use \(B=-Ah\) and multiply the quadratic equation by \(A^2\). Thus the claimed ratio polynomial vanishes.

Put \(D=r^2-4r+1\) and \(P=r^2-3r+1\). Since \(r,t\ne0\), the ratio implies \(D\ne0,\ r+1\ne0\), and \(t=-r(r+1)/D\). At this value
\[
 A=\frac{9r(r-1)(r+1)P}{5(2r-1)D}.
\]
If \(P\ne0\), substitution gives the unique value
\[
 h_*=-\frac{r^3(r+1)^2(2r-1)(5r^2-14r+5)}
                  {36(r-1)D^4},\qquad T_t=0.
\]
Here \(h_*\ne0\) is required by the real barycentric head, so \(5r^2-14r+5\ne0\). The tap \(T_t\) is the literal diagonal since no earlier nonzero live row is at \(t\).

If \(P=0\), then \(t=r+1\) and \(A=B=0\); no division by \(A\) is justified. In the exact quadratic coefficient quotient, the remaining genuine equation is
\[
        q_2\bigl(h-(5-15r)/36\bigr)^2=0.
\]
Here \(q_2=\lambda/[t(t-1)(t-r)]\ne0\), hence \(h=(5-15r)/36=h_*\), and substituting in the literal receiver tap again gives \(T_t=0\). Thus the exceptional leading pivot does not create an implicit diagonal or a second amplitude branch. The exact replay checks both quadratic coefficients separately. No weighted row is discarded and no unspecified geometrical order on numerical clocks is used.

## Verification

The [symbolic exact replay](verify.py) reconstructs the rational identities from Lagrange scalar formulas and the true affine heads, with an explicit common-root rather than a leading-pivot division. The native scalar module checks the two zero/uniform moment gates and the guarded third-ratio resultant in Lean/Mathlib 4.36 with only standard axioms, as shown by the typed import replay. The full literal proof is analytic. The subsequent grade-six crossing and its limits are in the companion note.

    python3 -B verify.py
    lake build RKCert.ReviewedNative.DIRKOrderTwelveFifteenNineSiteEarlyReturn
    lake env lean AuditDIRKOrderTwelveFifteenNineSiteEarlyReturn.lean
