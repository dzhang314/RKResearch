# Shift-one weighted size nine requires thirteen physical positions

Let \(A\) be strictly lower triangular over any characteristic-zero field
\(K\). If an actual row \(\beta\) is exact on rooted numerical stage
vectors through tree size nine for
\[
                \ell_1(P)=\int_0^1(1-X)P(X)\,dX,
\]
then its last nonzero physical position is at least 13. All integration is
formal polynomial integration. There is no ordering or sign hypothesis.
This is a mathematical theorem with separately checked Lean-core scalar
exits, **not** a native Lean proof of the weighted rooted bridge or a new
ordinary order-eleven stage bound.

## Shift-independent input and census

Use \(E_j\) for the actual numerical rooted span through degree \(j\)
(size \(j+1\)), \(F_j\) for actual columns with zero model, \(c=A\mathbf1\),
\(C=\operatorname{diag}c,\ Y=I-C,\ d=Ac-c^2/2\), and \(J\) for the lower
polynomial primitive. An actual application of \(A\) uses one grade and
acts on the formal polynomial by \(J\); coordinatewise multiplication
adds grades and multiplies models. A tagged state is a clock with
the clean/off tag \(d_i=0\) or \(d_i\ne0\). Let \(N,M\) count distinct
off and clean labels; a physical clock may occur with both tags.

Strict truncation at the last nonzero output preserves every rooted test.
The [old paid floor](../lower-bounds/paid-beta/01-PAID-GRADE-FIVE-SURPLUS.md),
inequality (1), already requires twelve positions. Suppose twelve, with
\(\beta_{12}\ne0\). Apply [FourTap](WEIGHTED-ORDER-NINE-FOUR-TAP.md)
and the arbitrary paid shift sections of [Off Gates](WEIGHTED-ORDER-NINE-OFF-GATES.md)
with \(m=1\); these require only \(10!\ne0\). They give:
* Separation through \(E_4\), \(\dim E_4=8,\ \dim F_3=2,\ \dim F_4=3\).
* \(c_{12}=1,\ 2\beta A=\beta Y,\ c_8=c_9=\theta\ne1,\ c_{10}\ne\theta,\
  c_{11}\ne1\); all consecutive edges in 8–12 are live.
* A genuine \(v\in E_4\), zero through row 7, supported only at clocks
  \(\theta,1\), with \(v_8,(Av)_9,\beta A^3v,\beta A^4v\ne0\).
  The first-seven evaluations on \(E_4\) are independent.
* \(H_j=E_j+K e_{12}\) has ranks \(9,10,11\) at \(j=4,5,6\).
  Write \(\rho=\beta A^2\). Then
  \[
      h_2=3\beta YA-\beta Y^2=6\rho-\beta Y^2,\quad
      H_6=\ker h_2,\quad h_{2,11}=-\beta_{11}(1-c_{11})^2\ne0.
  \]
* At \(N=5\), stage 8 is off and stage 9 clean at their common
  clock \(\theta\); all five off states occur through row 8,
  \(\rho_9\ne0\), and \(5(1-c_{10})=3(1-\theta)\).
  This is the arbitrary shift resonance \((m+4)y_{10}=(m+2)y_9\)
  specialized to the new shift. The \(N=4\) and \(N=5,M=7\)
  contradictions in Off Gates are shift-free.

The [small-off census](WEIGHTED-ORDER-NINE-OFF-CENSUS-SUPPLEMENT.md)
excludes \(N=0,2,3,7\) for any paid shift. Briefly: \(N=0\) is
impossible at the first nonzero clock, which exists by
\(\beta c=1/6\); \(N=2\) makes \(F_3\) a forbidden invariant
rank-two span; \(N=3\) gives at most two clean clocks by the
first-clean contrast \((X^2(X-u)^2)'\), while clean quadrature
needs at least five; \(N=7\) leaves exactly five clean states
and no repeats, so an endpoint terminal is impossible whether
tagged clean (two-endpoint Gram) or off (zero off aggregate).
The \(N=4\) argument uses the nonzero third off tap and four
pure moments, requiring at least five off states.

For \(N\ge3\), \(F_4=dP_{\le2}(C)\); \(d^2\in F_4\) fixes a
nonzero head \(G\) of degree at most two with \(d_i=G(c_i)\ne0\)
on off sites. An \(E_4\) column has the state form \(P(c)+dQ(c)\).
At the first physical nonzero clean clock \(u\), the masked
\(C(G(c)-d)\) is zero on every predecessor, and its grade-four
primitive is exact on this clean row. Thus \(J(XG)(u)=0\).
This excludes constant \(G\); if \(G(0)=0\), testing \(G(c)-d\)
also gives \(JG(u)=0\), incompatible with nonzero degree at
most two. Consequently \(G(0)\ne0\) and \(\deg G=1\) or 2
in every remaining multiple-off branch (all have a nonzero
clean row). Linear monic \(G\) has root \(2u/3\); quadratic
monic \(G=X^2+gX+h\) satisfies \(6h+4ug+3u^2=0\).

For \(N\le7\), seven tests \(\beta C^j d=0\) cancel every off
aggregate. The remaining degree-eight clean quadrature needs
at least five labels. For \(N\le5\), five tests \(\rho C^j d=0\)
also cancel all its off aggregates. Thus at \(N=5,6\) only
\(M=5,6\) remain, and at \(N\ge8\) one has \(M\le4\).
The one-off case uses its own forward normal form.

## New exact scalar data

Put
\[
 \begin{split}
 R_4&=42X^4-84X^3+56X^2-14X+1,\quad R_5=XR_4,\quad R_5(1)=1,\\
 L_3&=42X^3-56X^2+21X-2,\quad D_3=12X^3-18X^2+8X-1.
 \end{split}
\]
By the formal beta moments
\(\int_0^1 X^{a+k}(1-X)^b\,dX=(a+k)!b!/(a+b+k+1)!\)
these polynomials have their first four, three, three moments
zero for \(X(1-X),\ X(1-X)^2,\ X^2(1-X)^2\), respectively.
The corresponding paid degree-three or degree-two Gram gives
uniqueness up to scale. \(R_4(1-X)=R_4(X)\).
In particular no orthogonal polynomial from shift two is reused.

A five-label clean quadrature includes 0, cannot contain both 0
and 1 (divide its degree-five hull by \(X(X-1)\), then apply
the weighted degree-three Gram), and has all aggregates nonzero.
Its monic hull is therefore \(B=XR_4/42\) by the four anchored
moments. A grade-five alias \((0,P)\) has \(P(0)=0\) by the
origin and its four tests \(\ell_1(X^kP)=0\), \(0\le k\le3\).
So every alias polynomial lies in \(K R_5\), irrespective of
whether there is an actual nonzero alias.

Write
\[
 \mathcal M_i(S)=\int_0^1 X^{i+1}(1-X)^2S(X)\,dX,\quad 0\le i\le2,
 \qquad
 \Delta(P;a,z)=(JP)(a)R_5(z)-(JP)(z)R_5(a).
\]
On quartic coefficients of degrees 0 through 4, the successive
moments scaled by \(840,2520,5040\) are rows
\((70,28,14,8,5),(84,42,24,15,10),(84,48,30,20,14)\).
The integer constants and scalar interfaces below occur in
[ShiftOneGate.lean](ShiftOneGate.lean). The arithmetic is valid
over arbitrary fields satisfying its explicit nonvanishing
guards. The entire rooted proof is asserted here only in
characteristic zero, matching the one-off forward source.

## Multiple-off cases other than five/six

**Five off, five clean.** The \(\rho\) clean aggregates match those
of \(\beta Y^2/6\) by exact moments through degree six, so all five
are nonzero and occur by physical 10. Since at least five of the
first eight sites are off, stages 9 and 10 are new nonzero clean
labels. Write \(s=1-\theta,t=1-c_{10}\); then \(5t=3s\) and
\(R_4(1-s)=R_4(1-t)=0\). Reflection gives \(R_4(s)=0\) and
\(625R_4(t)=3402s^4-11340s^3+12600s^2-5250s+625=0\).
Their explicit Bézout combination is 503606
(*reflectedRadauImpossible*).

**Six off, five clean.** The first nonzero clean \(u\) is a root
of \(R_4\). If \(G\mid B\), then \(G\mid R_4\) since \(G(0)\ne0\).
For a linear head the roots \(u,2u/3\) of \(R_4\) are excluded
by *directRadauImpossible*, whose integer constant is 9287.
For a quadratic head use *anchoredImpossible*: \(R_4(u)=0\),
the chronological \(6h+4ug+3u^2=0\) and the two coefficients
of \(R_4\bmod(X^2+gX+h)\) cannot all vanish. The coefficients are
\[
  -42g^3-84g^2+84gh-56g+84h-14,\quad
  -42g^2h-84gh+42h^2-56h+1,
\]
and the certificate integer is \(D_{\rm anchor}=498044911357686\).
This does not require a split head.

Thus \(G\nmid B\). The state-valued space \(S_{\rm state}\) has
dimension eleven and \(E_6\cap S_{\rm state}\) contains the
rank-ten \(P_{\le4}(c)+dP_{\le4}(c)\), by independent interpolation
at the five clean/six off labels. If that intersection had
rank ten, representing \(B(c),CB(c)\) in it forces their
polynomial parts to vanish on the five clean labels and gives
\(B-GT=aD,\ XB-GU=bD\), with \(D\) the monic six-off hull,
\(\deg T,\deg U\le4,\ a\ne0\). Coprimality with \(D\) gives
\(G\mid(aX-b)\); but then \(\deg(B-GT)\le5\), contradicting
degree six. So \(H_6=S_{\rm state}\). Its literal \(e_{12}\)
forces the terminal state unique, whereas it is off at clock 1
with live weight and zero off aggregate. It needs a different
off row at 1, contradiction. The rank/terminal reasoning is
independent of shift; see [Six/Five](WEIGHTED-ORDER-NINE-SIX-OFF-FIVE-CLEAN.md).

**At least eight off.** The off polynomial of \(v\) has degree
at most four and vanishes at at least six labels outside its
two clocks \(\{\theta,1\}\). Hence it is identically zero,
stage 8 clean, \(\theta\ne0,\ G(\theta)\ne0\).
Let \(B_*\) be the hull of the \(M_*\) clean labels where \(G\ne0\).
It contains 0 and \(\theta\). Since \(G(c)B_*(c)=dB_*(c)\),
\(\ell_1(GB_*X^k)=0\) through \(k=6-M_*\).
The anchored \(X(1-X)\) Gram excludes \(M_*=2\), and \(M_*=3\)
with \(G\) linear. With \(M_*=3,\deg G=2\), \(GB_*/X\) is
proportional to \(R_4\); \(G\mid R_4\) and \(R_4(u)=0\) for
every nonzero clean clock, so use the new \(D_{\rm anchor}\).

With \(M_*=4\), there are eight off/four clean distinct states.
The rank-ten \(P_{\le5}(c)+dP_{\le3}(c)\) equals \(H_5\) by
interpolation first on off, then on clean. Its literal
\(e_{12}\) forces the endpoint clean. All eight off weights
are nonzero (otherwise seven off tests cancel them and the
four clean labels cannot pay the degree-eight Gram).
Rows 9–11 are all off: row 9 is off at \(\theta\) by stage 8's
unique clean state, with \(d_9(Av)_9\beta_9\ne0\).
The two actual pure reads \(\beta(d\odot Av)=
\beta C(d\odot Av)=0\) would kill that charge if there were
fewer than three off sites in 9–11. Thus the four clean labels
are \(0,u,z,1\), with \(z=\theta\), and the \(v\)-model is
\(P=X(X-u)G\) after scaling. This is the forward portion of
[the high-off proof](WEIGHTED-ORDER-NINE-HIGH-OFF.md), with no
shift-two arithmetic imported. The three new tests are
\(\mathcal M_i((X-u)(X-z)G)=0\). For linear \(G\) the cubic must
be proportional to \(L_3\) and have roots \(u,2u/3\), excluded
by *directLobattoImpossible* (integer constant 233).

For quadratic \(G\), \(P(1)\ne0\) and \((C-\theta)v\) supplies
\(e_{12}\in E_5\), so \(E_5\) has dimension ten. The paid dense
size-six width eleven mandates a nonzero alias, whose line is
\(K R_5\). The actual pair space has dimension eleven and
its pure space dimension five. The four independent
\(dP_{\le3}\) directions plus \(R_5(c)\), detected at clean 1,
exhaust it. Since \(Av\) is zero at \(u,z\), its clean
polynomial part gives \(\Delta(P;u,z)=0\); no \(R_5\) value
is divided out. The three moments just given, quadratic
chronology \(6h+4ug+3u^2=0\), and this minor use the
*pencilImpossible* certificate. The minor is multiplied by
60 and divided only by \(u z(u-z)\), and the normalized
coefficients combine to the nonzero integer *pencilDen*.

**Six off, six clean.** All states are unique, every off
weight zero, and the terminal is clean. The rank-ten \(H_5\)
state chart expresses \(e_{12}\); its off polynomial of
degree at most five must vanish at six labels and hence
identically. Its clean polynomial of degree five is divisible
by \(G\), so \(\deg G=2\). The off polynomial of \(v\) is zero
at at least five other off labels and hence identically.
Thus row 8 is clean, row 9 off, and the first nonzero clean
\(a\) occurs before row 8. The clean model of \(v\) has four
distinct roots at the clean labels excluding \(\theta,1\);
it is divisible by \(G\), and \(G(0)\ne0\). Write
\(P=X(X-t)G\) after scaling. Here \(t\) is the nonzero root
other than the two head roots; \(P(1)\ne0\).
This is the literal placement in [Six/Six](WEIGHTED-ORDER-NINE-SIX-OFF-SIX-CLEAN.md).
The new tests are \(\mathcal M_i((X-t)(X-\theta)G)=0\) and,
by the same rank-ten argument and vanishing through 8,
\(\Delta(P;a,\theta)=0\). If \(a=t\) use *pencilImpossible*.
Otherwise \(a\) is a head root, and \(J(XG)(a)=0\) forces the
other root \(a/2\) by \(12J(X(X-a)(X-b))(a)=a^3(2b-a)\).
The gate *headRootImpossible* uses
\(G_*=(X-a)(2X-a)\), scaled moments \(420,2520,2520\) on
\((X-t)(X-\theta)G_*\), and the minor for \(60J(X(X-t)G_*)\)
divided only by \(a\theta(a-\theta)\), all nonzero by placement.
Its integer certificate is *headRootDen*.

## Five off, six clean: the changed reflected resonance

The aggregates of \(h_2=6\rho-\beta Y^2\) vanish on every state:
they vanish off by the seven and five pure tests, and clean
by its clock tests through degree six. Its live row-11 entry
therefore needs an earlier duplicate state at a donor \(j\).
There are eleven states, so this is the sole repeat and
\(H_6=S_{\rm state}\). The rank-ten state chart
\(P_{\le5}(c)+dP_{\le3}(c)=H_5\) contains \(e_{12}\), giving a
unique, clean terminal state at 1. Stage 9 is clean and 10
also clean (all off labels already occur by 8 and the sole
repeat is 11); write \(\theta,\xi\) for their clocks.
The first eight contain five off states and three clean
states \(0,u,w\). Incoming off charges at a clean row have
zero \(1,X\) moments since \(Ad,ACd\) vanish there.
The first nonzero \(u\) needs three prior off labels for
the \(X\) primitive. If the second \(w\) preceded the fourth
off label, its charges would be proportional to those of
\(u\) on the same three labels. The exact primitive
\((X^2(X-u)^2)'\) would give \(w^2(w-u)^2=0\), impossible.
Since row 8 is off, this puts \(w\) at actual row 7.

Write \(s=1-\theta,\ t=1-\xi,\ r=1-w\) and \(5t=3s\).
Let \(B\) be the literal leading block through row 10.
The row \(b\) gathers the \(\beta\) contribution of 11 to its donor,
dropping 12 only for positive-\(Y\) outputs. It is zero off.
Let \(\delta=A_{11,*}-A_{j,*}\) on the first ten columns.
It kills the prefix of \(H_5\) since \(A E_5\subset E_6\subset
S_{\rm state}\), and \(A e_{12}=0\); \(\delta_{10}=a_{11,10}\ne0\).
The genuine shift-one adjoint
\(r_k=(k+2)\beta Y^k A-\beta Y^{k+1}\) annihilates \(E_{7-k}\).
After gathering on those state-valued inputs and the terminal
direction, it equals \(L_k+(k+2)\beta_{11}(1-c_{11})^k\delta\),
where \(L_k=(k+2)bY^kB-bY^{k+1}\). This is not an order claim
about a quotient tableau.

The zero gathered row \(r_1=h_2\) gives
\(L_1=\ell=-3\beta_{11}(1-c_{11})\delta\).
As the first-ten restriction of \(H_5\) has rank nine, \(L_2\)
is proportional to \(\ell\), with factor \(t\) read at site 10
where \(\ell_{10}=-b_{10}t^2\ne0\).
At site 9 put \(x=b_{10}t a_{10,9}\). Then
\(3x-b_9s^2=\ell_9,\ 4t x-b_9s^3=t\ell_9\).
Subtracting \(t\) times the first gives \(tx=b_9s^2(s-t)\).
Thus \(3x=2b_9s^2,\ \ell_9=b_9s^2\ne0\), and
\(L_{3,9}=(2st-s^2)\ell_9\) (*fiveSixVisible*).
Here \(b_9\ne0\) follows from the nonzero \(\rho_9\), its lack
of another contribution at that state in the support through
row 10, and the zero state aggregates of \(h_2\).
The rows \(\ell,\ell Y\) are independent (two distinct clocks
and two nonzero entries), and both kill the rank-eight
restriction of \(H_4\). Thus \(L_3\) is in their span, and its
values at 9 and 10 give \(L_3=(st-(s-t)Y)\ell\).

At physical row 7 there are only two later clean feeds from
stages 9 and 10, say \(x,y\) at \(k=1\). Hence
\[
 \begin{split}
 3(x+y)-b_7r^2&=\ell_7,\\
 4(sx+ty)-b_7r^3&=t\ell_7,\\
 5(s^2x+t^2y)-b_7r^4&=(st-(s-t)r)\ell_7 .
 \end{split}
\]
Use \(s^2x+t^2y=(s+t)(sx+ty)-st(x+y)\) and \(5t=3s\) to reduce
this to \(b_7r^2(r-s)^2/5=2s(r-s)\ell_7/25\).
Since \(r\ne s\), obtain \(5b_7r^2(r-s)=2s\ell_7\)
(*fiveSixSecondFeed*), rather than the old shift-two scalar.

Let \(B_c=X(X-u)(X-w)(X-\theta)(X-\xi)\).
Each interior clean weight is nonzero: deleting one would
leave five labels containing both endpoints or at most
four active labels. Thus the three \(X^{k+1}(1-X)L_3\)
tests give a nonzero barycentric row
\(b_x(1-x)L_3(x)B_c'(x)=T\ne0\) at the four interiors.
Indeed the cubic cannot vanish on all four labels and a
nonzero null vector of three Vandermonde moments on four
labels has all four entries nonzero.
The detector \(\ell\) kills \(C^k(G(c)-d)\) for \(0\le k\le3\),
giving a second barycentric row \(\ell_xG(x)B_c'(x)=D\)
on the five nonterminal clean clocks. It is nonzero at
\(\theta\) since \(G(\theta)\ne0\) by row 8.
For the two rows, \(DL_3(\theta)=TsG(\theta)\) and
\(DL_3(\xi)=-TtG(\xi)\); at row 7 the calculated elimination
gives \(5Tr(r-s)G(w)=2sDL_3(w)\). Subtract the comparisons
to obtain (*fiveSixComparisons*)
\[
 \begin{split}
 5G(\theta)L_3(\xi)+3G(\xi)L_3(\theta)&=0,\\
 5r(r-s)G(w)L_3(\theta)-2s^2G(\theta)L_3(w)&=0 .
 \end{split}
\]
No head evaluation is cancelled.

Adjoin the chronology \(6g_0+4u g_1+3u^2 g_2=0\).
With \(j=5-3s=5\xi,\ L=L_3(\theta),\ L'=125L_3(j/5)\),
multiply the first reflected equation by 25. Its coefficient
row is \((L'+75L,L'\theta+15Lj,L'\theta^2+3Lj^2)\).
The determinant of the three homogeneous rows is zero as
\(G\ne0\). It factors as
\(2(5w+3s-5)L_3(\theta)\,p_3(u,w,s)\); the first factors are
nonzero by paid 2, \(w\ne\xi\), and the barycentric row.
The clean hull with endpoints gives the three
\(\mathcal M_i((X-u)(X-w)(X-\theta)(X-\xi))=0\).
On this monic quartic use scales \(4200,12600,12600\), i.e.
\(840,2520,2520\) applied to the quintuple of the quartic.
The three resulting integer polynomials and the determinant
factor \(p_3\) have explicit arithmetic combination
*fiveSixDen* in the *fiveSixImpossible* leaf. The state/rank
and gathering steps above remain paper mathematics.

## One off: both audited forward alternatives

Use the purely forward source and weighted reduction in
[Single Off](WEIGHTED-ORDER-NINE-SINGLE-OFF.md), sections
“Weighted inputs, and audit of the forward bootstrap” and
“A weight-independent seventh-row dichotomy.”
The independent ranks \(F_3,F_4\) and separated \(E_4\) supply
the same constant amplitude \(g=Ac-c^2/2\) at its unique off
clock, and \(F_4=Kg+hP_{\le1}(c)\) with \(h=Ag\).
The no-identical-physical-row surgery preserves the weighted
tests and violates the twelve-row rank floor, just as at
shift two. The rank-nine versus rank-ten bootstrap for
\(gh=0\), then the full \(P_{\le5}(c)+Kg+hP_{\le2}(c)\),
uses the newly recomputed \(K R_5\) alias and \(R_5(1)=1\).
In the rank-ten case \(e_{12}\in E_5\) gives
\(g_{12}=h_{12}=0\) by the pure products with the live output.
The doubled-\(t\) intercept is unchanged, and \(R_5(t)\ne0\)
is an algebraic consequence of that intercept, not a reused
shift-two formula. The no-causal-interpolation proof uses
\(h_2=3\beta YA-\beta Y^2\) and its right \(A,Y\) images in
\(E_5^\perp\); its invariant-row contradiction now ends at
\(\beta Y\mathbf1=\ell_1(1-X)=1/3\ne0\). In that inverse-clock
calculation the coefficient is 3, not 4.
These, the \(E_4,H_j\) ranks above, and the nonzero clock from
\(\beta c=1/6\) are the only weight-dependent inputs in the
forward bootstrap. The first four features, fifth doubled
\(t=2d\) (here \(d\) is the first nonzero clean clock),
calibrated sixth clock \(z\), and seventh-row master residual
are pure forward actions.

The same late witness forces tied stage 8/9 clean at a
clock \(\theta\) not previously clean, by the normal charts
of \(v,Av\) and their actual eighth/ninth entries.
The two independently checked alternatives are:
* **New calibrated seventh clock.** The \(v\)-model is
  proportional to \(X^2(X-t)^2\). Its support relation
  \((C-\theta)(C-I)v=0\) pays three \(X^2(1-X)^2\) moments
  of the monic cubic \((X-t)^2(X-\theta)\). This forces it
  proportional to the **new** \(D_3\), impossible because
  \[
    (27-54X)D_3+(72X^2-72X+14)(D_3'/4)=1.
  \]
  This cubic has no double root even over nonordered fields
  (*repeatedCubicImpossible*).
* **Genuinely doubled seventh clock \(z\).** The two earlier
  doubled fibres force the model \(P=X(X-d)(X-2d)(X-z)\)
  after scaling. The same support relation pays
  \(\mathcal M_i((X-d)(X-2d)(X-z)(X-\theta))=0\).
  Both actual \(Av\)-values are zero on each earlier doubled
  fibre, forcing the polynomial part \(JP+\lambda R_5\) to
  vanish at \(2d,z\). This gives \(\Delta(P;2d,z)=0\).
  In *fibresImpossible*, use moment scales \(840,2520,2520\)
  and divide the \(60\Delta\) polynomial only by
  \(2dz(2d-z)\). Its nonzero certificate integer is
  *fibresDen*. Neither \(R_5\) value is cancelled.

These two alternatives and all other counts \(N,M\) have now
been excluded. This proves the paper floor of 13. The associated
Lean file checks local scalar assumptions, including shifted
moment normalizations and the coefficient-identity transfer;
it does not claim to formalize the rooted constructions above.

## Certificate and coefficient audit

Beyond the paid small scalars, the new scalar exits require only
the listed nonzero integer for the actual branch:
* Five/five reflected pair: \(503606\). Linear Radau pair: \(9287\).
  Linear Lobatto pair: \(233\). The repeated cubic uses constant \(1\).
* Anchored quadratic: \(498044911357686\).
* Quadratic pencil: \(19443497358891130087432166062370387383976122519321875687230682651062323832938540409939491709621111893980003298098780\).
* Six/six head root: \(4831112173336038819894072991438901734043067273116683106485949072000\).
* One-off doubled fibres: \(123027927115471870447978953148667838640085119266800\).
* Five/six reflected head: \(1621679820846283676525876655192978442995925401010634434091666890061123250231151135596924494030432360156245021240272000\).

All large certificates are explicit coefficient sums verified using
Lean integer normalization and transferable field evaluation, not
external Gröbner results trusted as axioms. The nonconstant
cancellations are exactly the literal clean-clock distinctions in
the three primitive minors and the factors \(w-\xi,L_3(\theta)\)
in the five/six determinant; the earlier two-feed identity cancels
\(r-s\). The paid \(10!\) already makes 2, 3, 5, 7, 12, and 14
nonzero. No sign, discriminant, or polynomial parameter is assumed
invertible without the indicated proof. A failed guard outside
characteristic zero is not evidence of a weighted method.

See [the separate ordinary order-eleven status](ERK11-AFTER-TWO-WEIGHTED-NINE-FLOORS.md)
for the exact common cutoff guard and the unsolved spike/sharp-width split.
