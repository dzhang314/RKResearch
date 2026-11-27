# Five off clocks and six clean clocks at shift two

A strictly explicit, last-active twelve-row tableau exact on all rooted
profiles through size nine for \(\ell_2(P)=\int_0^1(1-X)^2P(X)\,dX/2\)
cannot have five distinct off clocks and six distinct clean clocks
over a characteristic-zero field. No ordering is used. Over a
field paying \(11!\), this argument requires that the exact
nonzero integer certificate constant below remain nonzero.

This is a branch exclusion. It does not by itself improve the
unrestricted weighted order-nine or ordinary order-eleven stage bound.
The proof uses the repeated clock at stages 8–9 and the shifted
resonance from [FourTap](WEIGHTED-ORDER-NINE-FOUR-TAP.md) and
[Off Gates](WEIGHTED-ORDER-NINE-OFF-GATES.md), not an ordinary
order-nine endpoint theorem.

## Packed actual states and the two early clean rows

Write \(d=Ac-c^2/2\), \(Y=I-C\), and
\(\rho=\beta A^2,\ \sigma=\beta A^3\). A state includes the clock and
the off/clean tag. The paid midpoint dimensions imply
\(F_4=dP_{\le2}(C)\), and \(d^2\in F_4\) makes
\(d_i=G(c_i)\ne0\) on off sites for a nonzero head polynomial
\(G\) of degree at most two. The physical terminal row is live at
clock 1, with the exact row identity \(3\beta A=\beta Y\).
Off aggregates of both \(\beta\) and \(\rho\) vanish by the seven
and five respective \(d\)-times-clock tests. Thus
\(h_2=12\rho-\beta Y^2\) has zero off aggregates and annihilates
\(E_6\). Its clock tests through degree six, restricted to six clean
states, also give zero clean aggregates. Since
\(h_{2,11}=-\beta_{11}(1-c_{11})^2\ne0\), row 11 must duplicate
one earlier state. There are exactly eleven distinct states in the
twelve rows, hence this is the sole duplicate; all first-ten states
are distinct. The polynomial state profile of degree five
\(P_{\le5}(c)+dP_{\le3}(c)\) has dimension ten by interpolation,
so it equals \(H_5=E_5+K e_{12}\). It is state-valued; the included
actual terminal coordinate therefore has a unique state. The
terminal state is clean since its off aggregate would otherwise
force its nonzero weight to vanish. The full state space \(S\)
has dimension eleven and lies in the kernel of \(h_2\), so
\(H_6=\ker h_2=S\).

The shifted off-gate result gives stage 8 off and stage 9 clean at
the same clock \(\theta\), with all five off states among the first
eight rows. Stage 10 is clean as well: all off states have already
occurred and the sole repeat is row 11. Write \(\xi=c_{10}\), and
put
\[
                    s=1-\theta,\qquad t=1-\xi,\qquad 3t=2s .
\]
Both are nonzero. The early eight rows have five distinct off
states and three clean states (0 and two nonzero states \(u,w\)
in physical order). We claim the second nonzero clean row is
physical stage 7. For a clean row \(i\), the incoming grouped off
charges \(r_i(x)=\sum_{j:\,c_j=x,\ d_j\ne0} A_{i,j}d_j\)
have zero \(1,X\) moments because \(Ad,ACd\) are pure of grade
at most four. Its ordinary primitive tests on \(X,X^2,X^3\)
are exact. If the first nonzero clean row \(u\) had fewer than
three earlier off states, these two zero moments would make
all its off charges zero. Then its exact \(AX=u^2/2\) would
give zero, impossible (all earlier clean clocks are 0).
If the second nonzero clean row \(w\) preceded the fourth
early off label, both clean rows would have the same three
off labels and proportional off charges, by the same two
moments. Test their incoming coefficients on
\((X^2(X-u)^2)'\). All earlier clean contributions vanish
at 0 and \(u\); the first primitive is zero at \(u\), hence
the second also would be zero at \(w\). This would give
\(w=0\) or \(u\), contradiction. So \(w\) must follow all
four early off rows and the first two clean rows 0 and \(u\).
It is stage 7. In particular stage 8 is off and there are only
two later clean rows in the first-ten prefix.

At the first nonzero clean row \(u\), the actual vector
\(C(G(c)-d)\) vanishes on every predecessor, as the mask is zero
off and at clock 0. Its rooted primitive of grade at most four
at this clean row is exact. Therefore \(J(XG)(u)=0\).
Writing \(G=g_0+g_1 X+g_2 X^2\), this gives
\[
                   6g_0+4u g_1+3u^2 g_2=0.                  \tag{1}
\]

## The actual gathered adjoints

Let \(j<11\) be the unique donor whose state row 11 repeats,
and let \(\Delta=A_{11,*}-A_{j,*}\) restricted to the first
ten columns. This is an actual incoming row difference, not
a quotient tableau. It kills \(H_5\) because \(A E_5\subset
E_6\subset S\), and \(A e_{12}=0\). Its coefficient at 10 is
\(a_{11,10}\ne0\), from the live suffix; the donor row has zero
there by strictness even if \(j=10\).

Write \(B\) for the literal first-ten leading block. Let \(b\)
be the aggregated \(\beta\) row on the ten nonterminal states
represented on the first ten sites: add the contribution of
row 11 at its donor, discard the endpoint row for these
positive-\(Y\) reads. It is zero on off states. For \(k\ge1\)
let \(Y\) also denote the unchanged diagonal of the first ten
clocks, and put
\[
              L_k=(k+3)(bY^k)B-bY^{k+1}.
\]
The actual full weighted adjoint \(r_k=(k+3)\beta Y^k A-
\beta Y^{k+1}\) kills \(E_{7-k}\) by the shifted primitive
identity (cost \(k+1\)); it kills \(e_{12}\) as well. Its
gathered row is
\[
                 \overline{r_k}=L_k+(k+3)\beta_{11}
                                 (1-c_{11})^k\Delta .
\]
Indeed the endpoint weight drops after the first \(Y\), and
row 11 contributes its actual incoming row instead of the
incoming row of its donor. Clock multiplication commutes
with gathering because the duplicate clocks are equal.
The state-valued interpretation is used only for the inputs
\(E_4,E_5,E_6\), already established, not for \(A\) on all inputs.

Now \(r_1=h_2\) has zero gathered row. Write
\(\nu=-4\beta_{11}(1-c_{11})\ne0\), \(\ell=\nu\Delta\).
Then \(L_1=\ell\). The restrictions of \(H_5\) to the first
ten sites have dimension nine (their only kernel on \(H_5\)
is the endpoint line; row 11 is a state copy). Hence
\(L_2\) is proportional to \(\ell\). At the final prefix site
10, \(L_{1,10}=-b_{10}t^2\ne0\) and \(L_{2,10}=-b_{10}t^3\),
so \(L_2=t\ell\).
At site 9 put \(x=b_{10}t a_{10,9}\). The two equations are
\[
  4x-b_9s^2=\ell_9,\qquad 5t x-b_9s^3=t\ell_9 .
\]
Using \(3t=2s\), they give \(2x=b_9s^2,\ \ell_9=b_9s^2\).
Also \(L_{3,9}=6t^2 x-b_9s^4=(2st-s^2)\ell_9\).
Here \(b_9\ne0\), for instance from the earlier
\(\rho_9\ne0\) and the equality of state aggregates
\(12\rho=\beta Y^2\). The two nonzero detector coefficients
at the different clocks \(s,t\) mean \(\Delta,\Delta Y\)
are independent on the prefix. Both kill the rank-eight
restriction of \(E_4\) (use \(Y E_4\subset E_5\) for the second).
Thus \(L_3\), which kills that restriction, has the form
\((p+qY)\ell\). Its evaluations at sites 10 and 9 give
\(p+qt=t^2,\ p+qs=2st-s^2\), hence
\[
                         L_3=(st-(s-t)Y)\ell .
\]

At stage 7 put \(r=1-w\); \(r-s\ne0\) by clean-state
distinctness. The only two later clean feeds in \(bY^k B\)
are from stages 9 and 10. Set \(x=b_9 s a_{9,7}\) and
\(y=b_{10} t a_{10,7}\). The three equations are exactly
\[
\begin{split}
 4(x+y)-b_7r^2&=\ell_7,\\
 5(sx+ty)-b_7r^3&=t\ell_7,\\
 6(s^2x+t^2y)-b_7r^4&=(st-(s-t)r)\ell_7 .
\end{split}
\]
Eliminate the two feeds, using resonance and the paid
nonzero \(20(r-s)\). One obtains
\[
                        3b_7r^2(r-s)=s\ell_7 .
\]
These endpoint and feed eliminations are checked in
`FiveSixGate.twoVisibleWeights`, `affineMode`, and
`eliminateSecondClean`; the dimension and gathering
steps are proved above in paper form.

## Two exact clean barycentric rows

Let \(Q\) be the monic hull of \(u,w,\theta,\xi\), and
let \(B_c(X)=XQ(X)\), the five nonterminal clean hull.
Use
\[
                           L_3^*(X)=30X^3-36X^2+12X-1 .
\]
This is the checked cubic orthogonal to \(1,X,X^2\) for
\(X(1-X)^3\). Every interior clean weight is nonzero:
if one were zero, the remaining at most five active labels
either include both endpoints (impossible for a five-node
degree-eight quadrature by the paid endpoint Gram),
or have at most four active labels since the final weight
is live (impossible by the degree-four Gram).
The three exact \(X(1-X)L_3^*(X)\) clock tests make the
four interior charges \(b_x x(1-x)L_3^*(x)\) a barycentric
row on the four nodes, nonzero because the cubic cannot
vanish on all four. Thus there is a nonzero scalar \(T\) with
\[
                  b_x(1-x)L_3^*(x) B_c'(x)=T
                 \quad(x=u,w,\theta,\xi).
\]
This also proves \(L_3^*\ne0\) at each of those clocks,
without a sign argument.

The detector \(\ell\) annihilates the rooted mask
\(G(c)-d\) times powers up to degree three (total grade
at most five). So its five nonterminal clean charges
\(\ell_x G(x)\) have zero moments through degree three.
This is another barycentric row, with common
\[
                     \ell_x G(x)B_c'(x)=D .
\]
It is nonzero, detected at \(\theta\) by
\(\ell_\theta=b_9s^2\ne0\) and by \(G(\theta)\ne0\) from
the off stage 8 at that very clock.
Substitute the calculated reads at 9, 10, and 7 into the
two barycentric identities. Comparing 9 to 10 gives
\[
        3G(\theta)L_3^*(\xi)+2G(\xi)L_3^*(\theta)=0.          \tag{2}
\]
Comparing 7 to 9 gives
\[
        3r(r-s)G(w)L_3^*(\theta)=s^2G(\theta)L_3^*(w).        \tag{3}
\]
The core lemma `FiveSixGate.cleanHeadEquations` checks these
comparisons without division by a head value, weight or
cubic evaluation.

## The determinant and its exact arithmetic certificate

Equations (1)–(3) are homogeneous linear constraints on
the three coefficients of a genuinely nonzero \(G\), so
their \(3\times3\) determinant vanishes. Define
\(\theta=1-s,\ j=3-2s=3\xi\), and set
\[
 L=L_3^*(\theta),\qquad L'=30j^3-108j^2+108j-27 .
\]
After multiplying (2) by 9, the second row has entries
\((L'+18L,\ L'\theta+6Lj,\ L'\theta^2+2Lj^2)\).
The first row is \((6,4u,3u^2)\); (3) is the third row.
The determinant factors as
\[
               (2s+3w-3)\,(30s^3-54s^2+30s-5)\,D_7(u,w,s),
\]
where \(D_7\) is the explicit degree-seven polynomial in
`FiveSixGate.rootp3`. The factors before \(D_7\) are
\(3(w-\xi)\) and \(-L_3^*(\theta)\), both nonzero as just
proved. These are the only non-numerical guards in the
determinant factorization.

Because the six clean states \(0,u,w,\theta,\xi,1\) carry
exact degree-eight quadrature, their hull implies that
\(Q=(X-u)(X-w)(X-\theta)(X-\xi)\) has its three scalar
moments against \(1,X,X^2\) zero with \(X(1-X)^3\).
Use the denominator-cleared \(3Q\) and scale the moments
by \(2520,2520,27720\), respectively. After cancelling 3
on the first, these are the three polynomials
`rootp0`, `rootp1`, `rootp2` in the same scalar leaf.
Their exact expansion is checked.
The four polynomials, including \(D_7\), have an explicit
integer coefficient identity
\[
                  \sum_{i=0}^{3} a_i\,p_i=D_{\rm five/six}
\]
with the nonzero constant
\[
D_{\rm five/six}=
132984843803701111084755487750028773712626992326900845222721631503421536172242485130186197807889987591426757400780800 .
\]
The certificate is explicit in the Lean leaf; it was discovered
by rational elimination but replay merely checks exact integer
coefficients and field evaluation. No polynomial parameter
or resultant is inverted. The sole additional finite
characteristic guard beyond paying \(11!\) is the specified
nonzero integer constant. A prime at which it vanishes
is not a verified exception to the mathematical result.

## Formal and historical boundaries

`FiveSixGate.lean` checks the reflected scalar eliminations,
barycentric comparison, matrix singularity from a live head,
exact determinant factorization, shifted moment normalizations,
and the integer certificate. The actual weighted rooted order
paying those premises, state aggregation, late dimension ranks
and mask chronology are documented above, not claimed as a
new end-to-end theorem in the human-reviewed RK `HasOrder`
API. The ordinary `RKCert.ERKOrderNineFiveSix*`
development served as a structural source for gathered adjoints;
its ordinary weights, ordering, and scalar atlas are not used
as a weighted proof.

Together with the preceding six-off and high-off results, this
leaves only a single off clock in the shift-two weighted
twelve-row census over characteristic zero. The single-off
case, shift one, and the order-eleven rank/spike branch
remain independent.
