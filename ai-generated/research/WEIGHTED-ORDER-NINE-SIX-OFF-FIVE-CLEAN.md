# Six off clocks and five clean clocks at shift two

A strictly explicit, last-active twelve-row tableau exact on all rooted
profiles through size nine for \(\ell_2(P)=\int_0^1(1-X)^2P(X)\,dX/2\)
cannot have exactly six distinct off clocks and five distinct clean
clocks over a characteristic-zero field. More generally, the proof
works over a field paying \(11!\) with a nonzero integer coefficient
certificate for the actual linear/quadratic head branch. No order
on the field is used. This is a single branch exclusion; it does
not change the unrestricted weighted order-nine or ordinary
order-eleven stage bound.

Use the paid midpoint ranks and active-terminal conclusions of
[FourTap](WEIGHTED-ORDER-NINE-FOUR-TAP.md) and the actual late rank
deduction in [Off Gates](WEIGHTED-ORDER-NINE-OFF-GATES.md):
\(\dim F_4=3\), \(c_{12}=1\), \(\beta_{12}\ne0\), and
\[
             H_6=E_6+K e_{12},\qquad \dim H_6=11.
\]
Here stage indices in the statement are one-based.
Write \(d=Ac-c^2/2\). Six off clocks give independent \(d,Cd,C^2d\),
so these span \(F_4\). The product \(d^2\) fixes a scalar polynomial
\(G\) of degree at most two with \(d_i=G(c_i)\ne0\) on every off site.
A **state** is the pair consisting of the clock and the clean/off tag.

## Weighted quadrature and head nondivisibility

The seven paid moments \(\beta C^k d=0\), \(0\le k\le6\), cancel
each of the six off state aggregates. The scalar quadrature on the
five remaining clean labels is then exact through degree eight.
It has all five aggregates nonzero by the degree-four Gram and
includes the literal origin. A 5-label quadrature at both 0 and 1
would make its degree-five hull \(X(1-X)Q\), where \(Q\) is cubic;
the four zero moments against powers of \(X\) would contradict
the nonsingular degree-three \(X(1-X)^3\) Gram. Thus 1 is not clean.
If \(B\) is its monic clean hull, then \(B/X\) is the monic quartic
orthogonal to degrees zero through three for \(X(1-X)^2\). Hence
\[
                 B(X)=XR_4(X)/66,\qquad
                 R_4(X)=66X^4-120X^3+72X^2-16X+1 .
\]

For the first physical nonzero clean clock \(u\), every earlier clean
row has clock 0, and the rooted grade-three vector \(C(G(c)-d)\)
is zero on every predecessor. The grade-four primitive at this
row is exact, since all \(F_4=dP_{\le2}(C)\) defects vanish there.
It gives \(J(XG)(u)=0\). If \(G\) were constant this is impossible.
If \(G(0)=0\), the same test on \(G(c)-d\) gives \(JG(u)=0\);
the two primitive equations contradict a nonzero linear/quadratic
\(G\) with zero constant term. In particular \(G\) has degree one
or two, \(G(0)\ne0\), and \(R_4(u)=0\).

Suppose \(G\mid B\). Then \(G\mid R_4\) because \(G(0)\ne0\).
* For a normalized linear head \(X-w\), \(J(XG)(u)=0\) forces
  \(3w=2u\), with \(u\ne0\). The exact
  `SixOffFiveGate.linearRadauPairImpossible` rules out these two
  \(R_4\) roots when \(12687949=271\cdot46819\) is nonzero.
* For a normalized quadratic head \(X^2+gX+h\), the exact
  `HighOffGate.anchoredQuarticImpossible` from the high-off
  arithmetic leaf rules out \(R_4(u)=0\), the two zero
  remainder coefficients, and \(6h+4ug+3u^2=0\) whenever
  \(80683163243199125565174494540\) is nonzero. No hypothesis that
  the head splits or has distinct roots is used in that certificate.

Thus, under the indicated guard, \(G\nmid B\).

## Actual degree-six state rank

Let \(S\) be the space of all vectors constant on each of the
eleven distinct tagged states (five clean plus six off).
No physical rows are merged. The subspace
\[
                  P_{\le4}(c)+dP_{\le4}(c)
\]
has dimension ten, by independent polynomial interpolation on
five clean labels, then degree-four interpolation at the six
off labels. It lies in \(E_6\cap S\) by rooted inclusions.
If the intersection had dimension ten, the vectors
\(B(c)\) and \(CB(c)\) would be in this very subspace:
they are actual polynomials of degrees five and six and are
state-valued. They vanish on all five clean labels, so the
degree-four polynomial part would vanish identically in each
representation. Thus for some \(T,U\) of degree at most four,
\[
               B(x)=G(x)T(x),\qquad xB(x)=G(x)U(x)
                         \quad\text{on the six off labels}.
\]
Let \(D\) be the monic off hull (degree six). The polynomial
\(B-GT\) has degree at most six and vanishes at the six off
labels, so \(B-GT=aD\), and similarly \(XB-GU=bD\).
Nondivisibility gives \(a\ne0\); subtraction gives
\(G(U-XT)=(aX-b)D\). The head \(G\) is nonzero at every
off label, hence coprime to \(D\). Therefore
\(G\mid(aX-b)\), forcing its degree at most one. But then
\(B-GT\) has degree at most five, contradicting \(aD\).
This proves \(S\subset E_6\) as \(S\) has dimension eleven.
It is the forward two-polynomial argument underlying the archived
`RKCert.FixedFactor.five_on_state_le` in
`RKCert/CodimensionOneStateRank.lean` (there in the ordinary
legacy development with \(q=4\)); no ordinary order predicate
is being called as a weighted one.

## Why the last row cannot be duplicated or unique

From \(S\subset E_6\subset H_6\) and both dimensions eleven,
\(H_6=S\). The actual coordinate \(e_{12}\in H_6\) therefore
has to be state-valued, which means its terminal state is
unique: its value is one at row 12 and zero everywhere else.
But terminal clock 1 is not clean, hence row 12 is off.
Its physical off aggregate vanishes, and its last weight is
nonzero. This requires a **different off row at the same clock**,
contradicting the state-valued coordinate. In contrast, a
coincident clean row would not pay the off aggregate. This
terminal contradiction is checked in
`SixOffFiveGate.offTerminalImpossible` on the original
twelve physical coordinates.

## Formal status and coefficient scope

The exact linear-factor and terminal-coordinate assertions in
`SixOffFiveGate.lean` are Lean-core checked, as is the separately
supplied quadratic scalar gate in `HighOffGate.lean`.
The actual weighted rooted premise, paid spaces and the
scalar-chronology bridge above are paper-level deductions.
They are not asserted to be a new native theorem in the
reviewed RK `HasOrder` API. The archived forward theorem is
cited only for its algebraic argument, not as an implicit
order-conversion result. There is no real/ordered hypothesis.
The positive-characteristic extension uses \(11!\ne0\) and
the stated appropriate nonzero integer for the actual head
degree; certificate failure at a prime proves nothing about
existence there.
