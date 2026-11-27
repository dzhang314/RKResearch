# The high-off branch of twelve-stage weighted order nine at shift two

A twelve-row strict explicit tableau with active final output, exact on
all rooted stage profiles through size nine for
\(\ell_2(P)=\frac12\int_0^1(1-X)^2P(X)\,dX\), cannot have eight or
more distinct off clocks over a characteristic-zero field. An off
clock is counted only where the quadratic stage defect
\(d=Ac-c^2/2\) is nonzero; the same clock in a clean row is a
different state. No order, sign, or completeness of the field is used.

More generally, this proof works over a field paying \(11!\) if the
integer certificate constant for the actual branch is nonzero in it.
Those constants, and the precise hypotheses of the Lean interfaces,
are given below. This closes the high-off **branch**; it is not an
unconditional order-nine or order-eleven stage improvement.

## Actual late column and the effective clean count

Use [the four-tap terminal classification](WEIGHTED-ORDER-NINE-FOUR-TAP.md)
and [the exact late dimensions](WEIGHTED-ORDER-NINE-OFF-GATES.md).
Let \(N\ge8\) be the number of distinct off states, so the number
\(M\) of distinct clean states is at most four. Saturation gives
\(F_4=dP_{\le2}(C)\), and \(d^2\in F_4\) fits a polynomial \(G\) of
degree at most two with \(d_i=G(c_i)\ne0\) on off sites. In particular
all of \(E_4\) is state-valued and its columns are \(P(c)+dQ(c)\) with
\(\deg P\le4,\deg Q\le2\). Take the four-tap witness \(v\):
it vanishes through row 7, its grade-four model is \(P\),
its eighth coordinate is nonzero, and its support lies at clocks
\(\theta=c_8=c_9\ne1\) and 1. The **off** polynomial \(P+GQ\) of degree
at most four vanishes at every off label except possibly \(\theta,1\).
There are at least six other distinct off labels. Thus \(P+GQ=0\)
and \(v\) vanishes at all off sites. In particular stage 8 is clean.
Because row 1 is clean at 0 and \(v_1=0\), \(\theta\ne0\).
Also \(G(\theta)\ne0\) as \(v_8=P(\theta)=-G(\theta)Q(\theta)\ne0\).

For completeness, the elementary first-clean chronology supplies both
\(G(0)\ne0\) and \(1\le\deg G\le2\). At an actual clean row the pure
vectors \(Ad\) and \(ACd\) vanish, since they belong to \(F_4=dP_{\le2}(C)\).
The first nonzero clean row at clock \(u\) sees only 0 on earlier
clean rows, and \(X(G(c)-d)\) is zero on every predecessor. Its order
through numerical grade four gives \(J(XG)(u)=0\),
where \(J\) is the lower primitive. A nonzero constant \(G\) would
give \(G u^2/2\ne0\). If \(G(0)=0\), the same reasoning with \(G(c)-d\)
gives \(JG(u)=0\); for a linear/quadratic polynomial of zero constant
term the two primitive evaluations at \(u\ne0\) force \(G=0\)
by the \(2\times2\) determinant (only 2,3,4 are used).
This is the ordinary forward calculation
`ERKLowEndpointCore.first_nonzero_on_forces_head_shape`,
independent of output moment weighting.

Let \(M_*\) count the distinct clean labels where \(G\ne0\).
It counts 0 and \(\theta\), so \(2\le M_*\le4\).
Put \(B(X)=\prod_{x\,\mathrm{clean},\,G(x)\ne0}(X-x)\).
On physical sites the polynomial vector \(G(c)B(c)\) equals \(dB(c)\):
on off sites this is the defining head fit, and on clean sites both
sides vanish. Therefore
\[
             \ell_2(G B X^k)=0\qquad(0\le k\le 6-M_*).
\]
The grade budget here is \(2+M_*+k\le8\), not \(\deg G+M_*+k\).
Since the hull contains 0, \(GB=XW\), \(W\ne0\). If \(M_*=2\), or
if \(M_*=3\) and \(G\) is linear, then \(\deg W\le3\) and at least
four consecutive moments vanish. The paid nonsingular Gram for
\(X(1-X)^2\) makes this impossible. This leaves exactly:
\(M_*=3,\deg G=2\); \(M_*=4,\deg G=1\); \(M_*=4,\deg G=2\).

## \(M_*=3\): the anchored Radau divisor

Here \(GB/X\) is a degree-four polynomial orthogonal to \(1,X,X^2,X^3\)
against \(X(1-X)^2\). Hence it is a nonzero scalar multiple of
\[
                          R_4=66X^4-120X^3+72X^2-16X+1
\]
by the paid Gram and the four fixed moments (see the companion Off Gate
certificate). Because \(G(0)\ne0\), \(G\mid R_4\).
Every nonzero clean label, whether a root of \(B\) or of \(G\),
is a root of \(R_4\). In particular the first nonzero clean clock \(u\)
satisfies \(R_4(u)=0\) and \(J(XG)(u)=0\).
Normalize \(G=X^2+gX+h\) by its leading coefficient.
The latter equation gives
\[
                        C_0:=6h+4ug+3u^2=0
\]
after removing the nonzero \(u^2\) and the paid factor 12.
The monic division of \(R_4\) by \(G\) has linear remainder with
coefficients
\[
\begin{split}
r_1&=-66g^3-120g^2+132gh-72g+120h-16,\\
r_0&=-66g^2h-120gh+66h^2-72h+1 .
\end{split}
\]
Both vanish by divisibility, even if the first clean clock itself
is a root of \(G\) or if \(G\) does not split in the coefficient field.
The exact ideal certificate of `anchoredQuarticImpossible` excludes
\(R_4(u)=r_1=r_0=C_0=0\) whenever its constant is nonzero:
\[
               D_{\rm anchor}=80683163243199125565174494540.
\]
There is no distinct-root, sign, or irreducibility premise in this gate.

## \(M_*=4\): literal placement and a two-endpoint polynomial test

Now \(M=4\), \(N=8\), and every state occurs exactly once.
The degree-five state profile \(P_{\le5}(c)+dP_{\le3}(c)\)
has dimension ten. Indeed the off polynomial in any relation
has degree at most five and vanishes at eight distinct sites, so
is zero. The clean equations now force its degree-three head multiplier
to vanish at all four clean clocks, since \(G\ne0\) on them.
This profile lies in \(H_5=E_5+K e_{12}\) and equals it by the
reverse dimension cap. The terminal coordinate \(e_{12}\) belongs
to it; if row 12 were off, its off polynomial would vanish at the
other seven off clocks, hence everywhere, impossible. Therefore
row 12 is clean at clock 1.

All eight off weights \(\beta_i\) are nonzero. If one were zero, the
other at most seven would be eliminated by the seven test rows
\(\beta d C^k=0\), \(0\le k\le6\), using \(d_i\ne0\) and Vandermonde.
The remaining four clean nodes alone cannot carry a degree-eight
quadrature (the degree-four paid Gram has rank five). Now \(Av\)
starts at row 9 and has nonzero ninth coordinate, by the live
edge from row 8; row 12 is clean. Apply the two pure tests
\(\beta(d\odot Av)=\beta C(d\odot Av)=0\), of grades 7 and 8.
They are supported on the off sites among rows 9–11. If fewer than
three, Vandermonde would force all their contributions zero and
in particular rule out the ninth coordinate, which is off because
row 9 at \(\theta\) cannot share row 8's unique clean state.
Thus rows **9, 10 and 11 are all off**. The clean states are exactly
0, a nonzero \(u\) strictly before row 8, \(\theta\) at row 8, and
1 at row 12, all distinct. In the equations below write \(z=\theta\).

After scaling \(v\) and \(G\) by nonzero scalars, its polynomial model
is
\[
                          P=X(X-u)G .
\]
Indeed \(P=-GQ\), its values at the first two clean states 0 and \(u\)
are zero, \(G\) does not vanish there, and the multiplier \(Q\)
has degree at most two. The first-nonzero-clean test is still
\(J(XG)(u)=0\). Use the four-label clean hull in the previous moment
identity. With \(S=(X-u)(X-z)G\), the three exact equations are
\[
            \int_0^1 X(1-X)^3 S(X)X^k\,dX=0,\qquad 0\le k\le2.
\]
For \(\deg G=1\), \(S\) is the constant-normalized fixed cubic
\[
                        L_3(X)=30X^3-36X^2+12X-1
\]
by the paid \(X(1-X)^3\) Gram. If \(G\) is monic linear then
\(J(XG)(u)=0\) places its root at \(2u/3\); hence both \(u\) and \(2u/3\)
would be roots of \(L_3\). The exact cubic certificate
`lobattoCubicPairImpossible` has nonzero integer constant \(4349\).

## \(M_*=4,\deg G=2\): an actual grade-five minor in addition to moments

The v-column has \(v_{12}=P(1)\ne0\): \(G(1)\ne0\) and \(u\ne1\).
As \(v\) is supported at \(z\) and 1, \((C-z)v\) is a nonzero multiple
of \(e_{12}\) and lies in \(E_5\). Thus \(E_5=H_5\) has dimension ten.

If there were no polynomial alias in grade five, the genuine
\(E_5\)-to-polynomial map would be an exact dense size-six decoder
on ten rows, contradicting the [paid dense width eleven](erk-dense-width/README.md).
For any alias polynomial \(R\) at grade five, the literal origin
gives \(R(0)=0\) and the four tested moments give
\(\ell_2(RX^k)=0\) for \(0\le k\le3\).
The Gram rank therefore leaves exactly one line of possible aliases,
and it is generated by \(R_5=XR_4\). In the formal pair space through
degree five, the actual-vector projection has image dimension ten
and kernel dimension one, whereas the polynomial projection has
image dimension six (all bush powers). Its pure subspace thus has
dimension five. The four independent \(dP_{\le3}(c)\) directions
and \(R_5(c)\) lie in it; the last is independent of the first four
because it reads \(R_5(1)=3\ne0\) at the clean terminal row.
In particular every grade-five pure vector restricted to clean
sites is a scalar multiple of \(R_5(c)\).

Apply this to \(Av-(JP)(c)\). The actual column \(Av\) is zero
through row 8, including both \(u\) and \(z\). Necessarily
\[
             (JP)(u)R_5(z)-(JP)(z)R_5(u)=0 .
\]
No value of \(R_5\) has been divided out, and the pair-space reasoning
does not assume separation at grade five.

The three two-endpoint moments and this additional equation, together
with \(C_0=6h+4ug+3u^2=0\) for the monic \(G=X^2+gX+h\),
are exactly the premises of `lobattoQuarticImpossible`.
The inputs use integer-scaled moments \(2520,2520,27720\)
for the three successive weights, and \(60\) times \(JP\) for the
last equation. No polynomial parameter, determinant of a pivot, or
discriminant is inverted. Algebraic reduction substitutes
\(6h=-(4ug+3u^2)\) by denominator-cleared identities,
and cancels only the chronological distinctness factor \(u z(u-z)\)
and small paid factors 2 and 3. The resulting three-polynomial-variable
equations \(p_i(g,z,u)=0\), \(0\le i\le3\), have an explicit integer
certificate
\[
                         \sum_{i=0}^3 a_i p_i=D_{\rm pencil}\ne0
\]
with the positive integer
\[
\begin{split}
D_{\rm pencil}={}&28490536521647715398803728665041008150877879584339128685405854996049022519311418790877681183673807511726935902368650796170924416054081062517771673800000000000 .
\end{split}
\]
The coefficients, not a call to a Gröbner solver, are in the Lean file.
Exact ideal search was only the discovery mechanism. The check is an
integer polynomial identity, valid over all fields in which that
constant is nonzero.

## Domains, exact guards, and Lean boundary

Chronology and rank arguments need a nonzero coefficient field and
\(11!\ne0\); they never use ordering. The exact scalar gates additionally
need the specified nonzero integer in their own branch. For the
anchored gate the primes not already excluded by \(11!\) that divide
its exhibited constant are \(53,97,227,8893,98009,270890933\).
The cubic gate has \(4349\). The pencil gate is stated with the exact
integer above, without attempting to optimize its bad-prime set.
Over characteristic zero every one of these constants is nonzero.
Over positive characteristic a zero certificate constant is a guard
failure, not evidence that a weighted tableau exists.

The separate core Lean leaf checks the polynomial identity transfer to
an arbitrary field, the exact three scalar gates (including their
normalizations), and the small moment rational arithmetic. The
weighted rooted-order, chronological/rank and dense-width bridge above
is a documented mathematical proof, not a single native Lean theorem
on weighted tableaux. Assigning the result to \(\beta=bA^2\) needs
no extra hypothesis beyond its paid shifted order; it does **not**
eliminate the other possible off counts. The \(N=1,5,6\) branches and
the main order-eleven rank/spike conditions must still be checked
independently.
