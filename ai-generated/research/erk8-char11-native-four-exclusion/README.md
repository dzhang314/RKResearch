# ERK8: native four-off exclusion in characteristic 11

For any field \(K\) with \(11=0\), consider a literal strictly lower
\(A:\mathrm{Fin}(10)\times\mathrm{Fin}(10)\to K\) and physical weights
\(\boldsymbol b\) satisfying the reviewed \(\mathrm{HasOrder}\ 8\).
The two main Lean endpoints are in
RKResearch.Certified.Graded.ERK8CharEleven:

- **no_four_off_char11**: the count of distinct off clocks is not four.
- **order8_char11_only_one_off**: that count is exactly one. This uses
  the earlier native five-off and seven-off exclusions as well.

No hypothesis restricts the field to the prime field or a particular
finite extension. The four-off endpoint starts from the literal
tableau and has no caller-supplied rank, chronology, scalar
nonvanishing, or chart assumption. It does not itself exclude one off.
In particular it is not yet an end-to-end native eleven-stage lower
bound. The [mathematical stage-floor proof](../erk-eight-char11/README.md)
and the separate eleven-stage upper certificate remain distinct.

## Centered head

The paid physical split earns the literal first nonzero clean row
\(k=4\) or \(5\). In the centered orientation it has clock
\(6=1/2\), and the fitted defect is a nonzero scalar multiple of
\(q=X^2-X+8\). The early Newton and sentinel arguments use only off
injectivity before physical row 6, rather than the ten distinct tag
assumption of the earlier five-off branch. They exclude \(k=5\).
For \(k=4\), physical row 5 has clock 2, and the monic four-off
hull \(N_4\) has nonzero remainder proportional to \(6+2X\) modulo
\(q\).

The centered tail proof shortens the source proof's cofactor step.
Let \(\boldsymbol c=A\boldsymbol1\), and let
\(\boldsymbol\Delta=A^{\mathsf T}(\boldsymbol e_8-\boldsymbol e_i)\),
where \(i,8\) is the actual repeated tag. A polynomial correction
of degree at most two makes the degree-four test
\(N_4(\boldsymbol c)\) vanish on the clean anchor tags at \(0,6,1\)
without changing any off value or either quadratic clean value.
The correction is built from paid pure and defect columns, so the
new test lies in \(E_4\). Its pairing with
\(\boldsymbol\Delta\in E_4^\perp\) has only two live terms:
\[
 \Delta_6 N_4(x)+\Delta_7 N_4(z)=0,
 \qquad x=c_6,\quad z=c_7 .
\]
All early terms have been cut or are nodal roots, the terminal term
is cut, and \(\Delta_8=0\) by strictness. No projected cofactor
construction or hypothesis that a particular early residue is
nonzero is needed.

The native first and second reflected equations are paid at the
original physical columns 6 and 7. They explicitly include the
weight of row 8 in the appropriate clean tag when the earlier repeat
is itself at 6 or 7, and use the actual row difference for its
integration contribution. The paid pure anchor probe gives equal
nonzero clean masses at \(x,z\). Eliminating the single late tap yields
\[
 (6+2z)x^3 + (6+2x)z^2(3x-2z)=0 ,
\]
which contradicts \(x+z=1,\ xz=8\) in characteristic 11. Both
physical placements are closed in **no_actual_centered_four_off**.

## Noncentered head

The new generic modules earn the terminal hull identity and the
actual Newton rows before scalar specialization. If \(P\) is the
fitted quadratic, \(D\) is the monic four-off hull, and \(Q\) is the
monic hull of \(0,h,x,z\), the actual terminal profile gives
\[
 Q + P R_2 = \sigma D,\qquad \sigma\ne0.
\]
For a polynomial \(G\) of degree at most four, interpolate \(G/P\)
on each hull to get cubics \(U_D,U_Q\). Both quotient remainders
\[
 P U_D-G = D V_D,\qquad P U_Q-G = Q V_Q
\]
have \(V_D,V_Q\) of degree at most one. The terminal identity makes
\(D(V_D-\sigma V_Q)\) a multiple of \(P\). Coprimality and degree
then give \(V_D=\sigma V_Q\); comparing degree five transfers the
leading cubic coefficient. Here invertibility at each interpolation
site and coprimality are explicit, and no splitting of \(P\) is used.

The literal Newton adapter interpolates \(X^r/P\) on the first
three off senders for \(r=1,2,3\); a degree-one interpolation
remainder transports into the paid degree-two defect band and
has zero top coefficient. The only possible clean contribution to
the physical off outputs is the first clean coordinate when at row
4, and it is absent at row 5. The same interpolation earns the
row-4 clean gain from the original pure primitive columns.
The generic field theorems **actual_terminal_hull_transfer**,
**nodalMeasure_transfer_four**, **paid_newton_physical**, and
**paid_newton_clean_transfer** are in namespace
RKResearch.Certified.Graded.FourOffNewton. The transfer accepts
exact quadratic degree and nonvanishing on the four clean nodes
as explicit hypotheses; the characteristic-11 chart below earns
them. The adapter is also usable outside characteristic 11, but
these generic modules do not certify the other scalar specializations
or a linear fitted defect.

For \(q(h)=0\) there are exactly two algebraic orientations:
\((x,z)=(6,1-h)\) or \((1-h,6)\). The two choices of \(h\) are handled
by the same polynomial identities. The native scalar certificate
uses explicit cofactor reductions by \(h^2-h+8\) and 11. To record its
scale, write \(C_r\) for the clean top coefficient of \(X^r/P\) and
\(\kappa\ne0\) for the raw shape scale. The four values
\((\kappa C_1,\ldots,\kappa C_4)\) are respectively
\((8+h,7+10h,9h,4h)\) and \((7+4h,0,6+2h,4+8h)\).
Every inverse, the quadratic leading coefficient and all three final
nonzero quantities have explicit multiplication receipts. The two
chronological cases consume these receipts in
**no_actual_noncenter_four_off**. No enumeration of tableaux,
bounded point search, or computational oracle is used.

## Verification

From ai-generated/lean with the corresponding Mathlib checkout:

    lake build +RKCert.ReviewedNative.ERK8CharElevenFourExclusion

The frozen Lean 4.36.0 replay log and source digest list are adjacent.
The printed endpoints use only propext, Classical.choice and
Quot.sound. This packet does not claim a whole dependency build on
another release.
