# Dependent reflected quadratic seed in the lone invisible ERK10 ghost case

Continue the [single invisible ghost](ERK10-SINGLE-INVISIBLE-GHOST.md)
and [one outgoing clock](ERK10-SINGLE-INVISIBLE-GHOST-FIFTH-ROW-EXCLUSION.md)
chart over a characteristic-zero field. Physical row 2 has the
sole zero output weight and its actual \(r=Ae_2\) is supported at a
single clock \(t=c_3\). Write \(u\) for the genuine reduced reverse
quadratic defect (on the thirteen live sites), and suppose \(u\)
is proportional to \(r|_I\). In this **dependent** fork:
* the last actual nonzero \(r\)-tap is physical 13, every nonzero
  amplitude of \(r\) is identical, and the rank-two room \(W_2\)
  is not clock-invariant;
* \(r_{11}=r_{12}=0\); physical 11 and 12 are both genuine
  noncarrier response sites in the reduced reverse, with distinct
  nonzero reflected clocks;
* the literal reverse repeat gives \(c_{10}=c_{11}=2c_{12}-1\);
  \(A_{11,10},A_{12,11},A_{13,11},A_{13,12},A_{14,13}\) are all nonzero.

No complete nonexistence result for this fork is claimed.
The proof uses only the actual low-degree reverse and exact
original grade spaces, not full order ten of the reduced reverse.
Indices are one-based physical indices unless specifically called
reversed indices.

## 1. The reverse square is paid into the linear room

Use \(I=\{1,3,\ldots,14\}\), the weighted transposed live matrix
\(A^\vee=B_I^{-1}(A_{I,I})^\mathsf{T}B_I\), and the
linear reverse spaces \(W_i=B_I^{-1}(E_{8-i}^\perp|_I)\)
of ranks \(i=1,2,3\). The invisible-ghost ledger proves
\[
 W_{i+1}=W_i+C W_i+A^\vee W_i,\qquad
 \bar F_2=W_1=Ku,\quad \bar F_3=W_2,\quad
 \bar F_4=W_3+\langle u^2\rangle ,
\]
as well as noninvariance of \(W_3\).
There is no extension of the pure model map past the stated
degrees. Since \(u_{13}\ne0\) from the actual shifted-nine tap,
dependence already forces \(r_{13}\ne0\), and \(t\ne1\).

The original \(f_4=4\) throughout this one-clock chart:
if it were 3, strict growth would give
\(F_3=\langle e_2,r\rangle\), which is clock-invariant,
contradicting the reviewed outgoing grade-three Hermite gain
of two dimensions. Thus \(F_4|_I=W_3\) (projection loses
precisely the pure ghost line), and noninvariance and the
rank-four projection of \(F_5\) give
\[
                  F_5|_I=W_3+C W_3 .
\]
Write \(u=a r|_I\), with \(a\ne0\).
For any actual \(w\in F_4\) we have
\(\langle u^2,w_I\rangle_{B_I}=a\langle u,(rw)_I\rangle_{B_I}=0\):
\(rw\) is an actual grade-seven product and \(u\) is the
normalized annihilator of \(E_7\). Multiplication by \(C\)
does not change the vanishing, because \(u^2\) is supported
at clock \(t\). Pairing against any clock polynomial is zero
as well, since \(b r^2=0\) and \(r\) is supported at \(t\).
These checks exhaust \(E_5|_I\) (clock polynomials plus
the projected pure flag), hence \(u^2\in W_3\). Therefore
\(\bar F_4=W_3\) is genuinely of rank three.

If \(W_2\) were clock-invariant, the actual reduced reverse
outgoing Hermite gain at degree three would instead give
\(\dim\bar F_4\ge4\). The required separation through degree
three follows from \(\bar F_3=W_2\) and ordinary exact scalar
clock moments: a polynomial in that room kills its four
clock moments by the paid row pairing, so is zero by the
ordinary four-by-four Hilbert matrix. Hence \(W_2\) is not
clock-invariant.

Set \(s=A^\vee r_I\). Because \(Cr=tr\), the ranks and
noninvariance now give
\[
                W_2=\langle r,s\rangle,\qquad
                W_3=\langle r,s,Cs\rangle .
\]
The function \(s\) has nonzero entries at at least two
different clocks outside \(t\): otherwise the second span
decomposes under \(C\) into its blocks at just \(t\) and the
one possible other support clock, making it invariant.
An affine polynomial of \(C\) times \(s\) cannot vanish
on two such different clocks unless both coefficients
are zero. Since \(u^2\) is supported at \(t\), it therefore
lies in \(Kr\). It follows that \(r_i^2\) is a fixed multiple
of \(r_i\) and all nonzero \(r_i\) are the **same** nonzero
amplitude. Their output weights consequently sum to zero.

In fact the only possibly nonzero single-clock vector from
\(W_3\) lies in \(Kr\). To see this for a clock \(v\ne t\),
if \(s\) has at least three different off-\(t\) clocks, an
affine factor multiplying \(s\) would have to vanish at
two other off-\(t\) labels. If it has exactly two, the
\(t\)-block of \(s\) cannot be in \(Kr\) (otherwise \(W_3\)
is spanned by \(r\) and the two off-\(t\) support projections,
hence invariant). To cancel on the \(t\) block requires
the affine factor to vanish at \(t\) as well as the other
off-\(t\) label. In either case it is zero, leaving no
nonzero vector at \(v\).

## 2. The first five live-reverse rows are genuinely distinct

Suppose reversed physical row \(i=12\) or \(11\) were a
literal duplicate of a preceding reverse row \(k>i\).
Their clocks and all \(W_3\) values agree: the reverse
quadratic defect does, and so do the true \(A^\vee,C\)
moves generating \(W_2,W_3\). The normalized signed
difference
\[
                 z=e_i/b_i-e_k/b_k
\]
therefore lies in \(E_5\). Its model is zero by the exact
anchored five-moment argument in the
[late-cutoff proof](ERK10-SINGLE-INVISIBLE-GHOST-LATE-CUTOFF.md):
all five numerical \(bC^j\) reads vanish at equal clocks,
the origin component is zero, and the \(X\)-Gram is
nonsingular. Thus \(z\) is pure grade five.
It cannot be in \(F_4\): its live restriction is a
single-clock vector, and we just proved the only such
line in \(W_3\) is \(Kr\); but \(z_3=0\) and \(r_3\ne0\).

It follows that the old \(F_4\) is both \(A,C\)-invariant
after restriction to the physical prefix through \(i-1\),
since \(F_5=F_4+Kz\). The same partial inverse and
nilpotence proof as in the late-cutoff theorem puts each
nonzero clock indicator there in the restricted pure
space. Its live rank is at most three, so there are at
most three distinct nonzero live clocks in that prefix.
It includes \(t\) already at physical 3.

For \(i=12\), the original suffix clocks are only \(t\)
and \(1\), since row 12 duplicates row 13 or 14. There
are at most five total possible scalar sites, contrary
to the anchored ordinary quadrature support floor.
For \(i=11\), the suffix clocks are at most \(c_{12},t,1\).
Thus six scalar sites can occur only if there are exactly
three nonzero live prefix clocks and \(c_{12}\) and 1
are both new and distinct. In that case the live prefix
pure space is exactly the span of the three distinct
nonzero clock indicators. Its vector \(r\) is supported
only at \(t\) and nonzero at physical 3, so **every**
live prefix stage with clock \(t\) is \(r\)-active.
The suffix stage 13 is active too, and any duplicated
row 11 at clock \(t\) must be a duplicate of row 13
since both other suffix labels are new; it therefore
has the same actual reverse quadratic defect and is
itself active. Thus the uniform \(r\)-group is the whole
ordinary live clock-\(t\) group and its total weight
vanishes. This leaves at most five effective sites,
again impossible. Both duplicate possibilities have
been excluded without calling the reduced reverse an
order-ten tableau or deleting one of its own rows.

The same exclusion holds for \(i=10\), with an additional
ordinary moment count. A duplicate still makes \(z\in F_5
\setminus F_4\), so the live prefix through physical 9 has
\(k\le3\) distinct nonzero numerical labels including \(t\),
and its pure space contains all their indicators. At any
nonzero prefix label \(a\ne t\), writing its indicator in
the actual projected \(F_4=\langle r,s,Cs\rangle\) proves
that \(s\) is constant and nonzero on **every** prefix
live row at \(a\), since \(r=0\) on that clock.

If \(k=3\), write the other labels \(x,y\). The prefix
indicators saturate the projected dimension, so \(s\) is
zero on the prefix zero-clock rows. By strictness \(s_{13}=s_{14}=0\),
and by the putative duplicate \(s_{10}\) agrees with one of
the four later rows. Thus the whole support of \(s\) has
at most the five numerical labels \(t,x,y,c_{11},c_{12}\).
Its six paid \(b C^a s=0\) moments force zero pooled \(bs\)
at each one. Every \(x,y\) outside \(\{1,c_{11},c_{12}\}\)
has no suffix occurrence and constant nonzero \(s\), hence
has zero pooled ordinary weight. The ordinary quadrature
is therefore supported on at most \(\{0,1,t,c_{11},c_{12}\}\),
too few. If \(k=2\), the maximum of six possible ordinary
sites requires all of \(0,t,x,1,c_{11},c_{12}\) distinct for
the other prefix label \(x\). Allowing zero-clock \(s\) on
the prefix, its support is still within the five labels
\(\{0,t,x,c_{11},c_{12}\}\). The same six pure moments force
zero ordinary mass at \(x\), since it is a nonzero constant
\(s\)-label absent from the suffix. If \(k\le1\), the potential
ordinary support is at most five initially. This completes
the exclusion of a literal duplicate at physical 10.

## 3. Literal reverse low-degree contact and true old taps

Physical 13 is the first carrier in reduced reverse.
If physical 12 were also a carrier, its equal nonzero
reverse amplitude and equal clock would force its tap on
physical 13 to vanish by its actual quadratic equation
(the only other preceding reverse clock is zero).
It would then literally duplicate row 13. Thus \(r_{12}=0\).
Its reflected clock is nonzero: a zero clock there and
zero \(u\) would force both preceding entries zero, a
duplicate of the reverse origin. Its response \(s_{12}\ne0\)
then follows from the same quadratic equation.

To verify the next row, scale this **local reverse** matrix
and clocks by the inverse of the nonzero reverse carrier
clock \(1-t\). Let \(\tau\ne0\) be the rescaled clock
at the first noncarrier (physical 12). The normalized
carrier indicator \(v\) has \(d^\vee=-v/2\) and its response
\(R=A^\vee v\) is pure grade three. The true cubic error
in the rank-two flag is
\(-v/3+(1-2\tau/3)R\), by calibration at the first carrier
and first noncarrier. At the fourth reversed row
(physical 11), if it were a carrier, its reads \(a,b\)
on the two preceding nonorigin sites would satisfy the
actual equations
\(a+\tau b=0,\ 2\tau a+3\tau^2 b=0\).
Thus \(a=b=0\), giving a literal duplicate of the first
carrier. So \(r_{11}=0\). At its actual rescaled clock
\(x\), the same quadratic and cubic primitives solve
\[
 a=x^2(3\tau-2x)/(2\tau),\qquad
 b=x^2(x-\tau)/\tau^2.
\]
The clocks \(x=0,\tau\) give literal duplicate incoming
lists of the reverse origin and first noncarrier, so
\(x\ne0,\tau\), and \(b\ne0\).
The genuine pure \(A^\vee R\) belongs to the span of
\(v,R,CR\) by the rank-three reverse flag. At the first
carrier and first response its shape is therefore
\(\lambda(C-\tau)R\), using here the rescaled reverse clock
diagonal. At the fourth reversed row its \(bR_{\mathrm{first}}\)
term is nonzero, forcing \(R\) there to be nonzero too.
This is the actual second nonzero response; all local
claims are paid by grades at most four.

Returning to old coordinates gives \(s_{11},s_{12}\ne0\).
The only later old \(r\)-active row for either is physical 13,
so the actual weighted transpose formula \(b_i s_i=b_{13}A_{13,i}r_{13}\)
gives \(A_{13,11},A_{13,12}\ne0\).
Also the actual local \(b\ne0\) above is
\(A^\vee_{11,12}\ne0\), hence \(A_{12,11}\ne0\).
Finally the independent weighted shift-one floor gives
\(A_{14,13}\ne0\).

## 4. The actual fifth contact, including a carrier there

Continue in the same local rescaled reverse coordinates, with
first noncarrier clock \(\tau\) and fourth reversed clock \(x\).
The genuine rank-three flag fixes \(A^\vee R=\gamma(C-\tau)R\)
with \(\gamma=\tau/(3\tau-2x)\); its denominator is nonzero
because the fourth-row response is nonzero. Write \(y\) for
the fifth reversed clock (physical 10) and \(a_{54}\) for
its local tap on the fourth row (physical 11).

The true quartic test for \(Q(X)=X^2(X-y)(2X-3\tau)\)
is the [paid fifth-head contact](ERK10-FIFTH-HEAD-CONTACT.md)
before any use of grade-five flatness. To spell out the
carrier safeguard here, use \(w=-R/2\). The genuine
\(A^\vee Q'(c)-Q(c)\) has form
\[
 -Q(1)v+\big[-2Q'(1)+4\tau\gamma(C-\tau)
                         +4\tau(y-C)\big]w
\]
by evaluating at reversed rows 2,3,4. At reversed row 5,
\(Q(y)=0\); if it is a carrier, \(y=1\) and \(Q(1)=0\)
as well. Subtract \(4\tau A^\vee w\) there. The row-2
term is \(Q'(1)a_{52}\), exactly the \(-2Q'(1)w_5\)
term on the other side; the row-3 term vanishes because
\(Q'(\tau)=4\tau w_3\). The remaining scalar equation is
\[
                     6a_{54}x(x-\tau)(x-y)=0 .
\]
Here \(x\ne0,\tau\) was already proved.

If \(a_{54}=0\), an actual carrier at row 5 has \(y=1\)
and both quadratic and cubic right sides vanish after
the carrier correction; its only two nonorigin entries
are zero, a literal duplicate of the first carrier.
If instead it is noncarrier, the two primitives solve
\[
 a_{52}=y^2(3\tau-2y)/(2\tau),\qquad
 a_{53}=y^2(y-\tau)/\tau^2 .
\]
The same calibrated \(A^\vee R\) equation then gives
\(y^2(y-\tau)(y-x)=0\). At \(y=0,\tau,x\) the two solved
entries and row sum make a literal duplicate of the origin,
first noncarrier, or second noncarrier, respectively (the
missing tap is zero). All were just excluded in §2.
Therefore \(a_{54}\ne0\) and \(y=x=p\).

The exact doubling also holds if this fifth row is a
carrier. Write \(\epsilon\in\{0,1\}\) for that indicator,
so \(\epsilon=1\) implies \(p=1\). Put \(a=a_{54}\),
\(\Delta R=R_5-R_4\), \(\Delta b=a_{53}-a_{43}\).
The differences in the genuine quadratic and cubic equations
give
\[
 \tau^2\Delta b=p(2\tau-3p)a+\epsilon(\tau-1),\qquad
 \tau\Delta R=3p(p-\tau)a+\epsilon(1-3\tau/2).
\]
The calibrated unary relation at the same two rows gives
\(\tau^2\Delta b+2R_4a=2\gamma(p-\tau)\Delta R\),
with \(2R_4=p^2(3\tau-2p)/\tau\).
After clearing the already guarded factors it is exactly
\[
        4a p^2(p-\tau)(p-2\tau)+\epsilon\tau^2(p-1)=0 .
\]
The second term vanishes in both cases, and \(a,p,p-\tau\)
are all nonzero. Therefore \(p=2\tau\).
Undoing the common reverse scaling gives
\(1-c_{10}=1-c_{11}=2(1-c_{12})\). Because both original
weights are live, the nonzero strict reverse tap
\(A^\vee_{10,11}\) is exactly the nonvanishing of \(A_{11,10}\).
This uses no masked grade-five primitive and no full order
claim for the reduced reverse.

[ERK10SingleGhostDependentThirteenGate.lean](../lean/RKCert/ReviewedNative/ERK10SingleGhostDependentThirteenGate.lean)
checks the affine support, carrier duplicate linear taps,
first two noncarrier coefficient calculations, the repeated-head
scalar algebra with or without a carrier, and conversion
of a genuine reverse response into a nonzero old tap.
The pure-rank and ordinary support arguments are mathematical
and reuse the existing exact ghost frontier.
