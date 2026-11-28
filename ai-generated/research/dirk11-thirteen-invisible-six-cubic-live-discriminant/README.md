# No repeated \(F_3\) fiber at the actual ordinary clocks of live cubic DIRK11/13

**Result.** In the true normalized invisible-six live cubic
DIRK11/13 chart with \(\alpha=0,\tau\ne0,\deg U=3\), the
surviving ordinary clock pair cannot make the cubic \(F_3\)
have a repeated root. This excludes both entire degree-28
and degree-72 clock fibers, **including the simple profile
root when the other two roots coincide**. The unrestricted
real DIRK11 interval remains **13–14**.

Use the actual rooted tableau support, chronology and signed ranks
of the [fourth-clean](../dirk11-thirteen-invisible-six-cubic-live-fourth/README.md),
[only-\(F_3\)](../dirk11-thirteen-invisible-six-cubic-live-f3/README.md),
and [affine-pivot](../dirk11-thirteen-invisible-six-cubic-live-affine-pivot/README.md)
packets. Thus \(A_{aa}=0\), \(m=Y^2+rY+s\),
\(rs\ne0\), \(F_3(s)=0\), and the actual affine \(r\) pivot is live.
Write \(V,B\) for the fourth and fifth regular reverse clocks
and \(R_3=Y^3+c_2Y^2+c_1Y+c_0\) for the old ordinary cubic.
The three old roots and \(V\) are nonzero, so \(c_0,V\ne0\).
By the separate [leading-drop proof](../dirk11-thirteen-invisible-six-cubic-live-f3-degree-drop/README.md)
the cubic leader \(2V(4V+c_2)\) of \(F_3\) also cannot vanish.
These are conditions on the actual ordinary clock pair; no
assumption is made about other pairs in its algebraic fiber.

## 1. Exact clock projections

The discriminant of \(F_3\) in \(s\) factors, up to a nonzero
rational scalar, as
\[
 H_{28}(V,c_0,c_1,c_2)^2 H_{72}(V,c_0,c_1,c_2),
 \qquad H_{28}=2Vc_0-Vc_1c_2+c_0c_2.
\]
The second factor has degree six in \(V\) and is generated
exactly by the replay. Both are treated as actual cases, even
at an intersection. Substitute the \(T_4\) and \(R_3\) ordinary
Jacobi deflation coefficients as in the affine-pivot proof.
The live leader is \(D=132J_4(B)\). In the two cubic-or-lower
projected equations the removed contents are exactly
\(J_4(B),J_4(B)^9\) up to rational scalar. Their resultants
against the ordinary quartic \(T_4\) are, up to nonzero rational
scalar, \(J_4(B)^2\) times an irreducible degree-28 factor,
and \(J_4(B)\) times an irreducible degree-72 factor.
The Jacobi denominator is already live. Nothing else is
removed by clearing bases or by primitive normalization.
The finite-free replay shows that the leading linear cofactor
pivot reconstructing \(V\) from \(T_4\) and either projected
equation is a unit throughout both clock algebras at 101.

## 2. Retain every actual profile root

On the first guard \(H_{28}=0\), necessarily \(c_2\ne0\):
otherwise the equation gives \(2Vc_0=0\), impossible.
Thus \(c_1=c_0(2V+c_2)/(Vc_2)\). Exact substitution gives
\[
 F_3(s)=\frac{V(c_0+c_2s)^2}{c_2^2}
          \bigl(-3Vc_2^2+(8V+2c_2)s\bigr).
\]
At the repeated root \(s=-c_0/c_2\), both coefficients of
\(120c_0\mathcal A(r,s)\) vanish *identically*, an exact
substitution checked by the source. The already proved
affine-pivot closure therefore excludes this root.
The alternative slot
\[
 s=3Vc_2^2/(8V+2c_2)
\]
is directly retained in the replay. The denominator is
live on the prior non-leading-drop chart and a unit at
the chosen residue prime. If the two slots coincide,
the first proof already excludes that candidate; no
difference of profiles is inverted.

On the second guard \(H_{72}=0\), the actual cubic has
a common root with its derivative, possibly after field
extension. The leading linear cofactor of \(F_3,F_3'\)
is a unit over the whole degree-72 clock algebra modulo
101, so there is a unique common root \(s_*\) where a
repeated root can occur. The actual \(s\) must equal
\(s_*\) or the remaining root
\[
 -[Y_s^2]F_3/[Y_s^3]F_3-2s_*,
\]
where \(Y_s\) is the polynomial indeterminate for the
constant-profile coordinate \(s\). Both exact slots
are replayed. No assumption of a separation between
them is taken from a residue. This is a cubic deflation
argument with the verified unit leader, not a finite
list of guessed simple roots.

In each retained slot the genuine affine equation reconstructs
\(r=-A_0(s)/A_1(s)\); again its denominator is unit-tested
in the entire corresponding fixed-clock algebra, not inferred
from numerical nonvanishing at a single point.

## 3. True paid exclusions on all three retained slots

The replay reconstructs the genuine clean carrier and performs
the fixed-clock tests of the affine-pivot packet: lower degree
old interpolation with live \(k=Ym\), reciprocal sample at
\(V\), the forward five-prefix determinant in the cubic carrier
quotient, and, after the paired commutator forcing a zero
second ghost diagonal, the independent quintic crossing.
The five-prefix determinants are units in the degree-28
or degree-72 clock algebras. The whole degree-three first
ghost adjunction and the second-root pivot are verified;
the crossing is a unit in rank 84, 216, and 216,
respectively. There is no division by an unknown ghost
clock or diagonal. Both \(\gamma=3,4\) with at least two
gap ghosts and \(\gamma=5\) are therefore excluded.

Run `python3 replay.py` with SymPy; it accepts the same
sibling arithmetic overrides as the affine-pivot packet.
Only monic clock algebras are reduced modulo 101. Norm
inverses and all leaders used are checked by residue
multiplication, so lift by the adjugate over
\(\mathbb Z_{(101)}\). The actual characteristic-zero
tableau is not assumed integral at that prime.
This is a specialization of the already reviewed Lean
cofactor and genuine gap scalar gates; the clock
elimination is exact source arithmetic.

Consequently at any candidate the \(F_3\) cubic is squarefree
at the *actual* \(B,V\). This does not show that every other
\(V\) in a clock norm algebra is regular, and does not remove
those algebraic fibers by a generic denominator argument.
