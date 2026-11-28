# No simultaneous affine-pivot loss in the live cubic DIRK11/13 chart

**Result.** In the true normalized invisible-six live cubic
DIRK11/13 chart with \(\alpha=0,\ \tau\ne0,\ \deg U=3\),
the surviving affine equation for the middle profile coefficient
has nonzero leader at the actual profile. This rules out the
entire simultaneous affine-pivot-loss branch, whose exact
ordinary fifth-clock projections have degrees \(36,28,60,60\).
The unrestricted real interval remains **13–14**.

Use exactly the genuine signed ranks, chronology and field
hypotheses of the [live fourth-clean](../dirk11-thirteen-invisible-six-cubic-live-fourth/README.md)
and [only-\(F_3\)](../dirk11-thirteen-invisible-six-cubic-live-f3/README.md)
packets. Here \(m(Y)=Y^2+rY+s\), \(rs\ne0\), the fourth ordinary
reverse diagonal is zero, \(V,B\) are the fourth/fifth ordinary
reverse clocks, \(R_3(Y)=Y^3+c_2Y^2+c_1Y+c_0\) is the old regular
triple, and \(F_3(s)=0\) is necessary. All three old roots and
\(V\) are distinct and nonzero. The reciprocal carrier is live
at all ordinary nonterminal clocks and all ghosts. The proof
uses characteristic zero once the normalized ranks hold, with
no positivity or coefficient field ordering.

## 1. Exact projection of both lost coefficients

Let \(\mathcal A(r,s)\) be the linear remainder of the fourth
clean condition by the affinity quadratic \(\mathcal D(r,s)\).
The required equation is \(\mathcal A(r,s)=0\).
Multiply its coefficients by \(120c_0\), which is live since
the three old roots are nonzero, to get
\[
 120c_0\mathcal A(r,s)=A_1(s)r+A_0(s).
\]
A lost affine pivot \(A_1(s)=0\) requires \(A_0(s)=0\)
as well. The source expands both polynomials exactly.
Their resultant in \(s\) has the factors \(c_0^5,V\),
and four further polynomials in the old coefficients
and \(V\). One has degree zero in \(V\), one has degree
one, and two have degree three in \(V\). The live
\(c_0,V\) factors are the only ones discarded at this
step.

At the actual old clock set,
\[
 T_4(Y)=\frac{J_5(Y)J_4(B)-J_5(B)J_4(Y)}{Y-B}
\]
is the ordinary quartic hull up to its leader
\(D=132J_4(B)\ne0\). Its synthetic deflation at \(V\)
gives \(R_3\), with exact coefficient numerators
\(C_2=t_3+VD,\ C_1=t_2+VC_2,\ C_0=t_1+VC_1\).
In each of the four factors substitute \(c_j=C_j/D\),
clear \(D\), and pseudo-reduce modulo the true \(T_4(V)\).
The source removes the exact primitive contents
\(J_4(B)^3,J_4(B),J_4(B)^5,J_4(B)^6\), respectively,
up to nonzero rational scalars. Taking the resultant
against \(T_4\) gives respectively a live \(J_4(B)\)
factor of multiplicity \(6,2,4,4\), and one
remaining irreducible factor of degree \(36,28,60,60\).
All these denominator and content identities are checked
exactly. No other ordinary fiber is dropped; an overlap
between cases would satisfy every case for whose old guard
factor vanishes.

For each of the four actual old-factor choices the corresponding
degree-\(d\) monic clock algebra is tested modulo 101. The linear
cofactor of \(T_4\) and its accompanying projected degree-at-most-three equation has a
unit leader and hence reconstructs \(V\). In that clock algebra
\(A_1\), as a polynomial in \(s\), has leader \(-32V\), a unit
in the residue algebra. Normalize \(A_1\) to monic and reduce
\(A_0\) modulo it. The quadratic-or-cubic lower equation is
padded to degree three for a linear cofactor against \(A_1\).
Its linear leader is again a unit, uniquely determining \(s\).
This cofactor is a genuine necessary relation even at a degree
drop: take all shifted rows up through the indicated bounds and
form the cofactor combination of the coefficients above linear.
No rank conclusion is drawn from the leading assumptions beyond
the tested unit. The same construction also gives uniqueness
after extension of the actual characteristic-zero field.

The degree-36 case is already impossible: \(F_3(s)\) is
a unit in that full clock algebra modulo 101.

## 2. Exactly distinguish the two degree-60 cases

The two old degree-three guard polynomials from Section 1 are
distinguished by exact products, not by a coincident residue
root. The one giving the **contact** clock case is a factor
of \(\operatorname{Res}_s(F_2,A_1)\); the one giving the
**slope** clock case is a factor of \(\operatorname{Res}_s(F_1,A_1)\).
The source checks these two exact factorizations by matching the
factors of the simultaneous-pivot resultant. The normalized
cofactor argument above uniquely determines \(s\) in each
actual case. To prove that it is an \(F_i\) root, first pass
to a splitting field. The exact appropriate resultant and
the live fixed leading coefficient of \(F_i\) give a common
root \(s_*\) of \(F_i,A_1\). The constant of \(F_i\) is
nonzero because \(c_0\ne0\), so \(s_*\ne0\).
At any such \(F_i\) root, the exact identities in the
only-\(F_3\) packet give \(\mathcal A(r_*,s_*)=0\) and
\(\mathcal D(r_*,s_*)=0\), with
\[
 r_*=
 \begin{cases}
 c_2-c_0/s_* & (F_2),\\
 \tfrac{15}{16}(c_2-c_0/s_*) & (F_1).
 \end{cases}
\]
Since \(A_1(s_*)=0\), also \(A_0(s_*)=0\). Uniqueness
of the unit cofactor for \(s\) implies \(s=s_*\).
In particular no modular vanishing is interpreted as
either exact \(F_i(s)=0\).

The contact \(r_*\) is inadmissible because it makes
\(m\) vanish at old roots. The slope \(r_*\) is either
zero, already excluded, or imposes the already excluded
actual affine slope \(-1\), by the genuine old affinity
coefficients. Therefore an actual \(r\) must be the other
root of the true affinity quadratic:
\[
  r=\frac{s(2s+c_1)}{c_0}-r_*.
\]
This uses only the live \(c_0,s\), no discriminant or
difference of the two roots. In a genuinely repeated
quadratic the forbidden root is the only root and there
is no candidate. For the distinct degree-28 clock case
we recover neither root separately: adjoining the monic
\(\mathcal D(r,s)/c_0\) retains both, even at a repeat,
making rank 56. Each degree-60 case keeps rank 60.

## 3. Actual prefix and paired-crossing gates on fixed clocks

Reconstruct the carrier from the old cubic inverse
of \(k=Ym\), \(q=IP(V)/\ell(V)\), and the reciprocal
sample \(h(V)/q\), exactly as in the previous packets.
Every old inverse is checked in the full old degree-three
auxiliary quotient, not at one root. The other divisions
use \(q,\ell(V),R_3(V)\), the cubic carrier leader, and later
\(P_0(V)=V R_3(V)\) to adjust the quartics. Those are live at an actual
nonmonomial chart; they are independently unit-tested
throughout each algebra before forming the next quotient.

For \(\gamma=5\), the true \(A(C\phi)=0\) cut on five
initial ghosts gives the determinant of
\(I(XU),X I(XU),S_6\) modulo \(U\) equal to zero.
The fixed-clock replay verifies that it is a unit in
rank 56 or 60, respectively.

For \(\gamma=3,4\), fit the genuine \(G/b,YG/b\) on the
four clean rows with the earlier corrected quartics.
The paired commutator gives zero second ghost diagonal;
the two actual ghost clocks \(z,w\) therefore obey
\(r_1^*(Y)-z r_0^*(Y)=0\). The cubic in \(z\) has a unit
leader in the rank-56 or rank-60 base. Adjoin it as a
monic cubic; the quadratic leader for the other root
\(w\) is also a unit in rank 168 or 180. The independent
quintic weighted primitive gives the crossing
\(Q_{\rm eff}(w)U_{\rm rev}(z)-Q_{\rm eff}(z)U_{\rm rev}(w)=0\).
The replay shows that this is a unit in the full
rank-168 or rank-180 algebra. In particular no division
by a first or second ghost clock or by its diagonal is
implicit in these gates.

Run `python3 replay.py` with SymPy. The optional
`--project`, `--arithmetic`, `--old-pair`,
and `--old-mark` arguments override sibling paths.
The proof uses residue units solely to lift multiplication
inverses in monic clock algebras over \(\mathbb Z_{(101)}\).
No tableau coefficient or unknown ghost is assumed integral.
The native scalar checks for the genuine gap gates are in the
earlier fourth-clean and zero-two packets; the companion
cofactor audit here confirms the undivided uniqueness and
other-root use.

This argument does **not** invert the cubic leader of \(F_3\):
it includes any intersection with the already excluded
leading-degree-drop slice. It only closes the actual
simultaneous \(A_0=A_1=0\) slice; it does not exclude all
clock fibers where the \(F_3\) discriminant vanishes,
or fibers where some other projected profile has a
vanishing pivot. The remaining proof path stays separate.
