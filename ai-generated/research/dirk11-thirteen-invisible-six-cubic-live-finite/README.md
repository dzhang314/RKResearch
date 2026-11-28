# The live cubic no-opening-ghost chart has only finitely many ordinary clock profiles

**Result.** In the true normalized invisible-six DIRK11/13
chart with \(\deg U=3,\ \alpha=0,\ \tau\ne0\), the ordinary
nonendpoint clock profiles and the shapes of the cubic
carrier belong to a finite algebraic set. This includes all
remaining forward initial counts \(\gamma=3,4,5\), with
no nonvanishing condition imposed on the actual projected
pivots. It does not eliminate the finite set, certify any
realized tableau, or constrain all ghost clocks to be finite.
The unrestricted real DIRK11 interval remains **13–14**.

Use exactly the genuine rooted-order and signed normalization
of the [live fourth-clean](../dirk11-thirteen-invisible-six-cubic-live-fourth/README.md)
and [only-\(F_3\)](../dirk11-thirteen-invisible-six-cubic-live-f3/README.md)
proofs. In particular the fourth ordinary reverse diagonal
is zero, \(m=Y^2+rY+s\) with \(rs\ne0\), \(F_3(s)=0\),
and the reduced affine equation \(\mathcal A(r,s)=0\)
holds. As before \(V=1-a,B=1-b\) are the fourth and fifth
ordinary reverse clocks, \(R_3\) is the monic old triple
hull, \(P=Ym\), \(P_0=Y R_3\), \(P_1=Y(Ym\bmod R_3)\),
\(I\) is the zero-constant primitive, and \(h=YJ_4\).
There are five ordinary nonendpoint clean clocks. The true
grade and live profile arguments apply in any coefficient
field of characteristic zero.

## 1. Define the generic clock norms without large expansion

Treat \(B\) as an indeterminate. Begin over \(\mathbb Q(B)\)
with the reflected monic Jacobi pencil determined by
\(\lambda=-J_5(B)/J_4(B)\). Divide it by \(Y-B\) to get
the monic quartic; adjoin \(V\) by this quartic and deflate
again to get \(R_3\). In that rank-four algebra, invert the
cubic leading coefficient of \(F_3\), then adjoin \(s\)
by the resulting monic cubic. This makes rank 12 over
\(\mathbb Q(B)\). In it, invert the coefficient of \(r\)
in \(c_0\mathcal A(r,s)\) and use the linear equation
to find \(r\). The factor \(c_0\) is genuinely live for
any actual profile; its introduction avoids a symbolic
rational denominator in \(\mathcal A\)'s coefficients.

Use the old monic cubic as an auxiliary quotient to
invert \(k=Ym\) and compute the representatives of
\(\ell=IP/k\bmod R_3\) and \(h/k\bmod R_3\).
Set \(q=IP(V)/\ell(V)\). The reverse cubic carrier
\(U_{\rm rev}\), up to its freely chosen common scale,
is
\[
 U_{\rm rev}(Y)=u(Y)+
     R_3(Y)\frac{h(V)/q-u(V)}{R_3(V)},\qquad
 u=h/k\bmod R_3 .
\]
A true carrier is obtained this way because the reciprocal
profile specifies it at four distinct clean clocks.
The values needed to divide by \(q,R_3(V),\ell(V)\)
and the old inverse of \(k\) are among the guards.
The auxiliary cubic splits at the three actual old
roots; no fixed ordering of them is chosen.

There are two branches of the same arithmetic:

* **Five initial forward ghosts.** Put \(U(X)\propto
  U_{\rm rev}(1-X)\), and normalize \(U\) by its cubic
  leader to form a quotient. In that cubic, take the
  determinant of the coefficient columns of
  \(I(XU),X I(XU),S_6\), where \(S_6\) is the forward
  hull of the six nonterminal clean clocks. The
  [actual five-zero cut](../dirk11-thirteen-invisible-six-cubic-live-monomial/README.md)
  and \(R_6\propto S_6\bmod U\) force this determinant to
  vanish, independently of the last ghost clock. This
  test is an element of the rank-12 base.
* **Two or three reverse-gap ghosts.** Correct \(P,P_1\)
  by multiples of \(P_0\) to match \(q,Vq\) at \(V\).
  The adjusted quartics \(P_j^*\) already match
  \(G/b,YG/b\) on the old triple and the required zero at
  the true terminal. Compute \(r_j^*=IP_j^*/k\bmod R_3\).
  The paired genuine commutators in the live fourth-clean
  proof force the second gap ghost diagonal to vanish,
  even if the first diagonal vanishes too. Thus the
  two distinct ghost clocks \(z,w\) are roots of
  \(r_1^*(Y)-z r_0^*(Y)\). Invert the cubic leader in
  \(r_1^*(z)-z r_0^*(z)\), and adjoin \(z\) by the
  resulting monic cubic. In this rank-36 algebra, invert
  the quadratic leader in the two-root polynomial
  to reconstruct \(w\) by the sum of its roots.
  From the true quintic primitive of \((Y-V)P_0\),
  the effective clean cubic \(Q_{\rm eff}\) is fitted
  through the four ordinary rows using \(IP_5/k\).
  The independent ghost crossing
  \(Q_{\rm eff}(w)U_{\rm rev}(z)-Q_{\rm eff}(z)U_{\rm rev}(w)\)
  must be zero. This is the rank-36 test.

These define a finite list of rational functions of \(B\).
For every scalar inversion, record its multiplication
determinant in its current monic algebra, taking the
successive norms back to \(\mathbb Q(B)\) for a nested
auxiliary quotient. Record also the norms of both final
tests. Include the rational expressions' denominators.
A guard function may vanish for some exact \(B\) even
if the chosen actual pivot is live; those values are
retained in the finite cover rather than discarded.

## 2. One exact specialization proves all these functions nonzero

The replay constructs those same monic algebras at
\(B=2\bmod101\). It checks every needed inverse by
multiplying it back to one in the whole residue
algebra. Both final tests are units there, in ranks
12 and 36, respectively. This does **not** claim that
\(B=2\) or its reduction occurs in a tableau.

To justify the generic construction, start the algebra
over the localization of \(\mathbb Z_{(101)}[B]\) at
\((101,B-2)\), before any monic adjunction. Each guard
determinant just checked is nonzero in the residue
field, hence a unit of the localized ring, so its
multiplication adjugate gives the inverse that the
next monic step needs. The same argument proves both
final norm functions nonzero in \(\mathbb Q(B)\).
No normal form or factorial formalism for an unknown
tableau is reduced modulo 101.

Now take any real or other characteristic-zero
profile in the chart. If its \(B\) is not a zero or pole
of the listed nonzero rational functions, each generic
guard specializes to a genuine unit in the relevant
clock algebra. The actual \(V,s\) (and \(z\) in the
multi-gap case) give evaluation maps from the prescribed
monic adjunctions. The actual order and chronology make
one of the two final tests vanish in the actual field,
but that test's norm was nonzero at this \(B\), so its
multiplication operator is a unit. This is impossible.
Thus actual \(B\) is in the finite zero/pole cover,
**including any leading-degree and simultaneous pivot
losses**. A nonzero rational function over \(\mathbb Q\)
has only finitely many zeros and poles, all algebraic.
For any fixed such \(B\) there are only the four choices
from the Jacobi quartic for \(V\) and the finite old
clock permutations. The only-\(F_3\) proof supplies at
most six \(r,s\) shapes at fixed ordinary clocks,
including the exceptional fiber when a pivot vanishes.
Finally the genuine \(q=IP(V)/\ell(V)\) and reciprocal
interpolation determine the carrier shape in all
actual cases. This proves the stated finiteness.

Run `python3 replay.py` with SymPy. It imports sibling
project and arithmetic sources by default; the optional
overrides are `--project`, `--arithmetic`,
`--old-pair` and `--old-mark`. No giant
univariate norm expansion is an input: the ordered
monic-algebra and multiplication-determinant definitions
above name the exact finite cover. The companion Lean
lemma checks the finite union of polynomial root sets.
The paid chronology and residue-to-generic transfer are
given exactly in the source proof, not as a single
end-to-end Lean order theorem.
