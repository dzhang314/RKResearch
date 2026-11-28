# Two mixed early-profile contacts excluded for a quadratic carrier

**Results.** In the characteristic-zero normalized no-late
invisible-six DIRK11/13 chart, suppose \(U\) is quadratic and
\(\alpha\ge1\). In the nonmonomial old fit
\(m=Y^2+rY+s\), neither \(r=0\) nor \(c_2s=c_0\) is possible.
This is not an unrestricted DIRK stage lower bound.

Use the complete actual rooted hypotheses and chronology of the
[early profile census](../dirk11-thirteen-invisible-six-early-profile-census/README.md)
and the retained hull and adjoint-commutator gates of the
[monomial quadratic proof](../dirk11-thirteen-invisible-six-quadratic-monomial-early/README.md).
In particular \(\tau\ne0\), \(s\ne0\) in a nonmonomial fit,
and the literal first reverse ghost \(z\) has \(l(z)=w_0(z)=0\)
and diagonal zero. For \(\alpha=2\), \(w_0\) is quadratic
with a second distinct actual root \(w\). We impose no
numerical disjointness of any ghost and ordinary site.

If \(r=0\), the exact mixed old gate gives
\(s=c_0/c_2\) and \(6c_0=5c_1c_2\), with \(c_2\ne0\).
This forces \(l_1=-1\), so \(\alpha=2\) is ruled out by the
actual second-diagonal debit of the early-ghost proof.
For \(r\ne0,\ c_2s=c_0\), the old gate instead recovers
\[
 s=c_0/c_2,\qquad r=(2c_0+c_1c_2)/c_2^2,\qquad
 12c_0^2+8c_0c_1c_2-6c_0c_2^3+c_1^2c_2^2=0.
\]
Here again \(c_2\ne0\).

Let \(a,b\) denote the second and first regular forward sites.
Use the ordinary Jacobi quintic with
\(\lambda=-J_5(a)/J_4(a)\), deflate first at \(a\), then
at \(b\) and reflect the old cubic \(R\). Clearing \(D=132J_4(a)\)
in the displayed old coefficient equations gives one polynomial
in \(a,b\) each. For the nonzero-\(r\) contact take the
pseudo-remainder in \(b\) by the old ordinary quartic first:
its scalar polynomial content is exactly a nonzero rational
multiple of \(J_4(a)^3\). The result is cubic in \(b\).
The corresponding exact resultants in \(b\) are:

| contact | \(J_4(a)\) exponent | remaining irreducible degree |
|---|---:|---:|
| \(r=0\) | 5 | 24 |
| \(r\ne0,\ c_2s=c_0\) | 7 | 48 |

The Jacobi quartic factors are not actual clocks. In each
remaining monic field compute the literal \(b\) from the
necessary linear cofactor, whose denominator is tested as
a unit in the full residue algebra at 101. The program
verifies the old coefficients and reconstructs the
quadratic carrier \(U(1-Y)=J_4(Y)/m\bmod R\), up to common
scale. This equality holds because of the reciprocal
clean head, and enough old samples to determine a quadratic.
It then reconstructs \(z=-l_0/l_1\) using the actual first
reverse mark. In the two-ghost chart it recovers
\(w=-[Y]w_0/[Y^2]w_0-z\), admitting numerical contacts.

In \(\alpha=1\), the already excluded zero five-hull
multiplier cannot occur. The exact divided hull relation
requires the two-coordinate determinant of
\((X-(1-z))(F_b-r_bH)\bmod U\) and \(S_6\bmod U\) to vanish.
Here \(r_b=F_b(b)/H(b)\) is the forward head multiplier,
not the printed coefficient of \(Y\) in \(m\).
The determinant is a **unit** in each entire degree-24
and degree-48 clock algebra at 101. For \(\alpha=2\)
only the nonzero-\(r\) contact remains and the true
commutator instead forces
\[
 d_a^2 \{R(z)U(1-w)-R(w)U(1-z)\}=0 .
\]
It is a **unit** throughout that same degree-48 algebra.
The exact ingress pays the grade and order of those two
signals in the preceding monomial quadratic proof; their
proofs use neither a specific value of \(z\) nor a relative
ordering of the numerical ghost clocks.

Run **python3 replay.py** with SymPy; **--research PATH**
supplies the sibling arithmetic sources in an isolated layout.
All units lift only in the exact finite-free clock algebras,
not by reducing an unknown tableau. The relevant scalar
crossings and tap rules are in the native
**DIRKOrderElevenInvisibleSixEarlyGhost** module.
