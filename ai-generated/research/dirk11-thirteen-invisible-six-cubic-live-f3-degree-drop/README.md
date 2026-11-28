# No leading-degree drop on the surviving live cubic \(F_3\) probe

In the normalized invisible-six live cubic, no-late-ghost
DIRK11/13 chart of the [fourth-clean](../dirk11-thirteen-invisible-six-cubic-live-fourth/README.md)
and [only-\(F_3\)](../dirk11-thirteen-invisible-six-cubic-live-f3/README.md)
packets, the actual profile cannot lie on the vanishing
\(F_3\) cubic leader. This is an extra subchart exclusion,
not an unrestricted stage result; the real interval is **13–14**.

Use the genuine order, support, and rank hypotheses of those
packets and the first-stage ordinary chronology \(\alpha=0\).
The surviving profile satisfies \(m=Y^2+rY+s\), \(rs\ne0\),
and \(F_3(s)=0\); the fourth ordinary reverse diagonal is
already zero. The coefficient of \(s^3\) in \(F_3\) is
\(2V(4V+c_2)\), with \(V\ne0\).
Suppose \(4V+c_2=0\). Deflate the true reflected ordinary
Jacobi pencil at \(B\), producing a degree-four hull
with leader \(D=132J_4(B)\ne0\) and cubic coefficient \(t_3\).
Deflation at \(V\) says \(D c_2=t_3+D V\).
Hence \(V=-t_3/(5D)\) exactly, without a clock division.
The resultant of the quartic with \(5D V+t_3\)
has primitive factors \(J_4(B)\) and a degree-sixteen
factor. Only the former is discarded as a live Jacobi guard.

In the monic degree-16 clock algebra the residue test at
103 checks the **quadratic** leader of \(F_3\) as a unit.
Its cubic leader is exactly zero on the structural branch
by \(4V+c_2=0\), not inferred from reduction.
Adjoin the monic quadratic in \(s\), giving rank 32.
The exact coefficient of \(r\) in \(c_0\mathcal A(r,s)\)
is a unit there. So the affine cofactor equation determines
\(r\), and \(q=IP(V)/\ell(V)\) and \(U_{\rm rev}\) are
reconstructed by the all-live fourth-clean formulas.
All pivots used are tested in the entire residue algebra.

In the five-initial-ghost case use the true forward
\(A(C\phi)=0\) at those five ghost rows. The paid
initial-prefix hull forces \((X-\xi)I(XU)\) proportional
to \(S_6\bmod U\), with no prescribed remaining ghost
clock. The determinant of \(I(XU),X I(XU),S_6\)
modulo \(U\) is a unit in rank 32 at 103.

In the two- or three-ghost reverse-gap case use the
paired quartic commutators from Section 4 of the
[fourth-clean packet](../dirk11-thirteen-invisible-six-cubic-live-fourth/README.md).
They force the second literal ghost diagonal to zero
under the same true paid grades, even if the first
diagonal is also zero. The first ghost \(z\) obeys
\(r_1^*(z)-z r_0^*(z)=0\); the cubic leader is a unit,
so its monic adjunction gives rank 96. The distinct
second root \(w\) of \(r_1^*(Y)-z r_0^*(Y)\)
comes from its linear/quadratic coefficients, with
unit quadratic leader. The independent genuine
quintic primitive of \((Y-V)YR_3\) then requires
\(Q_{\rm eff}(w)U_{\rm rev}(z)-Q_{\rm eff}(z)U_{\rm rev}(w)=0\).
It is a unit in rank 96 at 103.

Run `python3 replay.py` with SymPy. The source uses
sibling arithmetic modules by default and accepts
`--project`, `--arithmetic`, `--old-pair`
and `--old-mark` overrides. As in the earlier
packets this is a finite-free unit lift in monic clock
algebras over \(\mathbb Z_{(103)}\), not the reduction of
an unknown tableau. The paid scalar adapters are already
kernel-checked in the fourth-clean and two-gap packets;
this is a new exact arithmetic specialization of them.
