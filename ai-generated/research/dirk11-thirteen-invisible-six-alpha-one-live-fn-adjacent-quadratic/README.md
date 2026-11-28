# The adjacent carrier equation keeps its quadratic leader

**Result.** In the remaining normalized invisible-six DIRK11/13
live direct noncontact \(F_n\) chart with \(\alpha=\beta=1\)
and nonzero fourth and fifth regular reverse diagonals,
the actual reverse quartic signal \(W_0(V)\) is nonzero.
Consequently the adjacent carrier equation \(A(E)=0\) is
genuinely quadratic with a live leading coefficient; it may
safely be made monic at any candidate. This is distinct from
the already treated signal \(W_0(x)\) at a ghost. It does not
give an unrestricted stage-bound change.

Use \(Y=1-c\), \(R=(Y-v)(Y-u)(Y-w)\), \(P=Ym\),
\(P_0=YR\) in the old reverse notation. The physical \(z\)
is the first-gap ghost, \(V\) is the next regular row, \(x\)
is the first middle ghost. The
[actual matched-column proof](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md)
gives \(d_x=0\), \(L=\lambda(Y-z)(Y-x)\) with live \(\lambda\),
and the genuine first-middle commutator. The
[fourth-clean separation](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-fourth-separation/README.md)
gives \(V-z\ne0\) in the nonzero-\(d_V\) chart.
Write \(\ell=\ell_1(Y-z)\), and \(IP=\ell P+\delta P_0\).
Here \(\delta\ne0\) by old nonmonomiality. Also
\(1+\ell_1\ne0\) by the
[old slope-minus-one exclusion](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-minus-one/README.md).

## 1. Exact coefficient and actual surviving linear pivot

Define the old polynomial quotients
\[
 F=W_0/(Y-z),\qquad B_0=(IP_0-PW_0)/P_0 .
\]
Both are at most affine by the old samples and the first
ghost zero. The genuine fourth ordinary quartic gives
\(d_V=B_0(V)-K_*F(V)\). The
[cleared adjacent equation](../dirk11-thirteen-invisible-six-alpha-one-live-fn-fifth-compensator/README.md)
uses \(E=qK_*\), \(Z=qY-p\), live \(q\),
\(Q=ZP+E P_0\), and common live old numerator scale \(n\).
With \(L^\#=Z\widehat\ell-q\widehat\rho+E\widehat W_0\),
write \(a=[Y^2]L^\#,\ x_n=-q[Y]L^\#-pa\).
Then
\[
 A(E)=q(nq/5-a)[Y^4]Q\,Vc_0+x_n[Y]Q,\qquad c_0=R(0).
\]
Taking coefficient \(E^2\) gives exactly \(-c_0 U_V\),
where \(U_V=q\widehat W_{0,1}+(p+qV)\widehat W_{0,2}
       =nq F(V)\).
These are exact coefficient identities, not generic
nonvanishing claims. Since \(V-z\ne0\), loss of the
quadratic leader means \(W_0(V)=0\).

In that hypothetical branch \(d_V=B_0(V)\) is independent
of \(K_*\). The true adjacent relation in the same actual
gauges is
\[
 (V-z)(\delta-\ell_1K_*)
      +((1+\ell_1)K_*-\delta)d_V=0.
\]
Indeed \(A(E)\) is this expression times
\(nq^3c_0/(1+\ell_1)\), by the old fits and integration by
parts. **coordinate-audit.py** checks that scale and its
leading coefficient identically in \(E\) on four exact
rational old-coordinate probes. The actual equation
therefore has coefficient of \(K_*\)
\((1+\ell_1)d_V-\ell_1(V-z)\), and constant
\(\delta[(V-z)-d_V]\). If that coefficient were zero,
the actual root and live \(\delta\) would force
\(d_V=V-z\); the same coefficient would then equal
\(V-z\ne0\), a contradiction. Hence \(A(E)\) is truly
linear with live \([E]A\) on this hypothetical slice.
Replacing \(E\) by \(-[E^0]A/[E^1]A\) is legitimate
throughout the slice, not an assumption about generic
roots or a modular pivot.

## 2. Excluding the exact leading-zero locus

**project.py** projects the exact polynomial \(U_V=0\)
in the familiar scaled rank-12 monic \(F_n\)/ordinary tower.
Only common content on forbidden ordinary factors is removed.
The exact raw norm degree is **1068**, squarefree degree
**200**. Beyond \(J_4,E_+\), its support is:

| Factor | Live guard | Exact cap | Residue degree at 103 |
|---|---|---:|---:|
| degree 12, constant 16227 | homogeneous \(c_1+6s\) | 11 | 12 |
| degree 12, constant 54123 | \(c_2\) in rank-four lower algebra | 9 | 4 |
| degree 48, constant 1865429207937 | homogeneous first-gap \(q\) | 11 | 1 |
| degree 60, constant −1461941766456 | determinant of old \(m\)-multiplication | 11 | 1 |
| degree 60, constant −10517167453750047 | 1 | 12 | 6 |

The exact guard norms give the displayed upper ranks,
with the lower ordinary rank cap 3 lifted to 9 for \(c_2\).
The pure signal \(U_V\) itself vanishes at all actual
candidates in the slice. The true first-middle
commutator, using \(d_x=0\), has homogeneous carrier
degree at most four after \(x\) is reconstructed; use
the exact scale of the
[late-affine proof](../dirk11-thirteen-invisible-six-alpha-one-live-fn-late-affine/README.md)
without its exceptional slope condition. Its homogeneous
degree-four value at \((-[E^0]A,[E^1]A)\) is another
necessary scalar. No presumed specialization degree or integrality of old
weight ratios enters this evaluation.

**rank.py** takes the summed multiplication images of
the guard times \(U_V\), and the guard times that pinned
first-middle scalar, on each exact model's chosen residue
component at 103. The observed ranks **132, 36, 11, 11,
72** attain the exact caps times their residue degrees.
Thus the exact characteristic-zero image is the whole
guard image; evaluating at an actual candidate would
kill its live guard. This is a rational rank lift, not
reduction of unknown clocks, \(E\), or tableau entries.
The hypothesized leading loss is excluded.

Run **bash verify.sh** with SymPy and python-flint 0.9.
This is an exact written and reproducible source proof;
the local Lean pivot statement, if supplied separately,
does not purport to formalize the rooted tableau ingress.
