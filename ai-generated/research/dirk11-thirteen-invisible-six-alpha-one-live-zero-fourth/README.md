# A zero fourth reverse diagonal is impossible in the live direct Fn cube

**Result.** In the normalized no-late invisible-six
DIRK11/13 profile with cubic carrier, \(\tau\ne0\),
\(\alpha=1\), direct noncontact old \(F_n\) and
\(\beta=1\) or 2, the literal fourth ordinary reverse
diagonal must be nonzero. This packet excludes only
\(d_V=0\), not the unrestricted thirteen-stage case.
The real stage interval remains **13–14**.

Use the order and true spaces of the
[early profile census](../dirk11-thirteen-invisible-six-early-profile-census/README.md)
and [live finite-profile proof](../dirk11-thirteen-invisible-six-alpha-one-live-cubic/README.md).
The literal reverse order is
\(T,v,u,w,z,V,[\beta],B,[\gamma],O\).
Write \(Y=1-c\), \(N=A^{\mathsf T}\),
\(W(P)=b_{\rm wt}P(Y)\), and \(I\) for primitive from
zero. Let \(R\) be the old hull of the three ordinary
reverse clocks, \(P_0=YR\), and \(L_0=IP_0/Y\).
With the true old interpolant \(m\), use
\(P=Ym\), \(M=(J_4/m)\bmod R\), and
\(W_0=(L_0/m)\bmod R\).
The actual quartic error is \(G W_0\).
Normalize the live reciprocal relation as
\(G/b_{\rm wt}=YJ_4/U_r\) on regular sites, with
\(U_r(Y)=U(1-Y)=M+tR\), \(t\ne0\).

## 1. Zero diagonal, distinct numerical sample, and actual zero tap

Assume \(d_V=0\). The genuine quartic at \(V\) reads
\(IP_0(V)=W_0(V)k\), where \(k=G_V/b_V\ne0\).
For the actual early tap \(T_*=N_{V,z}G_z/b_V\),
write \(\ell,\rho\) for the usual old
\(IP/P,I^2P/P\) fits. The paired true cubic marks at
\(V\), with zero diagonal, give
\[
 T_*=\ell(V)k-IP(V),\qquad
 (z-V)T_*=I^2P(V)-\rho(V)k.
\]
The latter is the strong adjacent marked read from the
[live finite-profile proof](../dirk11-thirteen-invisible-six-alpha-one-live-cubic/README.md#1-common-old-fit-and-adjacent-marked-quadratic).
If \(\lambda\) is the slope of \(\ell\),
the actual first-gap calculation gives
\(\ell(V)=\lambda(V-z)\) and the identities
\[
 (1+\lambda)I^2P=\ell IP+\delta IP_0,qquad
 (1+\lambda)\rho=\ell^2+\delta W_0.
\]
The first is an exact polynomial identity by integration
by parts; the second is its old remainder. The constant
\(\delta\ne0\) in the nonmonomial direct Fn profile.

If \(L_0(V)=0\), the quartic forces \(W_0(V)=0\).
The [degree-24 exact ordinary projection of
this primitive](../dirk11-thirteen-invisible-six-cubic-zero-five/README.md)
depends only on \(IP_0(V)=0\) and the ordinary Jacobi
pencil, not on any other chart. **contact.py** uses
its same linear ordinary cofactor and the direct Fn
cubic profile. It verifies \(W_0(V)\) is a unit at
103 in the full rank-72 ordinary/profile algebra, a
contradiction. In particular all inversion denominators
are units over this prescribed algebra; no actual
tableau is reduced at 103.

Thus \(L_0(V)\ne0\). Numerical \(z=V\) is also
impossible: \(\ell(z)=\rho(z)=0\), so the actual
marked equation above gives \(I^2P(V)=0\).
The first integration identity gives \(\delta IP_0(V)=0\)
and hence the already excluded \(L_0(V)=0\).
Now multiply the marked equation by \(1+\lambda\).
The two integration identities, the quartic at \(V\),
and the unmarked equation combine to
\[
 (1+\lambda)(z-V)T_*=-\ell(V) T_*.
\]
As \(\ell(V)=\lambda(V-z)\) and \(z\ne V\),
this gives **\(T_*=0\)** with no division by
\(1+\lambda\). The actual tableau entry \(N_{V,z}=0\)
follows from live \(G_z,b_V\).
Eliminating \(k\) between the quartic and unmarked
reads yields the first exact base gate
\[
 \ell(V)IP_0(V)-W_0(V)IP(V)=0.                            \tag{1}
\]

## 2. A forward rank strengthened to six ghost zeros

Let \(a=1-V,b=1-B\), \(\phi=U(c)-g\), and
\(\Omega=A[C(C-b)\phi]\).
The actual masked-primitive argument gives zero
reads at the first five forward ghosts.
The sixth forward ghost is the physical \(z\),
after \(a\) but before the older ordinary clocks.
Its only possibly nonzero masked clean donor is
\(a\), and that entry is \(A_{z,a}=N_{V,z}=0\).
Thus \(\Omega\) vanishes on **all six ghost rows**.
At \(a\) the only possible input is its own
diagonal, which is zero, and at \(b\) all inputs
are killed.

Put \(H=XJ_4(X)\), \(F_b=I_X[X(X-b)U]\) and
\(K_b=H(b)F_b-F_b(b)H\). The genuine grade-six
zero-profile space is
\(g\mathcal P_3+K_{\rm coeff}(e_T-H_T)\),
as in the live finite-profile proof. Hence
\(K_b+UQ_3\) on the six ghost clocks is zero,
and as a polynomial of degree at most six it
is a scalar multiple of their hull.
The six ordinary nonterminal hull \(S_6\) is
proportional to that ghost hull modulo \(U\),
with the live proportionality from the true \(E_6\)
shape and coprimality of \(S_6,U\).
Therefore \(K_b\) is a scalar multiple of \(S_6\)
modulo \(U\), **not** merely an affine multiple
of a five-ghost hull.

Reflect to reverse coordinates. The three live
factors \((Y-1)(Y-B)(Y-V)\) of reflected \(S_6\)
also divide \(K_b(1-Y)\): these are the literal
zero clean reads at forward \(0,b,a\).
They are units modulo the cubic carrier.
The degree-at-most-three quotient polynomial
\(P_f=K_b(1-Y)/((Y-1)(Y-B)(Y-V))\)
is therefore a scalar multiple of \(R\) modulo
\(U_r\). Thus \(P_f\in\operatorname{span}(R,U_r)\)
by the degree limit. Reducing modulo \(R\) yields
the three coefficient minors
\[
 M_i [P_f\bmod R]_j-M_j[P_f\bmod R]_i=0,
 \qquad 0\le i<j\le2.                                   \tag{2}
\]
Every column here is in the reverse coordinate.

## 3. Exact direct Fn clock proof

The actual zero diagonal and old quartic give
\(D_4(V)+tL_0(V)=0\) with
\(D_4=(L_0M-W_0J_4)/R\).
Since \(L_0(V)\ne0\), use the scaled actual carrier
\(C=L_0(V)M-D_4(V)R\).
The polynomial gate (2) is homogeneous, so it
can be computed using the forward reflection of
this one carrier. **clock.py** independently
recalculates the reflected primitive in the scaled
reverse coordinate:
\[
 I_X[X(X-b)C(L-X)](L-Y)
     =\int_Y^L (L-Z)(B-Z)C(Z)\,dZ ,
\]
where \(L=132J_4(V)\) is the clock scale and
\(b=L-B\) uses the scaled \(B\).
It verifies this identity coefficientwise over the
exact monic clock quotient, and separately checks
the reflection of \(H\). Thus no forward coefficient
list is reduced against a reverse modulus.

The rank-12 finite-free algebra over \(\mathbb Q[V]\)
is the monic ordinary quartic in \(\widehat B=LB\)
and the monic scaled Fn cubic for
\(\sigma=L_3 L^2s\), where \(L_3\) is its scaled
cubic leader. The direct ratio
\(r=6c_2s/(c_1+6s)\) is implemented in a common
homogeneous numerator gauge with no guard division.
The old inverse fits use a common adjugate, whose
scalar is live on actual profiles. All removed
nonconstant coefficient content is supported on
\(V(V-1)J_4 E_-E_+E_{\rm rep}\), all live by
the ordinary Jacobi guards.

The exact projection norms of (1) and the three
minors (2) have degrees **720,836,836,836**.
Their exact joint gcd has degree **588**. The
only forbidden Jacobi factors are
\(J_4^{48}\) and \(E_+^6\), with
\(2VE_+=J_5+J_4\) (the latter would force a
zero ordinary endpoint root). The other exact
irreducible factors and their certificates are:

| Degree (constant) | Multiplicity | Actual-live guard | Cap | Residue degree |
|---|---:|---|---:|---:|
| 60 (17286671927043) | 1 | cleared carrier at \(V\) | 11 | 3 |
| 60 (−1461941766456) | 1 | old \(m\)-norm | 11 | 1 |
| 12 (16227) | 3 | scaled \(c_1+6s\) | 11 | 12 |
| 12 (54123) | 18 | lower \(c_2\) | 9 | 4 |

For each listed exact factor \(f\), the script checks
divisibility by \(f\) of the **exact** norm of its
guard. Thus the guard multiplication image over
\(\mathbb Q[V]/f\) has dimension at most the indicated
cap (the lower quartic rank is at most 3 for \(c_2\)).
The mod-103 multiplication columns for the four
necessary equations times the guard attain that cap
in the chosen residue extension. Since exact
vanishing minors would reduce to zero, they attain
it over the exact field, so their sum equals the
whole image of the guard. Any actual evaluation
killing (1) and (2) would kill that live guard.
The carrier-at-\(V\) guard is genuinely live because
it is \(L_0(V)U_r(V)\) in the chosen numerator gauge.
No actual clocks, weights, or tableau entries are
assumed integral modulo 103.

These tests use no beta-specific crossing. They
exclude only the stipulated zero-fourth-diagonal
direct Fn case, not the remaining live-diagonal
profile.

## Reproduction and native scope

Use Python 3 with SymPy and python-flint 0.9.0:

    python3 clock.py
    python3 contact.py

The second script accepts **--research PATH** for
siblings in an isolated checkout. This packet is an exact written/source proof. A separate
Lean source for the scalar transfers is awaiting its
kernel audit and is not part of this immutable receipt.
