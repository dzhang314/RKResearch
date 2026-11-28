# Nine live sites: the four-distinct three-cross edge layout is impossible

**Scope.** Continue the [genuine nine-site six-pair chart](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md).
The four calibration clocks \(a,h=a/2,d=1-b,e=1-b/2\)
are distinct; the extra sets are \(\{e,t\}\) on the
left and \(\{h,t\}\) on the right. Thus \(h,e,t\) are
the three crossing pairs and the other free active
label \(u\) fills both inner non-dormant rows.
This closes the dormant at physical 8 or 10 over
**characteristic zero** given genuine nine-site
separation and the inherited paid mixed transfer.
It completes the earlier finite edge atlas,
including its unordered zero-centroid branch.
The physical-9 dormant branch for this geometry
is not closed here.

## 1. Two paid centroids and their actual live guards

Study dormant physical 8, with clock \(z\), so
rows 9 and 10 both have clock \(u\). Define the
usual models \(V_a=X^2(X-a)^2,V_b=(1-X)^2(X-d)^2\),
\(P=JV_a,Q=\bar J V_b,W=V_aV_b\), and
\[
 H=\int_0^1PV_b,\qquad C=\int_0^1 XPV_b,\qquad
 I_j=\int_0^1 X^jW,\qquad
 I_{uu}=I_2-2u I_1+u^2 I_0 .
\]
The actual \(AV_L V_R\) can have support only
on rows 9 and 10, because \(AV_L\) vanishes
through physical 8 and \(V_R\) after physical 10.
It has one clock \(u\). Paid grades \(5+4\) and
\(5+4+1\) therefore give \(C=uH\), without a
division or a sign claim.

The actual \(V_LV_R\) is supported on rows 8–10.
After multiplication by \(X-u\), only the
dormant row remains; both its model reads are
literal. Its first and second masked tests give
\[
 I_2-uI_1=z(I_1-uI_0),\qquad
 I_{uu}=b_8(z-u)^2W(z)=(z-u)(I_1-uI_0).
\]
The leftmost paired product is grade \(4+4+2\);
the first mask needs one fewer clock factor.
Every factor in the dormant expression is
nonzero by genuine separation and live \(b_8\).
Hence \(I_1-uI_0\ne0\), and
\(z=(I_2-uI_1)/(I_1-uI_0)\) is justified even
when \(H=0\). No Gram positivity argument is
needed for this pivot.

Let \(\Pi_5=(X-a)(X-h)(X-d)(X-e)(X-u)\).
The ordinary tests \(\int X(1-X)\Pi_5 X^j\),
\(0\le j\le3\), have degree at most ten.
In the actual nine-site quadrature only \(z,t\)
survive their factors, with nonzero modified weights
because the nine scalar sites and their **pooled**
masses are live. In particular the \(t\)-pool is
nonzero by the [six-pair response law](ERK11-SIX-PAIR-SITE-MASK.md):
\(B_t f_1 f_2=-\mu_t\ne0\).
Thus a common live scalar multiple of \(\Pi_5\)
does not affect the conclusion that the shifted
zeroth moment \(\int X(1-X)(X-z)\Pi_5\ne0\);
its sole surviving site is \(t\).
The old finite atlas's algebraic singular shifted
orbit is therefore not a true tableau orbit.

## 2. The three exact equations when \(H\ne0\)

In this branch \(u=C/H\). Put
\[
 M=I_1H-I_0 C,\quad N=I_2H-I_1 C,\quad z=N/M .
\]
The preceding live masked product earns \(M\ne0\)
over characteristic zero. In the exact replay use
the scaled hull
\[
 \Pi_5^\#=(X-a)(X-h)(X-d)(X-e)(H X-C),\qquad
 m_j=\int_0^1 X(1-X)\Pi_5^\# X^j .
\]
Set \(p=M m_1-Nm_0,\ q=M m_2-Nm_1,\ r=M m_3-Nm_2\).
The actual shifted row tests are \(q=t p,\ r=t q\),
and \(p\ne0\) by the genuine two-site support.
Thus \(t=q/p\) and the first exact width equation
is \(D=pr-q^2=0\).

The actual first off-diagonal of derivative
characters has factors
\[
 L_0=(a-e)(a p-q),\quad L_1=-e q,\qquad
 R_0=(h-d)(q-dp),\quad R_1=-(1-h)(p-q).
\]
They scale the actual row-7 and row-11 derivative
characters by live factors. Put
\(\Phi_L=L_0D_L^{(0)}+L_1D_L^{(a)}\),
\(\Phi_R=R_0D_R^{(0)}+R_1D_R^{(b)}\).
Their pairing in the normalized inverse Gram
is the second equation \(F=0\).
The left dormant row is literally
\(D_z/a^5\), \(D_z=a^5\ell_z-30P(z)\ell_a\).
Pairing it with row 11 and clearing \(M^5\)
gives the third equation \(G=0\).
Both are paid anchored contacts, not pure model
evaluations asserted at a non-dormant row.

The replay cancels only exact factors of the
live width, clock, \(H,M,p\), or genuinely live
dormant-product/ordinary Lagrange guards.
The reduced bidegrees in \((a,b)\) of \(D,F,G\)
are \((16,16),(20,20),(20,23)\).
The two exact \(b\)-resultants of \(D\) with
\(F,G\) have degrees 624 and 672 in \(a\).
Using the [coefficient-bound CRT method](ERK11-NINE-SITE-HALF-DIFFERENT-CENTER-OPPOSITE-EXIT.md),
60 certified integer primes reconstruct both
via a modulus exceeding twice the coefficient
bounds (bit lengths 3265, 3632).
Their rational monic gcd has degree 280,
with factorization
\[
 a^{32} W_{72}\,W_{12}^4\,W_8^{16}.
\]
The \(W_i\) are the irreducible rational
factors of indicated degrees, returned
by exact factorization. The width \(a=0\)
is forbidden.

At each \(W_i\) use an exact homogeneous
linear subresultant \(\lambda b+\eta\) of
the following guard pair:
\[
\begin{array}{c|c|c}
\text{width degree}&\text{guard pair}&
  \text{common power in }D,F,G\\ \hline
72 & p,q &1\\
12 & M,N &2\\
8  & H,C &4
\end{array}
\]
The leading coefficient \(\lambda\) is a unit
in the complete residue coefficient algebra
modulo 101. In the rational width quotient,
homogeneous evaluation verifies that both
guards vanish at \(-\eta/\lambda\), and that
the requisite initial Taylor coefficients of
\(D,F,G\) all vanish there. Thus the monic
linear factor is a genuine forbidden root,
and may be divided out to the displayed power.
This exact evaluation is done before any
modular gcd inference. Integral monic division
holds over the local coefficient algebra at 101
because the width polynomial is monic there
and \(\lambda\) has a unit norm.

After dividing out those exact factors, all
three degrees are retained and their gcd is
constant in **every** factor field of the
squarefree coefficient reduction modulo 101.
Making one polynomial monic and using its
finite-free power basis, a maximal minor of
the two other quotient multiplication maps is
a unit. This lifts the unit ideal, excluding
every true remaining characteristic-zero \(b\)
fiber. Neither arbitrary tableau reduction
modulo 101 nor an assumption of simple
projected widths is used.

## 3. Zero centroid is also impossible

If \(H=0\), the actual paid centroid gives \(C=0\).
The exact \(b\)-resultant of \(H,C\) has a single
irreducible degree-eight factor in \(a\).
In its complete rational coefficient field the
exact \(b\)-gcd of these equations is linear.
Thus \(a,b\) are now fixed in that field, but \(u\)
is still variable; dividing by \(H\) would not be
permissible.

Use the same three equations in \(u\), now with
the true monic \(\Pi_5\),
\(M=I_1-u I_0\), \(N=I_2-u I_1\). These are the
same actual live shifted moment operations and
same literal derivative contacts, because the
masked dormant read proved \(M\ne0\) regardless
of \(H\). Their **raw** degrees are \(4,4,7\)
in \(u\), and the exact common gcd is constant
in the degree-eight coefficient field. No
positive-definiteness premise or dropped root
is needed to earn \(H\ne0\) as a consequence.

## 4. Optional paid pooled mark and reflection

There is a further independent literal contact,
though the elimination above does not need it.
Let \(R_9,R_{10}\) be the actual two reverse
anchored functionals of the active pair at \(u\).
Their \(B_u\)-normalized weighted average
cancels the common response correction by
the vanishing first response pool. Its form is
\(r_u+\rho r_d\) for some scalar \(\rho\).
Both the actual forward \(D_z/a^5\) at row 8
and \(\Phi_L\) at row 7 annihilate it, giving
the pivot-free mark
\[
 \langle D_z,r_u\rangle_N\langle\Phi_L,r_d\rangle_N
 -\langle D_z,r_d\rangle_N\langle\Phi_L,r_u\rangle_N=0.
\]
No optional derivative coefficient is divided out.
The companion Lean gate checks response-average
cancellation, the determinant step, and the
masked-moment live-factor identity.

Exchange the two models and reflect \(X\mapsto1-X\)
to handle physical-10 dormancy. All mixed
supports and paid grades exchange; no reverse
ordinary order eleven is invoked.
The standalone replay only needs SymPy and
python-flint (verified 0.9). The physical transfer,
quadrature payment and exact eliminations are
mathematical plus replay, not an end-to-end native
Lean tableau theorem. No numerical stage bound
changes.

[Replay program](erk11-nine-site-distinct-three-edge-exit/replay_n12_distinct_three_edge_exit.py), [exact output](erk11-nine-site-distinct-three-edge-exit/exact-replay.txt), and [portable Lean gate](../lean/RKCert/ReviewedNative/ERK11RepeatedPoolPortGate.lean).
