# Nine live sites: the half–half different-extra edge layout is impossible

**Scope.** Continue the [genuine nine-site six-pair chart](ERK11-SIX-PAIR-DORMANT-CLOCK-SEPARATION.md)
with half–half overlap and **different** extra sets.
This excludes the dormant at physical 8 or 10 over
characteristic zero given genuine nine-site separation
and the inherited mixed order payments. It uses the
[prior full edge-pivot exclusion](ERK11-NINE-SITE-HALF-DIFFERENT-EDGE-PIVOTS.md),
so neither a zero right cubic pair nor a zero left
derivative pair is assumed away. Together with the
central different-extra and same-extra exits, this
closes the half–half part of the nine-site chart,
not the four-distinct geometries or all of ERK11.

## 1. Physical edge supports and measured port

Study dormant physical 8; reflection exchanges the
two paid mixed systems and handles dormant physical 10.
Write \(z=c_8\) for the dormant, \(x=c_9\), \(y=c_{10}\)
for the other inner clocks, \(a,b=2-a,\ d=a-1,\ h=a/2\),
and \(t\) for the common free extra. Let \(u,v\) denote
the left-only and right-only active labels. “Right
matched” means \((u,v)=(x,y)\); “right opposite”
means \((u,v)=(y,x)\). All nine scalar clock sites
are genuine and distinct.

Use the preceding models \(V_a=X^2(X-a)^2\),
\(V_b=(1-X)^2(X-d)^2\), primitives \(P=JV_a,\ Q=\bar J V_b\),
and model moments
\[
 H=\int PV_b=\int V_aQ,\quad C_1=\int XPV_b,\quad
 C_2=\int XV_aQ,\quad J_0=\int PQ,\quad
 I(p,q)=\int V_aV_b(X-p)(X-q).
\]
Literal \(V_L,V_R\) vanish through their seventh
row in the corresponding orientations; \(AV_L\)
vanishes through physical 8, and \(A^\star V_R\)
from physical 10 onward. Their single-primitive
mixed products are supported on \(\{9,10\}\) and
\(\{8,9\}\); the two-primitive product is supported
on \(\{9\}\). The unadvanced mixed product is
supported on \(\{8,9,10\}\).

The four-product algebra of the
[central two-clock gate](ERK11-NINE-SITE-CENTRAL-TWO-CLOCK-RANK-ONE-EXIT.md)
applies to the **physical middle read at 9** now
at clock \(x\), whether or not it is dormant.
Inserting \(X-y\) in the forward primitive
product, \(X-z\) in the reflected primitive
product, and \((X-z)(X-y)\) in the unadvanced
product isolates physical 9 in all four.
The order grades are \(5+4+1,\ 4+5+1,\ 5+5,\ 4+4+2\).
Consequently
\[
 (C_1-yH)(C_2-zH)=J_0 I(z,y).
\]
In particular one does **not** divide by \(I(z,y)\)
or identify its active stage-9 values with \(V_a(x),V_b(x)\).
The bilinear coefficients \(A_0,B_0,C_0,D_0,\Delta_0\)
of the earlier gate therefore now apply to \((z,y)\),
not \((x,y)\).

At dormant physical 8 both unadvanced values are
the model values. Inserting the other two inner
clocks gives the genuinely live factor
\[
 I(x,y)=b_8(z-x)(z-y)V_a(z)V_b(z)\ne0 .
\]
The reflected primitive product with \(X-x\) gives
\[
 C_2-xH=b_8(z-x)V_a(z)Q_8,\qquad
 Q_8=(C_2-xH)(z-y)V_b(z)/I(x,y).
\]
Here \(Q_8=(A^\star V_R)_8\) is an actual read.
NB: \(P_8=0\) by strictness, not from this formula.
Thus the actual left anchored row 8 is
\(D_z/a^5\), \(D_w=a^5\ell_w-30P(w)\ell_a\);
at the right anchored row 8 the only possible
correction is a multiple of \(r_d\), determined
by this actual \(Q_8\). Its scaled functional is
\[
 I(x,y)\big(b^5r_z-30Q(z)r_d\big)
       +30(C_2-xH)(z-y)V_b(z)r_d .
\]
The companion Lean gate checks the scalar product
transfer to \(Q_8\) before field division.

## 2. Exact contact solves, with no shifted pivot assumption

Let \(K_j(w)\) be the pairings of \(D_w\) with
the two right derivative basis rows, divided by
\(aw(a-w)\); let \(\widetilde K_j(w)\) be the
reflected cubics obtained from
\(D^R_w=b^5r_w-30Q(w)r_d\) and divided by
\(b(1-w)(w-d)\). The brackets suppress the
common Gram scale 210. Write \(k_j=K_j(z)\).
The actual off-diagonal of row 8 with row 11
forces \(\Phi_R\) proportional to
\((k_1,-k_0)\), with both \(k_j\ne0\) by the
prior edge-pivot proof. The row-7/row-11
contact then forces \(\Phi_L\) proportional to
\((g_1,-g_0)\), where
\[
 g_0=k_1-T_4(b)k_0,\qquad
 g_1=T_4(a)k_1-U_{4,4}(a,b)k_0 .
\]
Both are live by the same prior result,
including possible derivative-rank width fibers.
The scalar pattern of the contacts gives
\[
 u=\frac{a(a-t)g_0}{(a-t)g_0+t g_1},\qquad
 v=\frac{d(t-d)k_0+(1-t)k_1}{(t-d)k_0+(1-t)k_1}.
\]
The left numerator is live, and the right
denominator minus numerator is \(b(t-d)k_0\ne0\).
The same reasoning works when solving either
relation for \(t\) from \(u\) or \(v\).

If \(\Delta_0\ne0\), put \(E=A_0z+C_0,\ Y=-(B_0z+D_0)\).
At an actual solution \(E\ne0\): otherwise both
affine coefficients of the bilinear would vanish,
forcing \(\Delta_0=0\). Thus \(y=Y/E\). In each
orientation the contact solves yield \(t=t_N/t_D\),
\(x=x_N/x_D\):
* right matched \(y=v\): first use
  \(t_D=(Y-dE)k_0+(E-Y)k_1\),
  \(t_N=d(Y-dE)k_0+(E-Y)k_1\), then
  \(x_D=(a t_D-t_N)g_0+t_Ng_1,\
  x_N=a(a t_D-t_N)g_0\);
* right opposite \(y=u\): first use
  \(t_D=(aE-Y)g_0+Yg_1,\ t_N=a(aE-Y)g_0\),
  then \(x_D=(t_N-dt_D)k_0+(t_D-t_N)k_1,\
  x_N=d(t_N-dt_D)k_0+(t_D-t_N)k_1\).

These exact denominators are live by the guards just
proved. Scale homogeneous coordinate pairs by
removing their common exact factors; this is safe
because the original denominator is live. The
replay reduces the \(g\)-pair by \(a(a-2)\),
the right-matched \(t\)-pair by \(a-2\), and the
right-opposite \(x\)-pair by \(a-2\), up to nonzero
constant normalizations. Other common factors
in these coordinate normalizations are constant.

From the ordinary degree-ten scalar quadrature,
there are precisely the two shifted tests
\[
 S_j=\int_0^1 X(1-X)(X-z)
       (X-a)(X-h)(X-d)(EX-Y)(t_DX-t_N)(x_DX-x_N) X^j=0,
       \qquad j=0,1.
\]
Only live scales multiply the monic active hull.
There is no third shifted equation or presumed
rank of a shifted Hankel matrix in this reduction.

## 3. Two more actual marks used in the projection

Here let \(A_a=\langle\ell_a,\Phi_R\rangle_N\),
\(A_d=\langle\Phi_L,r_d\rangle_N\); these may vanish.
The actual reverse dormant row 8 pairs with
left row 7 to zero. With
\[
 I_N=E x_D I_2-(E x_N+Y x_D)I_1+Y x_N I_0
\]
this gives, after dividing the live \((1-z)(z-d)\)
factor,
\[
 \mathrm{Port}=
 b I_N\{g_1\widetilde K_0(z)-g_0\widetilde K_1(z)\}
 +30(C_2 x_D-x_N H)(Ez-Y)(1-z)(z-d)A_d=0 .
\]
This is the actual off-diagonal, not an equation
assuming the reverse dormant primitive is zero.

For **right matched** \(y=v\), the right-only
active label is repeated at a calibrated right
front row and physical 10, with \(Q=0\) in both.
The [same-clock anchored row difference](ERK11-NINE-SITE-HALF-DIFFERENT-CENTER-MATCHED-EXIT.md)
then gives \(\langle\Phi_L,D^R_y\rangle_N=0\).
The response difference is nonzero by the pair
law. Its normalized cubic contact, cleared by
\(E^3\), is the additional gate \(G_1=0\).

For **right opposite** \(y=u\), the forward
repeated-exclusive mark at physical 10 applies.
The actual grade-ten masked square product
isolates row 10 with clocks \(z,x\), and the
forward primitive product with clock \(x\)
also isolates row 10. Thus its paid mark is
\[
 I(z,x)\langle D_y,\Phi_R\rangle_N+
 30V_a(y)(y-z)(C_1-xH)A_a=0 .
\]
It applies without dividing by any individual
mixed amplitude. After dividing by \(y(a-y)\),
the divided difference
\[
 K_{\rm diff}(w,z)
 =\frac{K_0(w)K_1(z)-K_1(w)K_0(z)}{w-z}
\]
is polynomial and has degree at most two in \(w\).
The factor \(y-z\) is live.
The opposite gate \(G_1\) is the cleared polynomial of
\(a I(z,x)K_{\rm diff}(y,z)+
30y(a-y)(C_1-xH)A_a=0\).

The algebra also gives an independent optional
primitive mark at physical 9:
\(\,(C_2-zH)\langle D_x,\Phi_R\rangle_N+
30V_a(x)(x-z)J_0A_a=0\) in the right-matched
orientation, or
\(\,(C_1-yH)\langle\Phi_L,D_x^R\rangle_N+
30V_b(x)(x-y)J_0A_d=0\) in the right-opposite
orientation. Multiply the same-clock row difference
by the other actual primitive and the matching
clock/model factors. This uses the true
\(b_9P_9Q_9=J_0\), not a division by \(C_1-yH\)
or \(C_2-zH\). These optional marks are **not**
needed for the final projection.

## 4. Exact widths and genuine fibers, \(\Delta_0\ne0\)

In the four required gates \((G_1,S_0,S_1,\mathrm{Port})\)
remove exactly the replayed live factors, up to constants.
The shifts have no removed factor. In right matched,
the \(G_1\) factor is \(b^4F_6\); in right opposite
it is \(a^5b\). The Port factor is \(b^3F_6\)
in both. Here \(F_6\) is the derivative-width
factor of \(\Delta_0\); thus only genuine live
factors are canceled. The reduced bidegrees are:
\[
\begin{array}{c|rrrr}
 &G_1&S_0&S_1&\mathrm{Port}\\ \hline
 \text{right matched}&(28,6)&(51,13)&(51,13)&(44,14)\\
 \text{right opposite}&(53,12)&(55,13)&(55,13)&(45,14)
\end{array}
\]
in variables \((a,z)\). The exact three \(z\)-resultants
of \(G_1\) with the three remaining required gates
have degrees \((624,624,616)\) or \((1253,1257,1193)\).
Each finite actual common \(z\) gives all three
resultants zero, even at a specialized degree drop.
Their rational width gcds have degrees 279 or 668.
The CRT reconstruction uses certified integer primes
and the coefficient \(\ell^1\) determinant bound
from the [opposite central exit](ERK11-NINE-SITE-HALF-DIFFERENT-CENTER-OPPOSITE-EXIT.md):
the prime products exceed twice every exact bound.
There are 35 or 68 primes, respectively; the result
is an exact characteristic-zero projection, not a
tableau test modulo primes.

After dropping width factors dividing \(\Delta_0\),
the full rational factor table and fiber tests are:
\[
\begin{array}{c|r|c|c|c}
\text{orientation}&\text{width degree}&
\text{guard pair for exact linear gcd}&
\text{power removed from four gates}&p\\\hline
\text{matched}&17& k_0,\ Y-E&1&101\\
&21&k_0,\ k_1&1&101\\
&27&k_1,\ Y-dE&1&103\\\hline
\text{opposite}&6& z,\ z&1&101\\
&9& z-a,\ z-a&1&101\\
&14&g_0,\ Y&1&101\\
&18&g_1,\ Y-aE&1&101\\
&21&k_0,\ k_1&3&101\\
&32&k_0,\ t_N-t_D&1&101\\
&51&k_1,\ t_N-dt_D&1&101
\end{array}
\]
Degrees label irreducible width factors per orientation;
the residual degree 6 factor is distinct from \(F_6\).
The replay works in the exact rational coefficient
field of each irreducible width. The stated pair
of **live** guard polynomials has monic linear gcd
\(z-z_0\). It checks exact divisibility of all four
gates by the displayed power, keeping that forbidden
root outside the actual chart. The quotient data
are then integral at the listed prime. In every
complete factor field of the squarefree reduction
of the width polynomial, the four quotients have
constant gcd and each retains its full exact degree.
Make one quotient monic using its leading-unit norm.
Its power basis is finite free over the coefficient
algebra, also finite free over the rational integers
localized at the prime. A maximal minor of the
multiplication maps generating the quotient unit ideal
modulo the prime is a unit. Therefore the same unit
ideal holds over characteristic zero. This excludes
every remaining true \(z\) fiber, not just generic
roots of two projections.

## 5. Full determinant-zero fibers

The exact width identity
\(1646877554784000000\Delta_0=-a^2(a-2)^2F_4F_6\)
shows that only the \(F_4,F_6\) fibers remain.
Both have \(A_0\ne0\), and the rank-one bilinear
gives \(z=-C_0/A_0\) **or** \(y=-B_0/A_0\).
Use the already-earned contact solves with this one
fixed clock. The other is a single scalar parameter.
In the exact degree-four width field, both shifted
polynomials have constant gcd for either fixed clock
and both orientations. In the degree-six width field,
the fixed-\(z\) option makes both left port coefficients
\(g_0,g_1\) zero, an inherited impossible contact
dropout. For fixed \(y\) the exact shifted gcd is
a power of \(z(z-a)\) times the linear residual of
\(g_0/[z(z-a)]\): one power in right matched and
two in right opposite. Its roots are all forbidden by
the actual live \(z,z-a,g_0\). This includes the case
both forced roots occur and uses no ordered signs.

Reflection \(X\mapsto1-X\) exchanges strict supports,
the two primed models and the two orientations of the
paid systems; it obtains the physical-10 exclusion
without ordinary reversed order eleven.
The portable Lean gate checks the dormant read,
inner primitive mark, and cubic difference algebra.
The actual stage transfer, order payments and width
elimination remain mathematical plus the exact
standalone replay, not a native Lean tableau exclusion.

Replay with SymPy and python-flint:
`python3 -B erk11-nine-site-half-different-edge-exit/replay_n12_half_different_edge_exit.py`.
The [exact replay](erk11-nine-site-half-different-edge-exit/exact-replay.txt)
and [portable Lean gate](../lean/RKCert/ReviewedNative/ERK11EdgeDormantBilinearGate.lean)
are archived separately.
