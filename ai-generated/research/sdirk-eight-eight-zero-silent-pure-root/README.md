# Eight distinct zero clocks: the pure barycentric root cannot be silent

Let \(A,\mathbf b\) be a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with common nonzero diagonal \(\gamma\). Put \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Assume exactly eight physical zeros of \(\mathbf g\), at **eight different clocks**. The [low-label census](../sdirk-eight-eight-zero-low-labels/README.md) makes the other two stages the distinct individually silent physical rows 1 and 2. This packet concerns a zero-residual stage \(i\) at which both the ordinary weight \(b_i\) and the reverse pure quadratic coordinate \(z_i\) vanish.

**Result.** Such a stage is impossible over every characteristic-zero field. In the live reflected arithmetic branch the argument works over every field of characteristic zero or greater than seven with the stated literal off support. There is no assertion about the all-active affine root or a root that is not an actual node, or about general ten-stage nonexistence.

## 1. A silent pure root leaves seven scalar supports

Normalize \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\), and let \(U\) be the coordinate space on the eight physical zero-residual rows. Write \(P_8\) for the monic polynomial of their eight labels. The pure reverse quadratic row \(\mathbf z^\mathsf T\) is supported on \(U\), is nonzero at the terminal row, and annihilates scalar powers through degree five. Its nodal numerators are therefore affine:
\[
        z_i P'_8(x_i)=\theta(x_i),\qquad \deg\theta\le1.
\]
Indeed the moment nullspace has dimension two and the vectors of nodal values of \(1,T\), divided by the respective derivatives, lie in it by the leading-coefficient identity for Lagrange interpolation. The second reflected ratio is nonzero: otherwise the pure row would be supported at the terminal clock only, not possible with eight different labels and its constant moment zero.

If \(z_i=0\), then \(\theta(T)=k(T-\beta)\) with \(k\ne0\) and \(\beta=x_i\). A simultaneous \(b_i=0\) makes the weight and pure row supported at the other seven nodes. Their monic node polynomial is \(P_7=P_8/(T-\beta)\), and
\[
 z_jP'_7(x_j)=k\quad(j\ne i),\qquad I_D(P_7)=0,\qquad
 I_D(T^m)=D^m/(m+1).
\]
Thus the three actual rear cardinal ratios on these seven nodes are the ordinary, non-aggregate formulas: \(\beta\) cannot be a rear node, because all three rear pure coordinates are nonzero by the [paid literal gate](../sdirk-eight-eight-zero-low-labels/README.md#2-a-paid-rear-nonvanishing-and-exact-multiplicities).

## 2. The extra silent coordinate is a pure forward axis

The reverse space \(W_3\) is the span of the four ordinary rows \(\mathbf b^\mathsf T (C')^j\), \(0\le j\le3\), and the two pure rows \(\mathbf z^\mathsf T,\mathbf z^\mathsf T C'\), where \(C'=\operatorname{diag}(\mathbf x)\). The pure pair is independent at the last two physical labels since \(\kappa_R\ne0\). Thus the coordinate column \(\mathbf e_i\) is in \(F_4=\operatorname{Ann}W_3\) when \(b_i=z_i=0\).

Let \(a,b,c\) be the first three actual zero clocks, in physical rows 3, 4, 5. The supported forward gates give \(a=1+2u,\ Q(u)=0,\ b^2-(2u+4)b+1+2u=0,\ C_3(c;D)=0\) as in the [low-label proof](../sdirk-eight-eight-zero-low-labels/README.md#1-literal-placements-and-exact-profile-gates). Put \(Z_2=(T-a)(T-b)\), \(Z_3=T Z_2\). All cubics have actual supported representatives in \(E_3\), as shown by the two supported quadratics there. For these two inputs the primitive discrepancies at \(a,b\) form the matrix of \(-JZ_2,-JZ_3\), where \(J\) integrates from zero, since the inputs kill all earlier actual zero rows. Its determinant is \(a^2b^2(a-b)^3/24\ne0\). Here \(a\ne0\) follows by evaluating \(Q\) at \(u=-1/2\), and then \(b\ne0\) from its quadratic. Since \(GE_2\) has rank two on the off rows and \(\dim F_4=4\), this matrix detects all of the rank-two \(F_4|_U\). The axis \(\mathbf e_i\) must therefore be at \(a\) or \(b\).

On the other seven labels, \(F_4\) restricts to the line of \(L_{4,D}\): removing the axis drops the rank from two to one, and this Legendre trace is nonzero on seven distinct nodes. Similarly \(F_5\) restricts to the three-dimensional span of \(L_{3,D},L_{4,D},L_{5,D}\). Its restriction to \(U\) initially has rank four, and removing the same axis reduces rank by one. The indicated three traces are in \(F_5\) by the paid orthogonality moments and are independent by degree and node count.

## 3. Live arithmetic: the axis removes the extra early input

Take the quartic on the four early labels other than \(\beta\) as an actual supported \(E_4\) input, using the [coprime supported quadratics](../sdirk-eight-eight-zero-early-repeat/README.md#2-live-arithmetic-a-paid-quartic-with-a-repeated-early-clock). Subtract its value at \(\beta\) times \(\mathbf e_i\in F_4\subset E_4\). The supported column retains its quartic scalar trace, but now its actual input vanishes on **all five** early physical zeros. Hence its actual \(A'\) reads vanish on the four early labels under consideration, and the first rear read is diagonal. On those seven labels its pure primitive discrepancy is in the same three Legendre profiles as in the [supported quartic proof](../sdirk-eight-seven-zero-supported-quartic/README.md). The three live rear cardinal ratios also agree by section 1. The paid determinant and \(H,Q\) Bézout contradiction apply, with no characteristic-zero arithmetic. Without the pure axis subtraction, no such chronological diagonal at the first rear row could be assumed.

## 4. Silent and star: a finite forward cubic and diagonal quartic

Let \(\ell\) be the other of \(a,b\) than \(\beta\). The values \(JZ_2(\ell),JZ_3(\ell)\) are not both zero by the invertible first-two matrix. Since their pure errors at \(\ell\) lie on the \(L_{4,D}\) line, \(L_{4,D}(\ell)\ne0\). Form the supported cubic
\[
  S(T)=JZ_3(\ell) Z_2(T)-JZ_2(\ell) Z_3(T).
\]
Its error at \(\ell\) vanishes, so its entire pure primitive error restricts to zero on the seven other labels. The actual read at \(c\) is diagonal because both earlier physical zero inputs vanish, including at \(\beta\). Hence \(S(c)-JS(c)=0\). The same polynomial vanishes at \(\ell\), so the third clock satisfies the independent degree-at-most-three polynomial
\[
             R_\ell(c)=0,\qquad R_\ell(T)=\frac{S(T)-JS(T)}{T-\ell}.
\]
Then \(C_3(c;D)\) has degree at most four in \(D\) by the exact front formula, fixing a second small algebraic extension at the good reductions below.

Only \(\ell,c\) of the four early supported labels are fixed, so put \(P_2=(T-d)(T-e)\) for the other two. In the silent-eighth case \(H(v)=0\), \(s=D-1,t=s-v,r=s-2v\), \(\kappa=1+2v-v^2\), and set \(M=(T-\ell)(T-c)(T-s)(T-t)(T-r)\). Use the three masks
\[
 M,\quad \kappa M/(T-t)-M/(T-s),\quad M/(T-r).
\]
Their products with \(P_2\) have zero ordinary mean by nodal precision, the two singleton live cardinal ratio, and ordinary silence at \(r\). In the live star set \(m=D-2,\ M_0=(T-\ell)(T-c)\). The [gap-free star cancellation](../sdirk-eight-eight-zero-early-repeat/README.md#3-exact-characteristic-zero-silent-and-star-exclusions) instead gives masks
\[
 M_0(T-s),\quad M_0(T-s)(T-m)^2,\quad M_0((T-m)^2-2).
\]
Again no orientation is fixed or discarded. The three ordinary equations on the three coefficients of monic \(P_2\) annul the three-by-three determinant of their first three moments, including any recovery-pivot drop.

| Phase | \(\beta=a\) | \(\beta=b\) |
|---|---:|---:|
| Silent eighth | \((139,80)\) | \((83,26)\) |
| Live star | \((79,36)\) | \((103,73)\) |

The pairs are \((p,z_0)\), a prime and simple primitive residue for the exact degree-18 field of the silent gap or the degree-six gap-free star field, with primitive \(u+b+2v\) or \(u+b\). The replay verifies the exact degree, irreducibility and recovered coordinates. At each reduction \(R_\ell\) has degree three with unit lead and three simple, distinct roots, all inspected. At each such root \(C_3(c;D)\) has degree four with unit lead, and its gcd with the ordinary determinant is constant. The last gcd covers all algebraic values of \(D\), not just prime-field roots. Since a simple primitive residue lifts to an embedding of the exact field, and the two unit leads force successive integrality of \(c,D\) in any valuation extension, the constant gcd rules out the original characteristic-zero candidates. The four computations are not claims of finite-characteristic nonexistence.

## 5. Replay and remaining scope

Run `python check_silent_pure_root.py ghost` and `python check_silent_pure_root.py star` with SymPy 1.14 and Python-flint 0.8. The tests use the four fixed simple embeddings, not a residue search. The [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightEightZeroSilentPureRoot.lean) checks the one-line primitive cancellation and the homogeneous monic-tail determinant; the pure axis, chronological ingress and exact number-field steps are the mathematical proof. In the eight-distinct chart an affine numerator root at an actual coordinate must now have a **nonzero ordinary weight**. A constant numerator, an affine root not equal to a physical zero clock, and all general ten-stage questions remain open here.
