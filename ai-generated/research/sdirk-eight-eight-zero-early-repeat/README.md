# Seven zero labels with an early duplicate

Let \(A,\mathbf b\) be a strict ten-stage SDIRK tableau of ordinary order at least eight over a field, with common diagonal \(\gamma\ne0\). Let \(\mathbf c=A\mathbf1\) and \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Assume exactly eight physical entries of \(\mathbf g\) vanish and the number of distinct clock labels among those eight entries is seven. Suppose the two off rows are the individually silent physical rows 1 and 2 at distinct clocks, as required in characteristic zero by the [low-label census](../sdirk-eight-eight-zero-low-labels/README.md). This packet concerns the unique doubled label when **both its occurrences are among physical rows 3 through 7** and the reflected second ratio is nonzero.

**Result.** This chart is impossible in characteristic zero. The live reflected arithmetic part is impossible over every field of characteristic zero or greater than seven under the stated literal support assumptions. A duplicate connecting an early row with a rear row is not in scope; in particular a literal rear weight ratio cannot be substituted for a grouped cardinal ratio there.

## 1. Physical-to-grouped ingress

Normalize \(A'=A/\gamma\), \(\mathbf x=\mathbf c/\gamma\), \(D=1/\gamma\), and \(C'=\operatorname{diag}(\mathbf x)\). Let \(U=\ker\operatorname{diag}(\mathbf g)\). Denote the four distinct early zero labels by \(a,b,c,e\), using the first-new order for \(a,b,c\). The [supported forward gates](../sdirk-eight-eight-zero-low-labels/README.md#1-literal-placements-and-exact-profile-gates) give
\[
 a=1+2u,\quad Q(u)=4u^3-12u^2+3u+2=0,\quad
 b^2-(2u+4)b+1+2u=0,\quad C_3(c;D)=0.
\]
These are first-new, not necessarily consecutive, labels. In particular each is distinct from the three actual rear labels \(s=x_{10},t=x_9,r=x_8\). The explicit quadratic \(C_3\) is regenerated from the two supported read equations in the replay. In the notation \(J\) for formal integration from zero, take \(Z_2(T)=(T-a)(T-b)\) and \(Z_3=T Z_2\); choose \(\alpha,\beta\) so that \(J(\alpha Z_2+\beta Z_3)(a,b)=-L_{4,D}(a,b)\). The read determinant is \(a^2b^2(a-b)^3/24\); the quadratic is
\[
 C_3(T;D)=\frac{\alpha(Z_2-JZ_2)+\beta(Z_3-JZ_3)-L_{4,D}}{Z_2}.
\]

Let \(P_4=(T-a)(T-b)(T-c)(T-e)\), \(P_7=P_4(T-s)(T-t)(T-r)\), and \(I_D(T^j)=D^j/(j+1)\). Write \(B(x)=I_D(P_7/(T-x))\). The ordinary weight on each label is a sum over its physical occurrences, so \(B(x)=P'_7(x)\sum_{i:x_i=x}b_i\). Ordinary precision gives \(I_D(P_7)=0\).

The pure reverse quadratic row \(\mathbf z^{\mathsf T}\) is supported on \(U\), and its first six grouped moments vanish. Its grouped row is nonzero since the terminal pure coordinate is nonzero and at a singleton. Consequently
\[
 P'_7(x)\sum_{i:x_i=x}z_i=\Theta,\qquad \Theta\ne0,
\]
at every label, by the rank-six Vandermonde system. This makes the rear cardinal ratios valid **only** because the three rear labels are singletons. Write \(s=D-1,\ t=s-v,\ \kappa=1+2v-v^2\ne0\). Then \(B(s)=\kappa B(t)\), and
\[
\begin{array}{c|c|c}
\text{rear phase}&r&\text{extra gates}\\ \hline
\text{silent eighth}&s-2v&H(v)=0,\ B(r)=0\\
\text{live arithmetic}&s-2v&\kappa_3 B(r)=B(s),\ H(v)\kappa_3=-\kappa Q(v)\\
\text{live star}&s-(2-v)&B(t)=B(r).
\end{array}
\]
Here \(H(v)=v^3-4v^2-v+2\); these are the [literal last-three phase gates](../sdirk-eight-seven-zero-pure-distinct/README.md#2-rear-cardinal-rows-and-the-arithmetic-compatibility-sextic). The table uses no arbitrary reflection of silent rows.

## 2. Live arithmetic: a paid quartic with a repeated early clock

The [paid rank census](../sdirk-eight-seven-eight-zero-census/README.md) gives \(\dim F_5=6\), \(\dim GE_3=2\), and \(GE_3\subset F_5\) supported on the two off coordinates, with \(G=\operatorname{diag}(\mathbf g)\). Thus \(\dim(F_5|_U)=4\). Let \(\delta\) be the difference of the two physical coordinate rows of the doubled clock. This row **does not lie in \(W_2\)**. In fact an element of \(W_2\) is a sum of \(\mathbf b^{\mathsf T}q(C')\) for a scalar polynomial \(q\) of degree at most two and a multiple of \(\mathbf z^{\mathsf T}\). If it equals \(\delta\), testing the first three scalar moments makes the \(q\) part zero: the three-by-three Hilbert moment form has nonzero determinant (only the primes \(2,3,5\) enter, and \(D\ne0\)). The remaining pure multiple has zero grouped row only if it is zero, by the nonzero \(\Theta\) above. But \(\delta\ne0\). At saturation \(F_5=\operatorname{Ann}W_2\), so \(\delta\) gives an independent linear condition on \(F_5|_U\), and
\[
 F_5|_U\cap\ker\delta
 =\langle L_{3,D},L_{4,D},L_{5,D}\rangle|_U .
\]
Each right-hand profile belongs to the intersection by paid moments; their independence follows from the seven distinct labels and unit leading coefficients \(20,70,252\).

Every degree-at-most-four polynomial on \(U\) has an actual supported \(E_4\) representative. The two supported quadratic profiles \(P_0=2T-1-T^2/2\), \(P_{\rm off}=(T-1)(T-1-u)\) are coprime, because \(P_0\) is the nonzero normalized residual at each of the two distinct off clocks. Their products by \(1,T,T^2\) span every polynomial of degree at most four (the only relation is the scalar-multiple commutation relation). In particular choose the actual supported \(P_4\) column. All five early physical inputs vanish: four distinct roots and their one repeated occurrence. Therefore its actual \(A'\) read vanishes at both copies, and its pure primitive discrepancy has equal values on them. The discrepancy belongs to the three-dimensional intersection just proved. At row 8 its actual read is the diagonal value, since all earlier inputs vanish and the diagonal is one.

The [supported quartic determinant](../sdirk-eight-seven-zero-supported-quartic/README.md#3-rear-cardinal-moments-and-a-paid-contradiction) now applies without a distinct-physical-row hypothesis. Indeed it needs exactly the primitive correction in the three Legendre profiles, vanishing at the four distinct early nodes, the diagonal read at row 8, and the three singleton cardinal ratios. In reflected coordinate \(Y=D-T\), the actual read is therefore \([1+\nu(Y-y_r)] P_4(D-Y)\) on the support. The first two scalar primitive moments give \(\rho Q(v)=H(v)\), where \(\rho=B(r)/B(t)\ne0\), while the literal relation gives \(\rho Q(v)=-H(v)\). The exact \(H,Q\) Bézout identity with value \(64\) gives the contradiction. This does not require projecting the sixth-degree arithmetic polynomial.

## 3. Exact characteristic-zero silent and star exclusions

Put \(F=(T-a)(T-b)(T-c)\), so \(P_4=F(T-e)\). The three linear conditions in the unknown constant term \(-e\) are always of the form \(I_D((T-e)M_i)=0\). For the silent eighth, set \(M=F(T-s)(T-t)(T-r)\). The three masks are
\[
 M,\quad \kappa M/(T-t)-M/(T-s),\quad M/(T-r).
\]
They are just the ordinary mean, the terminal/second cardinal equation, and the physical silence of the singleton eighth row.

For a live star put \(m=D-2\), \(d=v-1\), hence \(t,r=m\mp d\), \(s=m+1\), and \(\kappa=2-d^2\). First \(B(t)=B(r)\) gives \(I_D(P_4(T-s))=0\); ordinary exactness then gives \(I_D(P_4(T-s)(T-m)^2)=0\). Finally \(B(s)=\kappa B(t)\), after using the first equation, gives
\[
 (1-d^2) I_D(P_4((T-m)^2-2))=0.
\]
The factor \(1-d^2\) cannot vanish, since one of \(t,r\) would equal \(s\). Thus the three masks are \(F(T-s),\,F(T-s)(T-m)^2,\,F((T-m)^2-2)\). This discards no orientation and requires no integration outside the paid ordinary range.

In each branch all three two-column minors of the rows \((I_D(M_i),I_D(TM_i))\) vanish, also when one or all ordinary moments are zero. Work over the exact initial field \(\mathbb Q(u,b)\), of degree six with primitive element \(u+b\); in the silent branch adjoin the ghost root \(v\) to get the degree-18 field with primitive element \(u+b+2v\). The replay verifies irreducibility, the inverse coordinate maps, and the clock equations. Thus these abstract field identities apply regardless of the chosen embeddings or root orientations.

For \(C_3=\ell_2 c^2+\ell_1 c+\ell_0\) and \(\ell_2\ne0\), pass to \(L=\ell_2 c\), satisfying \(L^2+\ell_1L+\ell_2\ell_0=0\). For each minor, clear its powers of \(\ell_2\) and reduce to \(p+qL\); its vanishing forces the norm \(p^2-pq\ell_1+q^2\ell_2\ell_0\) to vanish. This is valid even when the quadratic splits or has a repeated root. After stripping only the factors of \(\ell_2\), the exact norm degrees are \(32,32,28\) in the silent branch and \(30,28,32\) in the star branch. Both exact common gcds are \(D^4\), forbidden by \(D\ne0\). At \(\ell_2=0\), one has \(\ell_1\ne0\) by exact gcd, so substitute \(c=-\ell_0/\ell_1\) into the same minors after clearing the powers of \(\ell_1\). The common gcd with \(\ell_2\) is constant in each branch. No uncontrolled leading or moment pivot is left.

## 4. Replay and scope

Run `python check_early_repeat.py ghost` and `python check_early_repeat.py star` with SymPy 1.14 and Python-flint 0.8. The checks are exact over number fields, not finite grid tests. The [Lean companion](../../lean/RKCert/Research/SDIRKEightEightZeroEarlyRepeat.lean) checks the linear-tail minors, star cardinal factor, and monic quadratic norm gate, with theorem types audited by `proof-audit.lean`. The actual supported flags, chronology, and exact number-field checks are the source proof, not an unconditional native rooted-tableau theorem. No full ten-stage lower bound follows from this one duplicate placement.
