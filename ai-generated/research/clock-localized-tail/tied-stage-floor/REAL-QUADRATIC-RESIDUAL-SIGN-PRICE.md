# Real sign prices for the quadratic stage residual

Let \(A,\mathbf b\) be a real order-\(p\) RK tableau. Write \(\mathbf c\coloneqq A\mathbf1\), and use the genuine rooted spaces \(E_j,F_j\) from trees of size at most \(j+1\), with \(F_j\) the zero-profile space. Set
\[
 \mathbf g\coloneqq A\mathbf c-\tfrac12\mathbf c^{\odot2},
 \qquad B\coloneqq\operatorname{diag}(\mathbf b),
 \qquad G\coloneqq\operatorname{diag}(\mathbf g).
\]
Thus \(\mathbf g\) is the stage residual \(\mathbf Q([\bullet])\). It has degree two as a stage-derivative profile, and \(G E_j\subseteq F_{j+2}\) by rooted sum. Nothing below presumes positive weights, distinct nodes, a repeated fibre, or Gaussian output.

## Pure multiplication on the actual weighted rows

Let \(L\coloneqq\{i:b_i\ne0\}\) and \(w\coloneqq |L|\). Denote actual restrictions to \(L\) by \(E_j|_L,F_j|_L\). The quadrature tests give at least
\[
 h_j\coloneqq\min(j+1,p-j)
\]
scalar directions modulo \(F_j|_L\): pair with the genuine rows of low-degree \(\mathbf b\odot\mathbf c^{\odot \ell}\) and use the positive smaller Hilbert Gram. All ordinary pairings depend only on these weighted coordinates. If \(g_i\ne0\) for every \(i\in L\), multiplication by \(G|_L\) is invertible on the weighted coordinate space and maps \(E_{j-2}|_L\) into \(F_j|_L\). With
\[
 T_j\coloneqq
 \sum_{\substack{0\le i\le j\\i\equiv j\ (2)}} h_i,\qquad T_j\coloneqq0\quad(j<0),
\]
it follows that \(\dim(E_j|_L)\ge T_j\) through degree \(p-1\). Consequently \(w\ge Q(p)\coloneqq\max(T_{p-1},T_{p-2})\). This does **not** assume triangularity: an actual diagonal pure multiplier has replaced the nonsingular triangular commutator on this restricted space. In particular if a nonsingular stage-floor method has a zero output weight, some actual **weighted** stage must have \(g_i=0\); merely having a zero residual at a silent stage does not suffice.

In the nonsingular lower triangular class, with no hypothesis on zero values of \(\mathbf g\), the same \(T_j\) is a lower bound on \(\dim E_j\) on the whole stage space, by the invertible commutator \(CA-AC-A^2\), \(C\coloneqq\operatorname{diag}(\mathbf c)\).

## At odd orders \(p=4h-1\)

Let \(h\ge1\). Then \(Q(p)=2h^2\), and the relevant partial parity sums are
\[
 T_{2h-1}=h^2+h,\qquad T_{2h-2}=h^2,\qquad T_{2h-3}=h^2-h .
\]
For \(h=1\) the last is the zero space. The three facts below use ordinary pairings and exactly budgeted rooted sums:
1. The form with diagonal \(\mathbf b\) is nonnegative on \(E_{2h-1}\); its value at a vector twice is the integral of the square of its scalar representative. The degree cost \(2(2h-1)=p-1\) is paid.
2. The form with diagonal \(\mathbf b\odot\mathbf g\) is zero on \(E_{2h-2}\times E_{2h-2}\), by cost \(2(2h-2)+2=p-1\).
3. The form with diagonal \(\mathbf b\odot\mathbf g^{\odot2}\) is zero on \(E_{2h-3}\times E_{2h-3}\), by cost \(2(2h-3)+4=p-1\) whenever that space is nonzero.

The first square is independent of the choice of scalar representative: two representatives of an identical numerical vector have the same positive-norm pairing by the ordinary order. The second and third assertions use pure rooted products, not a positive sign assumption. A diagonal form nonnegative on a subspace of dimension \(u\) needs at least \(u\) positive or zero diagonal slots: otherwise the subspace meets the strictly negative coordinate subspace. A diagonal form zero on that subspace has at most \(s-u\) strictly positive slots and at most \(s-u\) strictly negative slots. Apply these facts either to the full space or to the actual weighted coordinates, as indicated below.

**Every near-floor nonsingular tableau, including zeros.** Write \(s=2h^2+e\) and \(z_b\coloneqq\#\{i:b_i=0\}\). The first form forces \(n_+(B)\ge h^2+h-z_b\). The second gives \(n_\pm(BG)\le h^2+e\). Since the positive \(b_i\)'s with \(g_i>0\) count towards \(n_+(BG)\), and those with \(g_i<0\) towards \(n_-(BG)\), we obtain both
\[
 \begin{split}
 z_b+\#\{i:b_i>0,\ g_i\le0\}&\ge h-e,\\
 z_b+\#\{i:b_i>0,\ g_i\ge0\}&\ge h-e .
 \end{split}                                                       \tag{1}
\]
Within each line the two counted sets are disjoint; the two lines cannot be added as independent stage charges. It is an unconditional exceptional-row census for real nonsingular DIRK and strict SDIRK at these orders.

**No zero quadratic residual on weighted sites.** Work on those \(w\) actual weighted coordinates, and write \(e_w\coloneqq w-2h^2\ge0\). The first and third forms have the same inertia, as \(g_i^2>0\) on that space. They imply
\[
 h^2+h\le n_+(B|_L)\le h^2+h+e_w,\qquad
 h^2-h\le n_-(B|_L)\le h^2-h+e_w .
\]
For each of the two strict residual signs, define the actual signed count
\[
 D_{\pm}\coloneqq
 \#\{i:b_i>0,\ \pm g_i>0\}-\#\{i:b_i<0,\ \pm g_i>0\}.
\]
The second form gives \(n_\pm((BG)|_L)\le h^2+e_w\). Subtracting respectively the negative and positive inertia counts from \(n_+(B|_L)\) yields
\[
                         D_+\ge h-e_w,\qquad D_-\ge h-e_w.           \tag{2}
\]
In particular \(w\ge 2h^2+h-\min(D_+,D_-)\), and if every weighted residual is strictly of one sign then \(w\ge2h^2+h\). This same-sign lower bound is valid even for nontriangular RK. It excludes the corresponding entire architecture at the quadratic floor at \(p=7,11,15,19\), with stage premiums \(2,3,4,5\); it does not exclude both-sign or zero-residual architectures.

At the exact quadratic floor under the same nonzero-on-weighted hypothesis all stages have nonzero weights, \(n_+(B)=h^2+h\), \(n_-(B)=h^2-h\), \(n_+(BG)=n_-(BG)=h^2\) and \(D_+=D_-=h\). Indeed the two inertia counts for \(BG\) add to \(2h^2\), and (2)'s two signed counts add to \(2h\).

## Ordered sign distribution, not just a total

Still assume no weighted \(g_i=0\). The pure multiplier \(\mathbf g\odot(\mathbf g-\tau\mathbf1)\), for any real \(\tau\), costs at most four. Its weighted diagonal form is zero on \(E_{2h-3}|_L\) by the same budget as item 3 above. For \(\tau>0\) not a physical weighted residual, the sign of the \(i\)-th diagonal compared with \(b_i\) flips exactly at \(0<g_i<\tau\). For \(\tau<0\), it flips exactly at \(\tau<g_i<0\). Thus for every cumulative segment of either strict sign taken outwards from zero, if \(D\) is its number of positive weights minus negative weights,
\[
             -e_w\le D\le 2h+e_w .
\]
Indeed the positive inertia of the new form is \(n_+(B|_L)-D\) and lies between \(h^2-h\) and \(h^2+h+e_w\). Take thresholds in gaps between actual distinct residual values; a repeated value is counted as a whole. At the floor the cumulative count never drops below zero or exceeds \(2h\), and ends at \(h\) on each side. For \(h=1\) the zero test space gives the same inequalities by the size of the weighted space alone. The ordering is on actual residual values, not clock labels, so this is also a test for singleton/no-repeat clock charts.

More generally any true pure stage multiplier of degree \(d\) induces a diagonal form zero on \(E_j\times E_j\) when \(2j+d\le p-1\). The present improvement uses the specific related multipliers \(\mathbf g,\mathbf g^{\odot2},\mathbf g\odot(\mathbf g-\tau\mathbf1)\), whose inertia comparisons are exact over the reals. No unrestricted stage minimum is asserted to rise: the theorem forces specific sign changes or exceptional rows, and raises the count on the strict one-sign subfamily.
