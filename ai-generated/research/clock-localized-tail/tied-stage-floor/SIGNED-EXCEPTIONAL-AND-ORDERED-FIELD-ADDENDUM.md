# Sharper exceptional row count and ordered-field scope

This addendum leaves the two sealed parent files unchanged. Use their notation with \(p=4h-1\), nonsingular triangular stage count \(s=2h^2+e\), and \(D_\pm\) the number of positive weights minus negative weights on the strict positive or strict negative quadratic-residual sector, respectively. Allow both zero weights and zero stage residuals. Put
\[
 \kappa\coloneqq\dim(E_{2h-1}\cap\ker B),\qquad
 z_{+,0}\coloneqq\#\{i:b_i>0,\ g_i=0\}.
\]
On \(E_{2h-1}\) the quadratic form of \(B\) is nonnegative. A vector in this subspace with zero coordinates on all positive slots can be nonnegative only if its negative slots are also zero. Hence projection onto the positive slots has kernel exactly \(E_{2h-1}\cap\ker B\), giving \(n_+(B)\ge h^2+h-\kappa\). The pure quadratic form of \(BG\) still gives \(n_\pm(BG)\le h^2+e\). Direct bookkeeping of signs gives \(n_+(B)-n_\mp(BG)=z_{+,0}+D_\pm\), so
\[
                 \boxed{\kappa+z_{+,0}+D_\pm\ \ge h-e}
\]
for each sign. In particular only the actual intersection with silent coordinates, not all silent stages, is charged; negative weights with the indicated strict residual sign cannot be ignored. No stage increment follows if the signed or exceptional census is already large enough.

All sign and weighted-support results in the parent apply over any ordered field, with the same proofs. The integrals are formal rational polynomial moments. Positivity of the rational Hilbert matrix follows over an ordered field because that matrix has a rational \(LDL^\top\) factorization with positive rational diagonal: positivity over the reals gives positive leading principal minors, which lie in \(\mathbb Q\), and the rational elimination pivots are their ratios. Every ordered-field embedding of \(\mathbb Q\) preserves their signs. The row dimension comparisons use only strict coordinate signs and elementary linear algebra. A threshold between two distinct actual residual values in the ordering argument can be chosen as their midpoint in the given field. No completeness, analytic integration over that field, or real-closedness is needed.
