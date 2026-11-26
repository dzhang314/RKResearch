# Integral domains and uniqueness of smallest same-diagonal tableaux

Let \(R\) be a nonzero commutative ring and let \(\gamma\in R\). A
complete rooted-tree series is the function assigning to each rooted
tree \(t\) the scalar \(\mathbf b\cdot\boldsymbol{\Phi}_t(A)\). Only
triangular tableaux with prescribed common diagonal \(\gamma\) are
considered here.

**Theorem.** Every nonzero complete rooted-tree series that has such a
realization over \(R\) has a unique smallest realization up to stage
permutation if and only if \(R\) is an integral domain. The property
quantifies over all realizable series of the fixed diagonal, not over
the smallest realization of one particular series.

Suppose first that \(R\) is an integral domain. Regard a tableau over
\(R\) as a tableau over its fraction field. The [field-level canonical
reduction](PROOF.md) merges stages with identical complete profiles,
sums the matrix taps into each resulting class, sums the output
weights, and discards classes that cannot reach a nonzero output
weight. These operations use only entries of \(R\) and addition.
Equality of profiles and detection of zeros are unchanged in the
fraction field. Ordering the classes by their earliest members
preserves triangularity and the prescribed diagonal, so the
fraction-field minimum already has a realization over \(R\).
Conversely, a smaller realization over \(R\) would contradict its
minimality over the fraction field. Any two minimum realizations over
\(R\) are therefore permutation equivalent over the fraction field,
and the same coefficient identities hold in \(R\).

Now suppose that \(R\) has nonzero elements \(a,d\) with \(ad=0\).
Consider two tableaux with the same matrix and different output
weights:
\[
A\coloneqq
\begin{pmatrix}\gamma&0\\a&\gamma\end{pmatrix},
\qquad
\mathbf b\coloneqq(0,1),
\qquad
\mathbf b'\coloneqq(-d,1+d).
\]
Modulo the ideal \((a)\), the matrix is \(\gamma I\). Unary extension
and rooted sum therefore preserve the equality of the two stage
coordinates of every tree, starting from the leaf
\(\boldsymbol{\Phi}_\bullet(A)=\mathbf 1\). Their difference lies in
\((a)\) over \(R\), so multiplication by \(d\) annihilates it. Thus
\(\mathbf b\cdot\boldsymbol{\Phi}_t(A)=
\mathbf b'\cdot\boldsymbol{\Phi}_t(A)\) for every \(t\).
The common leaf weight is \(1\); a one-stage realization of this
series must therefore have weight \(1\). Its weight for
\([\bullet]\) would be \(\gamma\), whereas the common two-stage value
is \(\gamma+a\ne\gamma\). Both displayed realizations are smallest.
Swapping the stages does not preserve \(A\), since \(a\ne0\), and the
identity permutation does not match the output weights.

For example, take \(a=7,\ d=11,\ \gamma=0\) in \(\mathbb Z/77\mathbb Z\).
The two weight vectors are \((0,1)\) and \((66,12)\), and their
complete series has minimum width two but no unique minimum. Over
\(\mathbb Z/49\mathbb Z\), the same construction with \(a=d=7\) has
minimum width two, while its series over the only residue field,
\(\mathbb F_7\), has minimum width one. Thus the maximum of the
residue-field minimum widths need not recover the ring minimum.

For an integral domain, the same descent applies to the
[filtered context ranks](FILTERED-CONTEXT-RANKS.md): use rank over the
fraction field, or equivalently the largest size of a nonzero minor
over \(R\). These ranks recover the support counts of the canonical
tableau over \(R\). No claim here uses only the first \(p\) rooted-tree
coefficients, and no finite-order stage bound follows directly.
