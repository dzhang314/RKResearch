# The reflected terminal weight has to be a unit

This is a necessary arithmetic gate, not a construction and not a DIRK stage-count lower bound.

Let \(R\) be a nonzero commutative ring with \(10!\) invertible. Consider a degree-nine scalar quadrature realized by a literal projected DIRK10 chart. Apart from the old origin and at most four merged scalar ports, all its contributing nodes are reflected physical nonports; there are no other scalar output weights. The first reflected nonport has clock \(1\). Every other nonport clock \(x_i\) satisfies \(1-x_i\in R^\times\); pairwise differences elsewhere need not be units. Write \(\mathbf w,\mathbf y=\mathbf1-\mathbf x\) for the reflected weights and clocks.

Assume that the actual nonport rows of the reverse block \(K\) are triangular on the reflected physical nonports and do not read a port column. This is the literal chronology in which an earlier retained port cannot depend on an unmerged future stage. Assume the low reverse actions on these rows are
\[
   K\mathbf w=\mathbf w\odot\mathbf y,\qquad
   K(\mathbf w\odot\mathbf y)=\mathbf w\odot\mathbf y^2/2.
\]
No condition on the reverse actions in the port rows is required. Then the weight of the reflected terminal node at \(1\) is a unit in \(R\). In particular it has no numerator prime outside \(\{2,3,5,7\}\) over \(\mathbb Z[1/210]\).

## Proof

If this weight were a nonunit, reduce at a maximal ideal containing it to a residue field \(k\). The factorial assumption puts \(1,\ldots,10\) in \(k^\times\), and each proper nonport \(y_i=1-x_i\) is still nonzero. If there is any nonzero reduced nonport weight, take the first. All earlier nonport weights are zero, so the two displayed leading actions force its diagonal to equal both \(y_i\) and \(y_i/2\). This contradicts \(y_i\ne0\). Thus all nonport weights vanish.

The remaining reduced scalar quadrature is supported on at most five sites: the origin and at most four ports. Combine any coincident nodes and delete zero weights. A degree-nine scalar rule over \(k\) cannot be supported on at most four sites. Indeed its moment matrix
\[
      H_{ij}=\frac{1}{i+j+1},\qquad 0\le i,j\le4,
\]
would have rank at most four by its evaluation factorization, whereas it is invertible. One may use its certified integer inverse [below](#exact-replay).

If precisely five sites remain, \(0\) is one of them. Their monic nodal hull \(P\) must satisfy \(\int_0^1 X^jP(X)\,dX=0\) for \(j=0,\ldots,4\) by the degree-nine condition. Here the integral means the exact scalar moment functional. Invertibility of \(H\) makes the monic degree-five polynomial with those five orthogonalities unique. It is
\[
   P(X)=\frac{252X^5-630X^4+560X^3-210X^2+30X-1}{252},
\]
whose constant term \(-1/252\) is a unit, contradicting the origin root. This excludes all residue fields at which the terminal weight could vanish, proving the asserted unit.

The reduction does not require positivity, a field structure on \(R\) itself, or pairwise separations among the quadrature nodes. It uses the reverse leading actions, the stated chronology, and the bounded support of the remaining port weights. It does not cover arbitrary tableaux with different topologies or free extra output weights.

## Exact replay

    python3 -B check.py

The replay checks the integer inverse after clearing the common moment denominator 2520, and all five orthogonalities. The same identities are also present in the dependency-free Lean arithmetic receipt. The maximal-ideal and rank argument above is mathematical rather than a native theorem in this packet.
