# The weighted stage bound starts at effective order eleven

**Theorem.** Let \(m\ge0\), \(r\ge11\), and let the coefficient field have \((m+r)!\ne0\). If an actual output row of a strictly lower triangular tableau is exact on all rooted stage profiles through tree size \(r\) for
\[
          \ell_m(P)\coloneqq\frac1{m!}\int_0^1(1-X)^mP(X)\,dX,
\]
then its last nonzero physical position is at least \(\lceil3r/2\rceil\). The resulting ordinary explicit stage floor over any nonzero commutative unital coefficient ring is the same, by paid residue-field specialization.

This lowers the threshold in the [odd proof](06-ODD-EXPLICIT-STAGE-BOUND.md) and its [weighted extension](07-WEIGHTED-DETECTOR-STAGE-BOUND.md). The arguments for all larger thresholds are unchanged. The extension to \(r=11\) and \(r=12\) uses three precise observations below, not arithmetic about individual tableaux.

## The penultimate tap already vanishes at budget five

Use the notation of the [penultimate-tap theorem](../../research/clock-localized-tail/PENULTIMATE-PAID-TAP.md). The weighted exact word tests and the purity of the commutator are the only scalar assumptions. Equations (2) through (6) of that file are valid in the complete terminal path for any \(L\ge4\) wherever the indicated indices exist: the suffix basis, reciprocal sequence, and one- and two-clock-factor identities were proved directly inside their word budgets.

First consider a late vector with nonzero top tap at budget \(L=5\). The prior proof through its equation (6) already gives \(r_2=0\) in the reciprocal sequence, so with \(a=\mu_4/\mu_5\) one has \(\mu_3=a^2\mu_5\). The next-degree late space has budget \(L'=4\); it contains an actual top-visible vector, namely \(A\mathbf v\). Its last and penultimate rows are proportional on that whole space, for the following reason.

At next degree, every vector with nonzero top tap starts at the same first possible physical row and produces the same next pair of physical \(Y\)-clocks, say \(y,y'\). If \(y\ne y'\), equation (6) at \(L'=4,j=2,i=1\) forces its reciprocal \(r_2=0\). It gives the quadratic relation between the last three taps, and hence proportionality on the full late space by the finite-field polynomial and linear-kernel argument in the earlier proof. If \(y=y'\), the first adjacent subdiagonal coefficient of \(Y\) in its two-dimensional chronological quotient must be zero, since \(Y\) is diagonalizable. Equation (2) at \(L'=4\) makes this coefficient
\[
                       m+4-y\,\frac{\mu'_3}{\mu'_4}.
\]
Here \(m+4\) is a paid unit, so \(y\ne0\), and the ratio of the penultimate to the top row is uniformly \((m+4)/y\) whenever the top read is nonzero. This directly implies proportionality on the whole late subspace: a vector in the kernel of the top read can be translated by a fixed top-visible vector, and the equation is linear. In either clock case the ratio is fixed by the actual vector \(A\mathbf v\), so it equals \(a\).

Now apply this next-level proportionality to the other actual vector \((Y-y_0I)\mathbf v\), where \(y_0\) is the first \(Y\)-clock at the original degree. The two relevant paid reads are
\[
 \begin{split}
 \mu'_3((Y-y_0I)\mathbf v)&=(m+4)\mu_4-y_0\mu_3,\\
 \mu'_4((Y-y_0I)\mathbf v)&=(m+5)\mu_5-y_0\mu_4.
 \end{split}
\]
Substitute \(\mu_4=a\mu_5\) and \(\mu_3=a^2\mu_5\), then use the common ratio. This yields \(a\mu_5=0\), so \(\mu_4=0\). Consequently the penultimate row is zero on the entire original late subspace if its top row is nonzero there. If desired it also follows that \(\mu_2,\mu_3\) are zero there: equation (2) now disallows all equal adjacencies, so equation (6) forces \(r_3=0\) as well.

It remains to exclude a late vector with \(\mu_5=0\) and \(\mu_4\ne0\). Use the one-omitted-row argument of that file on physical suffix ordinals \(0,\ldots,5\). There are at most two contributing paths of four edges; if two, their omitted rows are adjacent, and both are endpoints of an actual missing adjacent edge. All common rows have \(Y\)-clock zero by the five-cost words with one clock factor. With only one possible active row, at least one of the four insertion ordinals in a three-edge path cannot see that active row, because a path ordinal can move by at most two relative to its physical ordinal. The same is true with two adjacent active rows unless they are physical ordinals 2 and 3: an adjacent pair \(u,u+1\) can only be seen by insertion ordinals in \([u-2,u+1]\), and only \(u=2\) covers all of \(0,1,2,3\). In this last configuration use the first insertion ordinal. The only possible active starting position for a three-edge path is physical 2, which forces the literal path \(2\to3\to4\to5\); the edge \(2\to3\) is exactly the missing edge. Thus its response is again zero. The exact paid response is instead a nonzero integer multiple of \(\mu_4\) in every selected ordinal, a contradiction.

This proves the needed penultimate vanishing for all \(L\ge5\), without assuming clock separation or choosing a particular order-five coefficient field.

## Separation of the early prefix is already a dense decoder

The autonomous early-prefix argument in MAXIMAL-ODD-CLOCK-DELAY.md and be02d3f6… actually needs no separate construction of an ordinary output \(\ell_0\). If all positive weighted taps factor on \(E_d\) through the first \(2d\) physical coordinates, the available simultaneous functionals \(\ell_{m+1},\ldots,\ell_{m+d}\), and the literal origin, separate the numerical stage data from any nonzero polynomial alias through degree \(d\). Indeed a putative alias is \(XQ\), and the weighted \(X(1-X)^{m+1}\) moment Gram kills \(Q\). Its factorial budget is \((m+2d+1)!\).

Separation means the assignment from a numerical vector to its exact polynomial is a well-defined linear map on the actual rooted subspace of the prefix. Extend it linearly to all \(2d\) coordinates. This is an exact dense derivative decoder through tree size \(d+1\): its coefficients are polynomials in \(X\), and on each numerical Butcher weight vector it gives the required exact profile \(|t|X^{|t|-1}/t!\). The published dense-width theorem in RKResearch 10c21eac091c2976187119fb4111d05679db5de6, ai-generated/research/erk-dense-width, requires at least \(2(d+1)-1\) rows for such a chart for every \(d\ge5\). That contradicts \(2d\) rows directly. In particular the early-prefix proof does not depend on obtaining the unrestricted size-six pure floor from an ordinary order-five output.

## The old weighted floor suffices at effective size nine

For the two short-prefix contradictions in the detector argument, the new read or next-tap read keeps exactness through size \(2d\), or through size \(2d-1\) in the augmented branch. It would be supported within \(2d+1\) rows. One may use the older paid weighted baseline
\[
                         n\ge \lceil 3a/2\rceil-2
\]
for weighted effective size \(a\ge5\), proved as inequality (1) before the extra pure fifth-degree gain in 01-PAID-GRADE-FIVE-SURPLUS.md. At \(d=5\) the smaller retained size is \(2d-1=9\), and this floor is \(12>11=2d+1\). For every \(d\ge5\) the baseline is \(3d-2\) at \(a=2d\) and \(3d-3\) at \(a=2d-1\), both larger than \(2d+1\). This replaces either invocation of the stronger size-ten weighted floor when \(d=5\). The initial equality count \(3d+1\) and its pure dimension \(d\) still follow from the paid fifth-degree surplus at the starting size \(2d+1\ge11\).

With these changes the exact clock-delay classification, detector-tail filling, Newton actions and reweighting prove the same odd theorem for every \(d\ge5\). The even theorem follows by applying the odd theorem to the actual next weighted tap, whose physical last position is strictly earlier. This proves the effective-order threshold stated above. The proof is not yet formalized in Lean.
