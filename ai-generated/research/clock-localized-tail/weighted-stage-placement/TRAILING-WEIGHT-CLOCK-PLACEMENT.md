# Where nonzero weighted clocks must occur in a narrow triangular tableau

Let \(A,\mathbf b\) be an ordinary order-\(p\) lower triangular RK tableau over a field with \(p!\) a unit. Start by restricting to the actual last nonzero output index
\[
                t\coloneqq\max\{i:b_i\ne0\}.
\]
This preserves ordinary order by triangularity. Work on the resulting \(t\) physical stages. Put
\[
         Q(p)\coloneqq\left\lceil
                  \frac{\lfloor(p+1)^2/4\rfloor}{2}\right\rceil .
\]
The hypotheses below do not identify a fixed sign or positive weight: each visible clock means an actual label at a row of nonzero weight, even if its sum over the entire clock fibre is zero.

For a literal leading cut after row \(k\ge1\), set \(L\coloneqq t-k\), and let \(q\) be the number of distinct clocks with nonzero output coefficients in those last \(L\) rows. The endpoint in the tail statements is \(c=1\). When it is present, call it visible only if it occurs at one of these nonzero weights; zero-weight rows at clock one do not affect this definition. For this actual cut define
\[
 D_p(q)\coloneqq
   \sum_{\substack{0\le r\le p-1\\r\ {\rm even}}}
                \min\{p-r,r+1,(2q-r)_+\},\qquad
 T_q\coloneqq q(q+1)/2 .
\]
The top parity of the ordinary commutator count ends at degree \(p-1\), so its word budgets \(r\) are even. In particular \(D_p(q)\le T_q\).

## An absolute chronological staircase

If the leading matrix has no zero diagonals, the [masked-density bound](MASKED-DENSITY-GROWTH.md) gives
\[
             k\ge Q(p)-D_p(q)-E,\qquad
             L\le t-Q(p)+D_p(q)+E .                               \tag{1}
\]
Here \(E=0\) for an endpoint-free visible set. If an endpoint is visible and the actual suffix matrix \(T=A_{S,S}\) acts invertibly on the \(\boldsymbol\beta\)-row orbit, where \(\boldsymbol\beta=\mathbf b|_S\), it is enough to take
\[
  E\coloneqq
   \#\{r\in2\mathbb Z_{\ge0}: 2q\le r<h,\ 2r\le p-1\},\qquad
  h\coloneqq\dim\operatorname{span}\{\boldsymbol\beta T^a:a\ge0\}.
                                                                    \tag{2}
\]
If that invertibility is not known, leave off the condition \(r<h\) to obtain a safe upper bound for the endpoint debit. The reason for (2) is exact: above the baseline triangle \(r\ge2q\), every positive density is already paid, and the ordinary density is also paid either when \(r\ge h\) by the actual suffix orbit or when \(r>p-1-r\) because the positive densities fill the whole scalar dual. Below the triangle the endpoint causes no additional debit.

Sort the distinct visible clock labels of the full tableau by their last physical occurrence at a nonzero weight, denoted
\[
                       t_1>t_2>\cdots>t_b .
\]
The suffix strictly after \(t_i\) contains exactly \(i-1\) visible labels, even if other earlier occurrences of these same clocks interleave. For every endpoint-free such suffix with nonsingular leading matrix this gives the **absolute** lower placement
\[
                       t_i\ge Q(p)-T_{i-1}.                        \tag{3}
\]
This is not a claim that the same clock is forbidden at earlier stages. If the whole visible set has no endpoint and all diagonals are nonzero, write \(g\coloneqq t-Q(p)\). Then the sum of the ages \(t-t_i\) of the last occurrences is at most
\[
                       b\,g+\binom{b+1}{3}.
\]
This follows by summing the independent position inequalities in (3); it does not add lower bounds on overlapping suffix widths.

Through order \(20\), the endpoint debit in (2) is zero as soon as \(q\ge5\), regardless of suffix orbit or diagonal, since \(2r\le p-1\) would give \(r\le9\) whereas \(2q\ge10\). Thus (3) holds on those cuts even with a visible endpoint. At smaller \(q\), if the suffix orbit is invertible, use \(h\le L\) in (2) to replace \(E\) by
\[
           \bigl[\min\{\lfloor(p-1)/4\rfloor+1,\lceil L/2\rceil\}-q\bigr]_+.
                                                                    \tag{4}
\]
For example, in a wholly nonsingular tableau at exact width \(t=Q(p)\) and \(p\le20\), suffixes with one, two, three, or four visible labels have at most \(1,3,7,11\) physical rows respectively, even if the endpoint is visible. Off the endpoint the caps are \(1,3,6,10\). These are width and placement restrictions, not new stage-count entries. In particular at exact width the last **two** stages, when present, carry nonzero output weights at distinct clocks, even when neither earlier physical adjacency nor same-clock purity is assumed. This follows from the two-row tail when \(t\ge3\). At \(t=2=Q(p)\) the order is three, and its scalar two-by-two moment matrix already forces both weights and distinct clocks. More generally at gap \(g\) a suffix seeing just one nonendpoint output clock has \(L\le g+1\); one seeing only the endpoint has \(L\le2g+1\) with the invertible suffix orbit.

For a mixed leading diagonal, subtract the measured sum of right-kernel intersections \(\nu_j^P\) from the first inequality in (1), using the same top parity and \(j\le p-3\). Equivalently add this penalty to its second inequality. If there are \(z_k\) actual zero diagonals in the first \(k\) stages, the penalty is at most \(\lfloor(p-1)/2\rfloor z_k\). Thus a small measured suffix \(q\) can force literal zero diagonals already to occur by \(k\), even though a partly implicit method need not meet \(Q(p)\) globally. In particular (3) is still usable on wholly nonsingular leading pieces of mixed-DIRK methods, whether or not their suffix is singular.

## Endpoint slack forces a long path from the weighted suffix

For a nonsingular prefix, set \(R\coloneqq L-(t-Q(p))-D_p(q)\). If \(R>0\), (1) first forces a visible endpoint. When the suffix orbit is invertible, at least \(R\) even budgets from (2) must then exist. Their \(R\)-th smallest possible value is \(2q+2R-2\); hence
\[
                      h\ge 2q+2R-1,\qquad
                      p-1\ge4q+4R-4 .                             \tag{5}
\]
This constrains the orbit of the entire suffix output row, not the orbit of a specific endpoint-weighted row.

If the method has a common nonzero diagonal \(\gamma\), write \(N=T-\gamma I\). This is the true strictly lower suffix action. Its row orbit on \(\boldsymbol\beta\) is the same as that of \(T\), and \(h\) is exactly the least index with \(\boldsymbol\beta N^h=0\): the earlier consecutive row powers are independent by multiplying any first nonzero relation by the largest remaining power. Thus (5) forces a nonzero physical suffix path of at least \(2q+2R-2\) strictly lower taps. When \(h=L\) the \(L-1\) links all have to be the actual adjacent links of the suffix, and the last stage has a nonzero output coefficient. In mixed DIRK, different nonzero diagonal values can generate a long \(T\)-orbit without such a path, so the last conclusion is common-diagonal only.

At a saturated cut one can also check a direct scalar obstruction without classifying the matrix. The actual lost scalar ranks \(\lambda_j\) satisfy \(\sum_{j\equiv p-1}\lambda_j\ge L-(t-Q(p))\) by the nonsingular prefix recurrence. If that equals the sum of the proved grade-by-grade debit caps, every individual cap is attained. Thus any additional genuine prefix scalar read, independent in that specific degree, refutes the saturated shape. For instance if the cap at \(r=2\) is the full rank three, no nonzero paid scalar combination at that grade can descend; in particular the true suffix row \(\boldsymbol\beta[C_S,T]\) cannot be zero, since \(\mathbf b[C,A]\) physically pays \(\ell_2\) if it is. This illustrates a real overlap restriction, not a further assumed rank bonus.

These statements refer to the original nonzero weights and actual clock labels. Neither a count of aggregate quadrature nodes nor a guessed co-clock grouping can be substituted for them; the companion note explains the additional restrictions when the aggregate count itself is minimal.
