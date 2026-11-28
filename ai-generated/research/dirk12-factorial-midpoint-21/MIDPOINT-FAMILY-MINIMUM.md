# Why equal-substep midpoint extrapolation cannot use fewer than 21 stages at order twelve

This is a scope-specific minimum over characteristic-zero fields. It is
not a lower bound for general ordinary DIRK, arbitrary variable-step
midpoint compositions, or arbitrary positive characteristic.

Let \(n\) identify a uniform implicit-midpoint macro map with \(n\)
positive integer substeps. On the scalar test equation its stability
function is
\[
  R_n(z)=\left(\frac{1+z/(2n)}{1-z/(2n)}\right)^n,
  \qquad
  \log R_n(z)
   = z+\sum_{j\ge1}\frac{n^{-2j}}{(2j+1)2^{2j}}z^{2j+1}.
\]
Combine any repeated branch counts and let \(w_n\ne0\) denote their
remaining weights. The first-order identity enforces \(\sum_n w_n=1\),
also if the macro outputs were originally combined as increments from
the same input. Put \(M_j=\sum_n w_n n^{-2j}\).

At degree \(2j+1\), the term involving \(M_j\) in
\(e^{-z}\sum_n w_n R_n(z)\) is \(M_j/[(2j+1)2^{2j}]\).
Every other contribution involves \(M_i\) with \(1\le i<j\):
a product of \(\ell\ge2\) terms in the exponent uses total clock-power
index \(i\), and then its degree is \(2i+\ell\). Consequently linear
order twelve implies \(M_1=\cdots=M_5=0\) successively. This uses only
the necessary tall-tree conditions.

If \(r\le5\) distinct branch counts remained, the monic polynomial
\(P(X)=\prod_{n:w_n\ne0}(X-n^{-2})\) would satisfy
\(\sum_n w_nP(n^{-2})=P(0)\) by those moments. The left side is zero
but \(P(0)\ne0\). Thus at least six branch counts remain active.

For each such \(n\), the branch \(w_nR_n\) has a pole of order \(n\)
at \(z=2n\), and every other branch is regular there. No pole can
cancel in the sum. Its reduced stability denominator therefore has
degree at least
\[
                      \sum_{w_n\ne0}n\ \ge\ 1+2+3+4+5+6=21.
\]
Every \(s\)-stage RK stability function has the denominator
\(\det(I-z\mathit A)\) before reducing fractions and thus reduced
denominator degree at most \(s\). This proves 21 as a lower bound even
for a different RK realization of this same macro extrapolation family,
not only for its literal disjoint-block realization.

For the actual six branches at \(n=1,\ldots,6\), the same nodal
polynomial calculation at degree six gives
\(M_6=-(6!)^{-2}\). Hence the thirteenth tall-tree defect is
\[
      \frac{13!}{13\,2^{12}}M_6
                =-\frac{\binom{12}{6}}{2^{12}}
                =-\frac{231}{1024},
\]
agreeing with the separate literal integer replay. This proves the
scoped lower; full ordinary order of the 21-stage witness is checked
independently in the accompanying literal proof.
