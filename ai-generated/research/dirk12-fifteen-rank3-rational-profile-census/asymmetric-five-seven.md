# The five-forward/seven-reverse rational chronology fixes the denominator

This is a further exact restriction on the one-shared-root case of the [rational-profile census](README.md), not a fifteen-stage exclusion. Suppose the lone clean interior clock \(a\) has five dirty physical stages before it and seven after it in ordinary forward chronology. Put \(U=D/(X-a)\), \(V=T/(X-a)\) after taking the monic common factor. Then \(V\) is **nonconstant**, it **does not vanish at \(a\)**, and its projective coefficients are determined by the fixed \(a\). In particular this asymmetric chronology is impossible for a constant \(V\) or a repeated denominator root. The other physical split is not interchanged here: only the actual reverse flag has the rank-four pure band at grade six.

The fifteen weights are live by the [census](README.md). Let \(F,G\) be the monic numerical hulls of the five earlier dirty labels and the seven later dirty labels. All twelve labels are distinct; none is a root of \(U\). There is a nonzero genuine grade-four contrast \(P(\mathbf c)-\mathbf h Q(\mathbf c)\), with \(\deg P\le4,\deg Q\le1\), vanishing on the six physical rows before \(a\). This follows from the seven input coefficients, and the map to \(P\) is injective because a pure \(Q\) vanishes at five distinct dirty labels. The known nonzero diagonal and clean grade-six commutator and primitive yield \(P(0)=P(a)=JP(a)=J[XP](a)=0\). Up to scaling its unique scalar profile is
\[
                      P_a(X)=X(X-a)(X^2-aX+a^2/5).
\]
This is exactly the quadratic orthogonality of the remaining factor for \(X(a-X)\,dX\) on \([0,a]\). Therefore \(VP_a-UQ\) is a nonzero multiple of \(F\). It has degree at most five and vanishes on the five labels; it cannot vanish polynomially because \(\gcd(U,V)=1\) would give \(U\mid P_a\), contrary to the zero at \(0\) and the fact that \(U(0)\ne0\).

Conversely the true weighted reverse contrast \(\beta[(1-\mathbf c)(U(\mathbf c)-\mathbf hV(\mathbf c))]\) has grade at most five, and is zero on all rows earlier than the clean pivot in reverse chronology. Its profile is \((1-X)U\). The actual reverse primitive has grade-six pure discrepancy in \(\mathcal B_6=(\beta\mathbf h)P_3(\mathbf c)\). Thus
\[
                       V J^\ast[(1-X)U] + U R_3
\]
vanishes at all seven later labels, has degree at most seven, and is not identically zero: evaluating at roots of \(U\) gives nonzero values by the fixed check below and coprimality. It is a nonzero multiple of \(G\). Here \(J^\ast f(x)=\int_x^1 f\). This uses the original rank-four weighted operator, not a symmetric assumption on both flags.

On the twelve dirty labels the channel weights \(\nu_i=b_i U(c_i)/V(c_i)^3\) annihilate all polynomials through degree ten. Since these labels are distinct, \(\nu_i=M/(FG)'(c_i)\) for some \(M\ne0\), by the elementary top-coefficient identity for Lagrange interpolation. The ordinary scalar quadrature on the dirty rows equals the fixed Lobatto interior masses \(\omega_z\) on the four roots of \(U\) (the clean \(a\) and the two literal endpoints already account for their full fixed masses). Applying the same top-coefficient identity on the union of the twelve dirty roots and the four roots of \(U\) to polynomials \(V^3 S\) for all \(S\in P_3\) then shows
\[
                         \omega_z U'(z)F(z)G(z)=-M V(z)^3
                         \quad(U(z)=0).
\]
The polynomial \(V^3 S\) has degree at most six, well below the top degree 15, and the four values of \(S\) separate the four target masses. No unknown tableau weight or divisor is being reduced modulo a prime.

Substitution and cancellation only at \(V(z)\ne0\) now give
\[
          V(z)\ \text{proportional, with one common nonzero scalar, to}\
          f_a(z):=\omega_z U'(z) P_a(z) J^\ast[(1-X)U](z),\quad U(z)=0 .
\]
Thus any two such values determine \(V\) projectively. The exact fixed-root arithmetic verifies, for all \(a\) and all distinct roots \(z,w\) of \(U\), that \(f_a(w)-f_a(z)\ne0\) and
\[
                      (w-z)f_a(z)+(a-z)\bigl[f_a(w)-f_a(z)\bigr]\ne0.
\]
These force a genuine affine \(V\) and \(V(a)\ne0\). The unique second denominator root is off the fixed five-root grid, because the four values \(f_a(z)\) and the extrapolation at \(a\) are all nonzero. This reduces the viable denominator parameter to the one listed fixed real-algebraic shape for each \(a\), up to the scale of \(\mathbf h\).

The standalone exact script checks 30 slopes and 30 extrapolations, and the 20 ordered pairs of nonzero factors \(P_a(z),J^\ast[(1-X)U](z)\), at both \(43\) and \(181\). Ordered-root products of their numerators give characteristic-zero nonvanishing as in the main packet; the scalar Lagrange denominators at the fixed seven nodes and all small primitive denominators are units at both primes. This optional arithmetic is independently exact but is not part of the portable Lean receipt.

    python3 -B check-asymmetry.py
