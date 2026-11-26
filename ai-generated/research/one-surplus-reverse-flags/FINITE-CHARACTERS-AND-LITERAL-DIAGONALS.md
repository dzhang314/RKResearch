# When a finite reverse surplus gives a physical clock witness

Work over a field in which the factorials used below are units. Let \(N\) be the actual lower triangular reverse transpose, \(Y=\operatorname{diag}(\mathbf y)\) with reflected clocks \(y_i=1-c_i\), and \(\mathbf v\) the reversed output weights. Let \(M_j\) be a genuine zero-density one-mark flag, and let \(B_j\subset M_j\) be its actual word subflag. We require \(NB_j,YB_j\subseteq B_{j+1}\) wherever used, not just a polynomial model for the flag. Write
\[
 \mathscr D\coloneqq YN-NY-N^2,qquad
 D_{k+1}\coloneqq N\bigl(\mathbf v\odot\mathbf y^{\odot k}\bigr)
          -\frac{\mathbf v\odot\mathbf y^{\odot(k+1)}}{k+1}.
\]
These are the actual commutator and the primitive adjoint defects, at costs two and \(k+1\) respectively. A terminal-zero flag requires the relevant genuine errors and word actions to be terminal-zero.

A finite surplus on a unit band means a codimension-one quotient with normalized covectors \(\Phi_j\) such that
\[
 \Phi_{j+1}|_{M_j}=\Phi_j,qquad
 \Phi_{j+1}Y|_{M_j}=a\Phi_j,qquad B_j=\ker\Phi_j .
\tag{1}
\]
Here \(a\) is the finite character parameter. A witness at this reflected clock is a literal stage with forward clock \(1-a\).

## 1. Which finite characters are physically local?

In a late one-head normal form
\[
 M_H=U\oplus\mathbf w\mathcal P_m(Y),\qquad
 \Phi_H(\mathbf u+\mathbf wP(Y))=\ell(\mathbf u)+cP(a),
\]
the invariant space \(U\) splits by clock, \(\ell\) is supported at the \(a\)-fibre, and \(\mathbf w\) can be chosen in a fibrewise complement of \(U\). Let \(U_a\) and \(\mathbf w_a\) be the actual restrictions to the \(a\)-fibre.

The character has a representing row supported on this actual fibre if and only if \(c=0\), or \(\mathbf w_a\) is nonzero modulo \(U_a\). When \(c=0\) its nonzero invariant part requires an actual fibre. When \(c\ne0\), a local row must take the value \(c\) on the head and the prescribed values on \(U_a\); the complement assumption makes those requirements independent precisely when the head fibre is present. Otherwise \(P(a)\) is a nonlocal evaluation, even if an output happens to use the numerical clock \(a\).

On a physical prefix \(I\), suppose a row represents the character and the restriction of the head at \(a\) belongs to the restricted core. Let \(\mathbf u_a\in U_a\) match that restriction, with \(\mathbf u_a=0\) if the fibre is absent. The relevant coefficient is \(c_I\coloneqq c-\ell(\mathbf u_a)\); it does not depend on the choice of match because \(\ell\) factors through the prefix. If \(c_I\ne0\), at least \(m+1\) other head labels must be visible modulo the restricted core. Otherwise the product \(T\) of the at most \(m\) visible labels has degree at most \(m\), and the core cancels the head \(\mathbf wT(Y)\) on the whole prefix. The resulting vector has zero restriction to \(I\) but character value \(c_IT(a)\ne0\). If \(c_I=0\), there is no such counting requirement. See [the repeated-fibre argument](REPEATED-FIBRES-AND-NONZERO-DIAGONAL-OBSTRUCTION.md) for the full restriction criterion.

## 2. A finite cut that forces a literal zero diagonal

Take a physical row \(\lambda\) supported at clock \(a\) through a last nonzero index \(i\), representing the character through the relevant grades. In particular it kills \(B_{j+2}\). Put \(\beta\coloneqq\lambda\mathbf v\). Suppose \(\beta\ne0\) and there is a clock polynomial \(P\) such that
\[
 \deg P\le j,qquad P(a)\ne0,qquad
 \pi_{<i}\bigl(\mathbf v\odot P(\mathbf y)\bigr)
                          \in \pi_{<i}B_j,qquad
 \lambda\mathscr D\bigl(\mathbf v\odot P(\mathbf y)\bigr)=0 .
\tag{2}
\]
Then \(N_{ii}=0\) at this **literal** stage.

Indeed let \(\mathbf h\in B_j\) agree with the input on the strict earlier prefix. Both \(\mathscr D\mathbf h\in B_{j+2}\) and the last equality in (2) give
\[
 0=\lambda\mathscr D(\mathbf v\odot P(\mathbf y)-\mathbf h)
                   =-N_{ii}^{2}\beta P(a).
\]
The second equality is the actual triangular pivot calculation, using the diagonal \(-N_{ii}^2\) of \(\mathscr D\). Earlier values of the matched input are zero, not just pooled zero. The same argument applies to any representing row with this support and nonzero \(\beta\), even if it uses other earlier stages at the same clock.

Condition (2) is a finite rank certificate. Test the earlier prefix condition by an annihilator of \(\pi_{<i}B_j\), and append the linear scalar test involving \(\lambda\mathscr D\). There is a successful polynomial precisely when the evaluation row at \(a\) increases the rank of this coefficient matrix. It is enough to prove the stronger word membership \(\mathscr D(\mathbf v\odot P(\mathbf y))\in B_{j+2}\). In fact the exact identity
\[
 \mathscr D(\mathbf v\odot\mathbf y^{\odot k})
   =(Y-N)D_{k+1}-\frac{k+2}{k+1}D_{k+2}
\tag{3}
\]
follows from \(XJ-JX=J^2\), after expanding both primitive errors. Thus the first \(k+2\) actual primitive defects being in their word grades suffices for every clock mask of degree at most \(k\).

Here is a convenient prefix-only realization. For every earlier clock fibre ask whether the prefix of its scalar base can be matched by \(B_j\) on the whole earlier prefix, with zero on the other fibres. Let \(S\) be the set of unmatched labels. If \(a\notin S\), use
\[
                           P(X)\coloneqq\prod_{x\in S}(X-x).
\]
Then the prefix condition in (2) follows by summing the separate actual fibre matches. In particular a clock-invariant restricted \(B_j\) permits this test with independent local restrictions. If the first two defects vanish and \(B\) is the word flag seeded by \(D_3\), (3) already pays zero or one unmatched earlier label, in grade at most three. More generally a paid horizon \(H\) permits as many as \(H-2\) distinct unmatched labels if their initial primitive defects are paid into \(B\). This applies at every order range with the corresponding paid grades, including balanced cutoffs between six and ten without fixing an endpoint.

If the \(a\)-fibre has only one physical stage, a nonzero local representing row is a scalar coordinate evaluation, so \(\beta=0\) is exactly absence from individual output support. With repeated clocks this inference requires an extra measurement: the restriction of the scalar base to the physical support of the representing row must be detected by that row. One sufficient test is membership in the restriction of the full marked space but not in the restriction of its word subspace, provided the row represents the resulting nonzero quotient. Restrict the full spaces, not just their intersections with the fibre. A zero sum of signed output weights is not a visibility test.

## 3. A version using the surplus itself rather than the scalar base

Under (1), \(N\) acts between the one-dimensional quotients by a scalar \(\nu\), constant as long as the finite restriction is nonzero and \(N\) is paid across both grades. This follows by comparing \(\Phi_{j+2}(N\mathbf z)\) on an actual \(\mathbf z\in M_j\) using the two intersections. Consequently \(\mathscr D\) acts by \(-\nu^2\) there.

If a representative \(\mathbf z\in M_j\) with \(\Phi_j(\mathbf z)\ne0\) can be matched by \(B_j\) on the full strict prefix of a local representing row \(\lambda\), the same first-pivot calculation with \(N\) gives \(\nu=N_{ii}\). In particular an actually paid \(\mathscr D\mathbf z\in B_{j+2}\) forces a zero diagonal without asking that \(\mathbf v\) be visible. Matching on only the one clock fibre does not suffice for this argument: all earlier physical rows matter to \(N\).

## 4. A related paid scalar test for output absence

Suppose the actual primitive defects through degree \(r\) are invisible to the local row:
\[
 \lambda D_{k+1}=0\qquad(0\le k\le r).
\]
Then \(\lambda N(\mathbf v\odot P(\mathbf y))=\beta JP(a)\) for every \(P\in\mathcal P_r\). On the left pool the receiver values \(\lambda N\mathbf v_x\) at each distinct clock, and let \(m\) be the number of nonzero such pools.

If \(a\ne0\), a nonzero \(\beta\) requires \(r\le2m-1\). Otherwise take the monic receiver hull of degree \(m\) times every test of degree at most \(m\). Rescale the primitive at \(a\) to the fixed nonsingular ordinary Gram on \([0,1]\), contradicting the nonzero hull. If the contributing hull includes \(a\), the stronger requirement is \(r\le2m-2\): factor off \(X-a\) and use the paid endpoint-weighted Gram with tests through degree \(m-1\). Small receiver support therefore proves \(\beta=0\), or literal output absence under the visibility condition above. No sign of \(a\) or of the weights is used.

If \(a=0\) and \(r\ge m-1\), all receiver pools vanish by Vandermonde, since the primitive at zero is identically zero. For a fibre with one physical stage and \(\beta\ne0\), its pool is \(N_{ii}\beta\), yielding the zero-diagonal witness. With repeated fibres the same inference requires that this pool be physically isolated, or the strict earlier matching of the \(a\)-scalar fibre used in Section 2. Otherwise signed cancellation can make the pool zero on entirely nonzero diagonals.

These are field tests with the indicated units. The same calculation over a ring gives \(N_{ii}^2=0\) if \(\beta P(a)\) is a unit; one needs reducedness for the literal conclusion \(N_{ii}=0\). For a nonreduced example, extend the companion duplicate-stage construction to \(K[\varepsilon]/(\varepsilon^2)\), choose the duplicate diagonal \(\varepsilon\), and choose \(a\ne0\) in \(K\). The difference \(\varepsilon-a\) is a unit, and the commutator value at the new row vanishes even though its diagonal is nonzero. The field test still applies after any residue-field reduction that preserves the required visibility and prefix ranks.
