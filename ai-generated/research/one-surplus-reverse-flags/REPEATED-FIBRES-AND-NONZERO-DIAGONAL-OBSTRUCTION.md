# What prevents an unconditional zero-diagonal conclusion

The support and matching requirements in FINITE-CHARACTERS-AND-LITERAL-DIAGONALS.md distinguish an actual local character from an abstract polynomial evaluation. This note makes both the prefix distinction and the physical repeated-stage obstruction exact.

## Prefix localization with a nonzero invariant component

Use the same notation \(M_H=U\oplus\mathbf w\mathcal P_m(Y)\) and \(\Phi_H(\mathbf u+\mathbf wP)=\ell(\mathbf u)+cP(a)\). Suppose the character is representable on a physical prefix \(I\). In particular \(\ell\) factors through the prefix restriction of \(U\). If the head on the \(a\)-fibre is visible modulo the restricted core, the local fibre realizes both parts of the character.

If it is not visible there, choose \(\mathbf u_a\in U_a\) matching its earlier head restriction and define the residual coefficient
\[
                     c_I\coloneqq c-\ell(\mathbf u_a).
\]
This is independent of the match because \(\ell\) is itself prefix representable. If \(c_I=0\), the whole character is still representable on the physical \(a\)-fibre by the restricted invariant functional. If \(c_I\ne0\), the prefix needs at least \(m+1\) distinct effective head labels away from \(a\). Otherwise let \(T\) be their monic hull of degree at most \(m\). The vector \(\mathbf wT(Y)\) can be canceled on the prefix by a vector of \(U\): it has zero effective head there and the core splits by clocks. The only contribution of the canceling vector to \(\ell\) is \(-\ell(\mathbf u_a)T(a)\). Hence this actual zero-prefix vector has character value \(c_IT(a)\ne0\), contradiction. When the physical fibre is absent take \(\mathbf u_a=0\).

Thus a character that is not locally detectable still has a concrete earlier-prefix cost; it cannot be assumed absent merely because the head is zero at its numerical parameter. Nor can a statement about pooled output weights be substituted for individual visibility on a repeated fibre.

## A genuine one-surplus extension with no zero diagonal

There is a simple exact operation showing why the extra hypotheses of the diagonal test cannot be omitted. Begin with any achieved triangular RK method with a literal stage \(i\), nonzero output weight at that stage, and vanishing first adjoint primitive defect
\[
           N\mathbf v_0=Y\mathbf v_0
quad\text{on the old stages}.
\]
This is the usual simplifying adjoint identity of order one. Let the original stage's reflected clock be \(a\). Append a duplicate stage \(r\) after all original rows, but give it any chosen nonzero diagonal \(\eta\ne a\). In forward stage order, with the old row extended by zero, set
\[
           A_{r,-}\coloneqq A_{i,-}
                         +\eta(\mathbf e_r-\mathbf e_i)^{\mathsf T}.
\]
The row remains lower triangular and has exactly the desired new diagonal. Its clock equals the original clock, and its actual rooted weights equal those of stage \(i\) for every tree. For the latter fact, the extra term in the normalized unary readout vanishes as soon as the child's two entries agree; the leaf and rooted product steps complete induction. This is an exact stage alias even if \(\eta\ne A_{ii}\).

In reverse coordinates let \(\mathbf q\coloneqq\mathbf e_r-\mathbf e_i\) for the same two physical stages, and extend the old output \(\mathbf v_0\) by zero on the new alias. Then
\[
          Y\mathbf q=a\mathbf q,\qquad N\mathbf q=\eta\mathbf q .
\]
Move a nonzero part \(\delta\) of the output from \(i\) to \(r\), keeping the old stage's weight nonzero. The total new output is \(\mathbf v=\mathbf v_0+\delta\mathbf q\), and **every** rooted output is unchanged. The new first primitive defect is \(\delta(\eta-a)\mathbf q\), so \(\mathbf q\) is a genuine marked direction from grade one. The old defect remains zero at the new leading reverse row because it has old weight zero and no earlier reverse input.

More strongly, for every grade \(j\ge1\), the full genuine zero-density marked space for the new weights is the direct sum of the old space (extended by zero on the alias) and the line \(K\mathbf q\). Every genuine one-mark expression is linear in the output vector. Its evaluations at the two weight choices differ by a scalar multiple of \(\mathbf q\), since \(N,Y\), and every diagonal actual rooted-feature multiplier preserve that line. Formal models of those expressions are unchanged. The line itself is already genuine, so these evaluations span precisely the direct sum. This also proves that the old space is an actual subflag stable under the word actions inside the new space. Thus the added quotient has a finite character at the actual active clock \(a\), with \(N\)-action \(\eta\ne0\). Where the old spaces had unit gains, the new ones have the same unit gains.

The same obstruction can preserve a specifically chosen third-residual word flag. At \(a\ne0\), choose the new diagonal \(\eta=a/3\); at \(a=0\), take any \(\eta\ne0\). Then the change of \(D_3\) is \(\delta a^2(\eta-a/3)\mathbf q=0\), while \(D_1\) still creates the genuine line. The old \(D_3\)-word flag remains supported off the alias. Thus wherever the old spaces actually equal that word flag, the new relative surplus is exactly one over the *same* word flag.
e0), choose the new diagonal (eta=a/3); at (a=0), take any (eta
e0). Then the change of (D_3) is (delta a^2(eta-a/3)mathbf q=0), while (D_1) still creates the genuine line. The old (D_3)-word flag remains supported off the alias. Thus wherever the old spaces actually equal that word flag, the new relative surplus is exactly one over the *same* word flag.

For example one can supply the original vanishing defect and nonzero diagonals at any required finite order by palindromic compositions of implicit midpoint. In tableau form each substep of size \(b_i\) gives \(A_{ij}=b_j\) for \(j<i\), \(A_{ii}=b_i/2\). Therefore \(A^{\mathsf T}\mathbf b=\mathbf b\odot(\mathbf1-\mathbf c)\) exactly. The usual symmetric threefold recursion preserves nonzero real-algebraic substep sizes: for a current symmetric method of even order \(2k\), the three multipliers \(s,1-2s,s\), with \(2s^{2k+1}+(1-2s)^{2k+1}=0\) and \(s=(2-2^{1/(2k+1)})^{-1}\), cancel its first formal odd error; symmetry removes the next even error. The argument gives high order with all original physical diagonals nonzero. The alias adds only another such diagonal. This observation does not assert that those large examples saturate any absolute RK stage bound. It does show that genuine order, a one-dimensional relative flag surplus, and physical output support alone do not force an explicit stage.

The missing cut condition is exact in this example. The representing row is the new reverse coordinate and the scalar prefix is empty, but the commutator on the new scalar base has surplus contribution \(-\delta\eta^2\mathbf q\). It is not invisible to that row. Thus one cannot omit the actual commutator measurement even in the easiest possible prefix.

## A minimal-stage way to rule out the simplest local obstruction

Conversely, if a genuine surplus line has an actual representative \(\mathbf q\) supported on exactly two physical stages at one clock, with zero ordinary sum and \(N\mathbf q=\eta\mathbf q\) **as an actual equality**, it is a removable alias. Scale it as the difference of the two coordinate vectors. The equality then says that the two forward rows differ by \(\eta\) times that coordinate difference, so the rooted recursion gives identical weights at all trees. Merge the later stage into the earlier one and pool their later couplings and output weights. This preserves lower triangularity and the surviving diagonal entries, so it is valid for each of ERK, DIRK, and strict SDIRK whenever the starting tableau is in that class.

For example it is enough that the actual marked fibre at the next grade be one-dimensional and that the primitive action on the actual two-stage representative have no off-clock leakage. A stage-minimal method cannot have such an alias. This does not apply to an eigenvalue only in the surplus quotient, nor to a zero-sum eigenvector with support at three or more stages: a linear relation among their stage values does not in general survive coordinatewise multiplication at the root. To propagate the exclusion beyond this case one needs a separate test of higher rooted-feature invariance or an actual prefix match such as the one above.
