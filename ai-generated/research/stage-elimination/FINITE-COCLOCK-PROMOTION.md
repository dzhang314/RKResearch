# From a quotient character to a numerical co-clock relation

Let \(N\coloneqq A^\mathsf T\), \(\mathbf y\coloneqq\mathbf1-A\mathbf1\), and \(Y\coloneqq\operatorname{diag}(\mathbf y)\). Reversing chronological labels conjugates these operators and changes none of the rank statements. Work over a field \(K\). The order conditions are used only where a subspace is known to contain actual numerical relations.

## A character does not give a supported vector

Let \(B\subset M\subset K^s\) have codimension one, and let \(\chi\colon M\to K\) be nonzero with kernel \(B\). For a clock \(a\), set
\[
 S_a\coloneqq\{i:y_i=a\},\qquad
 P_a\mathbf z\coloneqq\bigl(\mathbf z|_{S_a^c},\mathbf1\cdot\mathbf z\bigr),\qquad
 U_a\coloneqq M\cap\ker P_a.
\]
The mass coordinate is redundant if \(M\) already consists of genuine zero-model marks. There is a co-clock zero-mass vector in \(M\) carrying the character if and only if
\[
 \dim P_a(M)=\dim P_a(B).
\]
Indeed, \(\dim U_a-\dim(U_a\cap B)=1-\dim P_a(M)+\dim P_a(B)\). In particular, the representation of a character by a *row* supported at clock \(a\) is not a substitute for this test for a *vector* at that clock.

For example, suppose the actual space is a finite polynomial band
\[
 M\coloneqq U\oplus\{\mathbf w\odot P(\mathbf y):\deg P\le m\},
 \qquad \chi(\mathbf u+\mathbf w\odot P(\mathbf y))=\ell(\mathbf u)+\kappa P(a).
\]
Assume \(M\subset\mathbf1^\perp\), \(YU\subset U\), \(\mathbf w\) belongs to a chosen \(Y\)-invariant complement to \(U\), and \(\ell((Y-a)U)=0\). Let \(H\) be the clock labels at which the corresponding piece of \(\mathbf w\) is nonzero. Suppose \(m<|H|\), so the polynomial coefficients are genuine coordinates. A supported representative carrying \(\chi\) exists exactly when either \(\ell\) is nonzero on \(U\cap K^{S_a}\), or all three conditions
\[
 \kappa\ne0,\qquad a\in H,\qquad m\ge |H|-1
\]
hold. In fact, off clock \(a\) the head component cannot be canceled by the invariant core; the polynomial must vanish at all labels of \(H\setminus\{a\}\). The required isolating polynomial has degree \(|H|-1\) when \(a\in H\). If \(a\notin H\), the whole support condition requires \(P=0\). Thus a scalar-head character may admit a local representing row while the head is still much too short to produce a local state vector.

## Invariant space and eigenline are separate tests

Choose a matrix \(O\) with kernel \(U_a\), and set
\[
 \mathcal O\coloneqq\begin{bmatrix}O\\ON\\\vdots\\ON^{s-1}\end{bmatrix},
 \qquad W\coloneqq\ker\mathcal O.
\]
By Cayley-Hamilton, \(W\) is the largest \(N\)-invariant subspace of \(U_a\). In particular it is genuinely co-clock and mass zero. For any extension of \(\chi\) to the ambient space, appending it to \(\mathcal O\) increases rank exactly when this largest invariant space carries the character. Appending it instead to \([\mathcal O;N-\nu I]\) tests exactly whether there is an actual eigenline carrying that character and eigenvalue \(\nu\).

When \(\chi(N\mathbf x)=\nu\chi(\mathbf x)\) holds on \(W\), let \(Q\coloneqq W\cap\ker\chi\) and choose \(\mathbf q_0\in W\) with \(\chi(\mathbf q_0)=1\). The obstruction to an eigenvector lifting that quotient generator is precisely the class of \((N-\nu I)\mathbf q_0\) in
\[
 Q/(N-\nu I)Q.
\]
Changing the representative adds an element of \((N-\nu I)Q\); when the class is zero it can be canceled by a change inside \(Q\). A sufficient condition is that \(\nu\) is absent from the spectrum of \(N|_Q\). The quotient identity on \(W\) is automatic from adjacent flag levels only if their characters agree on \(M\) and the graded action actually gives \(\chi_{m next}(N\mathbf x)=\nu\chi(\mathbf x)\).

A repeated diagonal gives a literal obstruction even for a common nonzero diagonal. Take
\[
 A\coloneqq\begin{pmatrix}c&0&0\\0&c&0\\\lambda&-\lambda&c\end{pmatrix},
 \quad\lambda\ne0,\qquad
 \mathbf u\coloneqq\mathbf e_1-\mathbf e_2,\qquad
 \mathbf q_0\coloneqq\mathbf e_3-\mathbf e_2.
\]
All three clocks equal \(1-c\). On the zero-mass plane, \(N\mathbf u=c\mathbf u\) and \(N\mathbf q_0=c\mathbf q_0+\lambda\mathbf u\). Quotienting by \(K\mathbf u\) gives slope \(c\), but no eigenvector with nonzero \(\mathbf q_0\)-component. In this example the entire plane nevertheless annihilates all tree vectors, because \(A\mathbf1=c\mathbf1\) and the recurrence keeps every tree vector proportional to \(\mathbf1\). Thus an actual invariant relation space can suffice for elimination even when the quotient eigenline cannot be split.

## When finite measured flags pay the nonlinear tests

Let \(E_g\) and \(d(t)\) have the meaning in the elimination note. The space
\[
 E_\infty\coloneqq\bigcup_{g\ge0}E_g
\]
is an \(A\)-invariant unital subalgebra of \(K^s\) under coordinatewise multiplication. Every unital subalgebra here consists precisely of vectors constant on its blocks of indistinguishable coordinates. To see this, for any one block choose, for each other block, a feature that differs between them. A scalar affine function of that feature is one on the chosen block and zero on the other block. Their product is the indicator of the chosen block. This argument is over any field; it does not require one feature with all values distinct.

These full tree classes can also be found without enumerating all trees: start with one block. Keep two rows in the same block at the next step only if their sums of \(A\)-entries into each current block agree. Every true equivalence remains in the same block, inductively: each current block indicator belongs to \(E_\infty\), and applying \(A\) yields the summed row entries. Intersecting their level sets with the old blocks again has indicators in \(E_\infty\), by the same polynomial argument. The stable partition is \(A\)-invariant on its block-constant vectors and therefore contains every numerical tree vector in its block-constant algebra. The two partitions thus agree. There are at most \(s-1\) nontrivial refinements.

Here are three finite sufficient tests that can be used before full stabilization.

1. **Maximal local rank at an observed partition.** Partition one fibre \(S\) into \(r\) joint profiles of \(E_g|_S\). Every block indicator on \(S\) is the restriction of a product of at most \(r-1\) affine functions of \(E_g\), hence of an element of \(E_{(r-1)g}\). Suppose \(W\subset K^S\) is \(N\)-invariant, annihilates that paid space, and \(\dim W=|S|-r\). Then \(W\) consists of exactly the vectors with zero sum on each of the \(r\) blocks. Its annihilator is the algebra of vectors constant on those blocks, with all outside stages left separate. Invariance under \(N\) makes that algebra \(A\)-invariant. All trees lie in it, and the safe elimination removes \(|S|-r\) stages. The case \(r=1\) needs only zero mass and the stated dimension/invariance. A measured codimension shortfall cannot be filled by treating untested class sums as zero.

2. **Local product saturation and a stable observed partition.** Suppose \(M_j\) is an ascending genuine mark flag, with \(\mathbf z\odot\boldsymbol\Phi_t(A)\in M_{j+d(t)}\) for \(\mathbf z\in M_j\), and \(M_j\subset\mathbf1^\perp\) for the levels used. If \(W\subset M_j\cap K^S\) and \(\dim(M_{j+g}\cap K^S)=\dim W\), then multiplication by any member of \(E_g\) preserves \(W\). If the full-stage partition observed from \(E_g\) is stable under the summed-row test, its coordinatewise algebra is \(E_\infty\). Multiplication by every tree vector therefore preserves \(W\). Its pairing with any \(\mathbf w\in W\) is the mass of another vector in \(W\), and is zero. This proves exact elimination, even without an eigenline calculation.

3. **Single co-clock block with enough external measurements.** Suppose a supported vector \(\mathbf q\in M_j\) has support exactly \(S\), and \(M_{j+g+1}\cap K^S=K\mathbf q\). Every member of \(E_{g+1}\) is constant on \(S\), since multiplication of \(\mathbf q\) by that member remains in the same line. Let \(J\subseteq S^c\) contain all external columns in which any two rows from \(S\) differ. If the observed projection
   \[
    \bigl\{(v_k-v_S)_{k\in J}:\mathbf v\in E_g\bigr\}=K^J,
   \]
   where \(v_S\) is the common value on \(S\), then those rows agree in every column outside \(S\). Indeed, \(A\mathbf v\in E_{g+1}\), and the difference on any two rows from \(S\) is exactly their outside row contrast paired with \((v_k-v_S)_{k\in J}\); the terms proportional to \(v_S\) cancel because the two row sums agree. Surjectivity makes the contrast zero. The total row entry into \(S\) also agrees, so \(S\) is one stable block with all outside stages singleton. It can be merged exactly to its earliest representative, preserving the diagonal class. In particular, a small external-read set gives a local rank check instead of a global stage-algebra calculation.

A mass-zero common \(Y,N\) line alone supplies none of these multiplicative or two-sided tests. The companion example shows the obstruction in genuinely paid tableaux.
