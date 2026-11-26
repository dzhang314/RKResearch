# The logarithmic ERK surplus survives over every coefficient ring admitting the order

**Theorem.** In the setting of the companion fifth-degree proof, let \(r\ge10,\ q=\lfloor r/2\rfloor\), and let \(h\) be the largest integer with \(5\,2^h\le q\). Then
\[
 n\ \ge\ \lceil3r/2\rceil-1+h .
\]
Thus ordinary order 20 requires **at least 30 explicit stages over every nonzero commutative unital ring**. This improves the former arbitrary-ring entry of 28, matches its characteristic-zero field entry of 30, and does not improve the ordered-field floor of 32. No new Lean check is claimed.

The earlier characteristic-zero proof is RKResearch commit c1d29976a37f7f264f7123bf0cd69a8126a107b3, ai-generated/lower-bounds/characteristic-zero/erk_characteristic_zero_logarithmic_stage_bound_rodrigues_boundary_jets_20261123.md (SHA-256 52dde9f7f2fb12ac7695c2d1598a3261861d3deb2d56886989418b52960bef45), with the diagonal filtration in erk_field_independent_surgery_one_head_and_p12_baselines_20261123.md. This supplement gives the proof in the finite prime budget. The notation \(A,c,C,F_j,E_j,J\), chronological compression, separation and dimension inequality (1) are those defined and proved in the companion 01-PAID-GRADE-FIVE-SURPLUS.md. A sufficient coefficient hypothesis throughout both files is that the field has characteristic zero or greater than \(p=m+r\); no other arithmetic exclusions occur.

## How many incoming rows a clock-invariant space consumes

Suppose \(U\subseteq F_j\) is \(C\)-invariant and separation holds through \(j\). Compress on \(H=P_{\le j}(c)\oplus U\). Restricting the actual \(F_{j+1}\) vectors need not preserve their rank; it can only lower it. The compressed \(U\) has the same dimension as before and splits by clock. Its annihilator in the rows of the full compressed coordinate space consists of exactly \(j+1\) clock-supported normalized rows \(\lambda_x\), by the single-block argument in the first proof. In particular \(\lambda_0=e_1^{\mathsf T}\), and the latest nonzero indices of the other \(j\) normalized rows are all distinct.

The restrictions of the *first* \(M=\lfloor(j+1)/2\rfloor\) nonzero-clock rows to the restriction of \(F_{j+1}\) are independent. Indeed, suppose a nonzero linear combination \(\lambda\) of them kills this space and let \(u\) be the latest clock in that combination by last physical index. Then \(\lambda A\) kills \(U\) since \(AU\subseteq F_{j+1}\), and is supported strictly before the last index for \(u\). Thus it is a linear combination of normalized rows completed earlier. Form
\[
 P(x)=x^2\prod_{v}(x-v)^2 ,
\]
where the product is over *all* earlier completed nonzero represented clocks. There are at most \(M-1\) of these. Thus \(\deg P'\le 2M-1\le j\), and \(P'\) vanishes at every earlier completed clock, including zero. But \(\lambda P(c)\ne0\) because only its nonzero coefficient at \(u\) survives. This contradicts \(\lambda(AP'(c)-P(c))=0\). In this argument the compressed \(A\) is applied to restricted inputs in \(H\), so its output agrees with the restriction of the original \(A\) even if that output is not in \(H\). All \(\lambda_x\) kill \(U\). Consequently
\[
 \dim F_{j+1}\ge \dim U+\lfloor(j+1)/2\rfloor.                    \tag{2}
\]
In particular a flat increment of one at \(j\ge3\) precludes \(F_j\) itself being \(C\)-invariant.

We also need a bound at an invariant *endpoint*. If \(F_k\) is \(C\)-invariant for \(k\ge5\) within separation, compress on the full \(E_k\) and form its \(k\) nonzero normalized rows. For each such clock \(x\), with last physical index \(i_x\), the row \(\lambda_x A\) integrates every profile of degree at most \(k-1\) up to \(x\), because \(\lambda_x\) applied to any profile through degree \(k\) gives its exact polynomial evaluated at \(x\). The strict prefix of \(i_x-1\) rows therefore yields an actual ordinary order-\(k\) method after dividing \(A\) and \(\lambda_x A\) by \(x\), by homogeneity. The baseline (1) in the companion, specialized to \(m=0,r=k\), implies \(i_x\ge\lceil3k/2\rceil-1\). There are \(k\) distinct such indices, and \(\dim E_k=k+1+\dim F_k\) is the full compressed length. Hence
\[
 \dim F_k\ \ge\ \lceil3k/2\rceil-3 .                             \tag{3}
\]

## What a whole interval of minimal increments would imply

Fix \(j\ge5\) with \(2j\le q\); in particular \(4j\le r\le p\). Suppose each of the \(j\) increments of \(\dim F_a\) from \(a=j\) to \(a=2j\) equals one. We show \(F_{2j}\) is \(C\)-invariant. By (2) none of \(F_j,\ldots,F_{2j-1}\) is invariant. Suppose, to the contrary, the endpoint also is not invariant. Write \(W=F_j\), and \(U\) for the largest \(C\)-invariant subspace of \(W\). Because \(\dim(W+CW)=\dim W+1\), there is a \(w\) such that, with \(k=\dim(W/U)\),
\[
 F_{j+a}=U\oplus w P_{\le k+a-1}(c),\qquad 0\le a\le j.         \tag{4}
\]
Here \(wP_{\le b}(c)\) denotes the span of \(w,Cw,\ldots,C^bw\). For the initial equality, set \(W_i=\{v:C^\ell v\in W,\ 0\le\ell\le i\}\). The first codimension is one, and \(C:W_i/W_{i+1}\to W_{i-1}/W_i\) is injective. There are \(k\) drops by one until the filtration stabilizes at \(U\). Taking \(w\in W_{k-1}\setminus W_k\) yields all \(k\) quotient pivots. Subsequent \(C\) powers supply the unique new direction at each flat increment, unless the chain has already saturated; saturation would make that entire \(F_{j+a}\) invariant. By the assumed endpoint noninvariance there are at least \(N\ge k+j+1\) effective clock values, those where the projection of \(w\) on that block is nonzero modulo \(U\). This follows by the usual polynomial interpolation on distinct clock values, also over a finite field. Formula (2) gives \(k+1\ge\lfloor(j+1)/2\rfloor\), so \(k\ge2\).

For every \(f\in W\), multiplication by \(f\) is a diagonal operator \(D_f\) that maps \(W\) into \(F_{2j}\) by the actual product rule for pairs. Each \(D_f\) preserves \(U\). Indeed take a member of \(U\) supported on one clock, which is enough because \(U\) is \(C\)-invariant. Its image is still supported on this clock. In the decomposition (4), its polynomial coefficient on the chain must vanish at all of the other effective clocks. There are at least \(N-1>k+j-1\) of them, so that polynomial is zero.

Choose a complement to \(U\) invariant under \(C\) and all \(D_f\). This requires no inner product, extension of the scalar field or averaging: split the coordinates into the joint blocks where all these diagonals take identical values, and take an arbitrary complement to the corresponding piece of \(U\) on each block. Polynomial interpolation for each diagonal followed by multiplication of the projectors gives the joint projections. There are only finitely many blocks and finitely many diagonals suffice to distinguish them. Replace \(w\) by its complementary projection, which differs by an element of \(U\). Then every \(D_fw\) is \(P_f(c)w\) with \(\deg P_f\le k+j-1\), and the effective clocks are precisely the distinct clocks on the support \(S\) of \(w\).

In fact \(\deg P_f\le j\). For \(t=1,\ldots,k-1\), \(C^t D_fw=D_f C^tw\in F_{2j}\) lies in the complement, hence it too has a polynomial representative of degree at most \(k+j-1\). At step \(t\), the previous bound makes \(\deg(x^tP_f)\le k+j\), which is less than \(N\). Agreement at the \(N\) support clocks therefore forces \(\deg P_f\le k+j-1-t\). In particular a member \(f\in U\) supported on one clock vanishes everywhere on \(S\), since its polynomial there vanishes at the \(N-1>j\) other support clocks. Hence every member of \(U\) vanishes on \(S\). Taking \(f=w\) gives \(w_i=P(c_i)\) on \(S\) for a nonzero polynomial \(P\) of degree at most \(j\). Next \(f=C^{k-1}w\in W\). Its degree-at-most-\(j\) representative on \(S\) equals \(x^{k-1}P\) identically, since the latter degree is \(<N\). Therefore \(\deg P\le j-k+1\le j-1\).

For \(Q=x\) and then \(Q=x(x-u)\), form \(z_Q=(QP)(c)-Q(C)w\), whose exact polynomial is nonzero \(QP\) through degree \(j+\deg Q\le2j\). Separation forces \(z_Q\notin U\). Let \(i\) be the earliest index where the prefix of \(z_Q\) through \(i\) fails to equal a prefix from \(U\); take \(v\in U\) matching up to \(i-1\). The new mismatch lies outside \(S\), since \(z_Q\) and \(U\) vanish there on \(S\). The clock-block splitting of \(U\) supplies a separating row \(\lambda\) supported on this prefix, on the single clock \(\xi=c_i\) and outside \(S\), that kills \(U\) but not \(z_Q\). To see this, on that clock block the restriction of \(z_Q\) is not in the restricted \(U\); omit its already-zero \(S\) coordinates and separate in finite-dimensional linear algebra. On its support \(z_Q=Q(\xi)P(\xi)\mathbf1\), so \(\lambda\mathbf1,Q(\xi),P(\xi)\) are nonzero. By (4) the row kills all of \(F_{2j}\).

For \(\deg R\le j-\deg Q-1\), \(R(C)z_Q\) agrees with \(R(C)v\) before \(i\). By strict chronology \(\lambda A R(C)z_Q=\lambda A R(C)v=0\): \(R(C)v\in U\), and \(AU\subseteq F_{j+1}\). Testing the polynomial component of the same primitive, whose pair costs at most \(2j\), gives \(J(RQP)(\xi)=0\). The first contrast therefore yields \(u\ne0\), the second \(v'\notin\{0,u\}\). No ordering or midpoint argument is needed.

## Why the two endpoint tests cannot occur in an admissible characteristic

Set \(l=j-1\) and rescale the variable by \(u\), so \(a=v'/u\notin\{0,1\}\). Retain \(P\) for the rescaled polynomial, still nonzero of degree at most \(l\). The two tests say
\[
 \int_0^1 xRP=0\quad(\deg R<l),\qquad
 \int_0^a x(x-1)RP=0\quad(\deg R\le l-2).
\]
The first has a one-dimensional solution space by the shifted moment determinant at \(a=1,b=0,h=l\) in the companion (here \(a\) in the determinant is its integer index). Let \(H=x^{l+1}(x-1)^l\). Then \(H^{(l)}/x\) is a nonzero polynomial of degree \(l\): its leading coefficient is \((2l+1)!/(l+1)!\). It spans the solution space by \(l\) integrations by parts, since the derivatives of \(H\) below order \(l\) vanish at zero and one. Thus \(xP\) is a nonzero multiple of \(H^{(l)}\).

The second test says the functional \(T(V)=\int_0^a V H^{(l)}\) on \(\deg V<l\) vanishes whenever \(V(1)=0\). Consequently \(T(V)=\lambda V(1)\) on that whole space. Substituting \(V=(x-a)^k\) and integrating by parts \(l\) times gives
\[
 (-1)^k k! H^{(l-1-k)}(a)=\lambda(1-a)^k,\qquad 0\le k<l.
\]
It follows that \(H\) agrees modulo \((x-a)^l\) with \(\lambda(x-1)^{l-1}/(l-1)!\): these derivatives determine all coefficients of the jet because factorials through \(l\) are units. Dividing by the unit \((x-1)^{l-1}\) in the truncated polynomial ring shows \(x^{l+1}(x-1)\) is constant modulo \((x-a)^l\). Since \(l\ge4\), both first and second derivatives must vanish at \(a\). But the first derivative \(x^l((l+2)x-(l+1))\) has only a simple zero away from zero: at that root its derivative is \((l+2)a^l\ne0\). This contradiction is valid in every admissible characteristic. The primitives, moments, derivatives and leading coefficient here need only integers through \(2l+1=2j-1\), already smaller than \(p\). All variable denominators elsewhere come only from invertible differences of distinct elements or nonzero field pivots.

## Summing the surplus

Write \(\delta(k)=\dim F_k-k\); it is nondecreasing through \(q\) by strict growth. At \(k=5\) the companion proves \(\delta(5)\ge0\). Suppose \(\delta(j)\ge i\) for \(j=5\,2^i\) and \(2j\le q\). If an increment exceeds one before \(2j\), \(\delta(2j)\ge i+1\). Otherwise \(F_{2j}\) is invariant by the two-contrast argument, and (3) gives \(\delta(2j)\ge j-3\ge i+1\). Induction and monotonicity give \(\delta(q)\ge h\). Substitution in the companion's (1) proves the theorem. The residue-field reduction there transfers this conclusion to nonzero commutative rings without assuming that some characteristic-zero quotient exists. For an ordinary tableau in a field the result localizes at every actual Beta tap, with \(r=p-m\) in the formula.
