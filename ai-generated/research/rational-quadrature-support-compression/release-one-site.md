# An irreducible forced cubic makes a one-site relaxation arithmetically finite

**Result.** Only finitely many rational 17-site uniform quadratures paying all 20 moments can contain at least 13 out of the fourteen particular rational sites in the canonical interval prefix described in **compression.md**. This applies without any sign or interval restriction on the new sites or weights. It does not decide whether any such rule exists, determine an effective bound or classify general 17-site rules. This is a source-level proof, not a Lean or general RK stage result. The arithmetic finiteness conclusion uses Faltings's theorem. The pencil, irreducible resolvent, local obstruction and monodromy deductions do not.

## Reusable hypotheses and the explicit quartic

Work over \(\mathbb Q\). Let \(H\) be a monic product of \(b\) distinct rational linear factors, and \(L\) a rational-moment functional. Suppose the three-by-three matrix \(M_{ij}=L(HX^{i+j})\), \(0\le i,j\le2\), is invertible, and the unique monic cubic \(C\) satisfying \(L(HX^j C)=0\) for \(0\le j\le2\) is irreducible over \(\mathbb Q\). We seek \(b+3\) rational nodes paying \(b+6\) moments. At the full prefix there are none because \(C\) does not split.

Choose any one of the fixed sites \(a\) to release and put \(H_a=H/(X-a)\). Let \(c\) solve \(M c=(L(H_a X^i))_{0\le i\le2}\) and set
\[
 V_a(X)=1-(X-a)\sum_{j=0}^{2}c_jX^j,\qquad A_a(X)=(X-a)C(X).
\]
All the monic quartic candidates at the remaining \(b-1\) sites are exactly
\[
        F_t(X)=A_a(X)+tV_a(X),\qquad t\in\mathbb Q .
\]
Indeed \(V_a(a)=1\) and \(L(H_aX^jV_a)=0\) for the three rows by construction. \(A_a\) also pays these rows. For any monic solution subtract \(A_a+tV_a\) with \(t=F_t(a)\) (that is, the value at \(a\) of the proposed quartic). The degree-\(\le3\) difference vanishes at \(a\); dividing by \(X-a\) gives degree \(\le2\) and zero moments under \(H\), hence the difference vanishes by invertibility of \(M\).

If \(L(H_a C)=0\), the recursion \(L(H_a X^{j+1} C)=a L(H_a X^j C)+L(H X^j C)\) shows that \(C\) itself occupies the one-dimensional direction. Since \(C(a)\ne0\), \(V_a=C/C(a)\). Every candidate retains this irreducible factor, so none splits. Otherwise \(A_a\) and \(V_a\) are coprime: \(V_a(a)=1\), and if \(C\mid V_a\) then \(V_a\) is a nonzero multiple of \(C\) with \(L(H_a C)=0\), impossible. In the numerical application the latter, nondegenerate case holds for *all fourteen* \(a\), by the single canonical cofactor-product receipt \(727220578\bmod 2147483647\).

## A resolvent and a local test without point searches

Write the monic quartic as \(X^4+B_tX^3+C_tX^2+D_tX+E_t\). Its ordinary three-pairing resolvent is
\[
 R_t(Y)=Y^3-C_tY^2+(B_tD_t-4E_t)Y+(4C_tE_t-B_t^2E_t-D_t^2).
\]
For roots \(r_1,\ldots,r_4\), its three roots are \(r_i r_j+r_k r_l\) for the three unordered partitions into two pairs. They are distinct whenever the quartic is squarefree: the difference of two of these products is a product of two nonzero differences of quartic roots, up to sign. At \(t=0\), one root is \(a\) and the other three are the conjugates of the irreducible cubic \(C\). The matching is identified with the partner paired with \(a\), so the Galois group acts transitively on the three resolvent roots. Therefore \(R_0\) is irreducible. As \(R_t\) is monic with coefficients in \(\mathbb Q[t]\), a proper monic factorization over \(\mathbb Q(t)\) would have coefficients in the integrally closed ring \(\mathbb Q[t]\) and specialize to a proper monic factorization at zero. It follows that \(R_t\) is irreducible over \(\mathbb Q(t)\). This gives an explicit plane cubic necessary condition \(R_t(y)=0\) for a rational split fiber (total degree at most three); it is not by itself sufficient.

In the numerical application \(M^{-1}\), \(H_a\), \(C\), \(a\), and thus \(V_a\), are integral at the specified prime \(q\). For every \(t\in q\mathbb Z_{(q)}\) the fiber reduces to \((X-\bar a)\bar C\), with \(\bar C\) irreducible cubic. Such a monic fiber cannot split rationally. This entire forbidden \(q\)-adic parameter neighborhood holds simultaneously for each release \(a\); it does not exclude the other parameter values.

## The splitting curve, including the constant-field issue

In the coprime case \(F_t=A_a+tV_a\) is irreducible over \(\mathbb Q(t)\): it is a primitive polynomial linear in \(t\) over \(\mathbb Q[X]\) (coprime \(A_a,V_a\)), hence irreducible in \(\mathbb Q[X,t]\); it is monic, so also primitive as a polynomial in \(X\) over \(\mathbb Q[t]\). Its splitting-field group \(\Gamma\) acts transitively on the four roots, and, by the irreducible resolvent, transitively on the three matchings. Consequently \(12\mid|\Gamma|\); as \(\Gamma\le S_4\), it must be \(A_4\) or \(S_4\). In particular the degree-four map cannot be decomposed into two rational degree-two maps over \(\mathbb Q\), because either group's action on the four letters is primitive. No unproved generic-simple-branching hypothesis is needed.

Let \(K\) be the splitting field over \(\mathbb Q(t)\). If there is not even one distinct completely rational split fiber, there is nothing to count. Otherwise at such a value \(t_0\), the four simple rational roots each lift uniquely to a power series in \(\mathbb Q[[t-t_0]]\) (Hensel's lemma). Thus \(K\) embeds over the base into \(\mathbb Q((t-t_0))\), has a place with residue field \(\mathbb Q\), and has constant field exactly \(\mathbb Q\). For the last assertion, any element algebraic over \(\mathbb Q\) in this Laurent field has vanishing formal derivative in characteristic zero, hence is an actual rational constant. So \(K\) is the function field of a smooth projective geometrically integral curve \(S/\mathbb Q\), with a rational point above \(t_0\). The full group \(\Gamma\) acts faithfully by \(\mathbb Q\)-automorphisms of \(S\).

* If \(S\) had genus zero, its rational point identifies it with \(\mathbb P^1\). Any finite subgroup of \({\rm PGL}_2(\mathbb R)\) has a cyclic subgroup of index at most two. Indeed its orientation-preserving subgroup acts on a circle; after averaging a metric over that finite group it acts by rotations. Neither \(A_4\) nor \(S_4\) has a cyclic subgroup of index at most two.
* If \(S\) had genus one, select its rational point as origin. Its rational automorphism group is translations by \(S(\mathbb Q)\) semidirect the origin-preserving automorphisms. In characteristic zero those fixing the origin act faithfully on its tangent line (for example, lift the complex elliptic curve to its complex torus and note that the derivative determines the linear lift). Their rational derivatives are roots of unity in \(\mathbb Q^\times\), so they have order at most two as a group. Every finite subgroup of \({\rm Aut}_{\mathbb Q}(S)\) therefore has an abelian subgroup of index at most two. \(A_4\) has no index-two subgroup and is nonabelian; \(S_4\)'s unique index-two subgroup is the nonabelian \(A_4\). Both are impossible.

Thus the existence of one admissible split fiber forces genus at least two. Faltings's theorem then says \(S(\mathbb Q)\) is finite. Every completely split squarefree rational fiber has a rational place above it by precisely the same lifting argument, so there are only finitely many. This argument is also valid when no rational point exists, because then there are no such fibers; it does not tacitly assume the arithmetic and geometric monodromy groups coincide before the rational-place argument.

A candidate with distinct active new sites is a subset of these squarefree split fibers; the monic quartic and the remaining \(H_a\) determine all the quadrature weights uniquely. Taking the finite union over the fixed choices \(a\) proves the assertion. It excludes a nonconstant rational or elliptic family of rational split solutions along any such release, but supplies neither a solution nor an effective search bound. Dropping two or more of these fourteen fixed nodes is outside its conclusion.
