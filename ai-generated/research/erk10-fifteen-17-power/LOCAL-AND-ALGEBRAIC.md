# Local and algebraic coefficient domains for the 17-adic geometry

The [five-equation construction](README.md) gives a strictly
explicit 15-stage method of exact order ten over **every
nonzero henselian local commutative ring with residue
characteristic 17**. The residue field need not be the
prime field, and the coefficient ring need not admit a
map from the complete integers \(\mathbb Z_{17}\).

Indeed fix \(d=8\). Regard the five displayed geometry
equations as polynomials over \(\mathbb Z_{(17)}\) in
\((a,c,e,f,g)\). All formal-integral denominators
\(1,\ldots,10\) and the other scalar denominators in the
equations (including \(12\) and \(20\)) are prime to 17.
They are units in the local ring because their residue
images are nonzero. The canonical prime subfield of its
residue field contains the solution
\((a,c,e,f,g)=(16,2,9,4,6)\) with Jacobian determinant
\(10\). The multivariate simple-root Hensel property
lifts this solution into the local ring. Equivalently,
the polynomial system localized at this determinant is
étale near the point, and the henselian lifting property
applies.

All further divisions in the literal reconstruction
are by units. The clock differences and cardinal
integrals are nonzero in the prime residue; the first
four, five and six reverse read systems are invertible
there; the extra donor, observer-coordinate and
forward-kernel pivots reduce to the same explicit
nonzero scalars as in the main packet. The opening
clock and decoder pivots are likewise units. Thus the
same weighted-transpose and actual rooted proofs work,
without cancelling any possible zero divisor.
The reconstructed tableau reduces to the
[published F17 literal](../erk10-fifteen-f17/tableau.json)
over the prime subfield. In particular its explicit
eleven-vertex bush defect reduces to \(8\), so it is
a unit and ordinary order eleven is impossible in the
nonzero ring. This is a local henselian result, not a
claim about all local rings of residue characteristic 17.

In characteristic zero one may also take a **finite
extension of \(\mathbb Q\) embedded in
\(\mathbb Q_{17}\)**. To see this, take the simple root
in \(\mathbb Z_{17}\) with \(d=8\), and put
\(K=\mathbb Q(a,c,e,f,g)\subset\mathbb Q_{17}\).
The same Jacobian is invertible over \(K\). Apply the
universal \(\mathbb Q\)-derivation to the five equations:
it yields that this Jacobian times the five coordinate
differentials is zero. Thus every coordinate differential
vanishes. Since \(K\) is finitely generated in characteristic
zero, \(\dim_K\Omega_{K/\mathbb Q}=\operatorname{trdeg}_{\mathbb Q}K\),
and all the differentials of its generators being zero
gives transcendence degree zero. Therefore \(K/\mathbb Q\)
is finite algebraic. All tableau coefficients are rational
functions of these coordinates with the verified nonzero
pivots, so they lie in \(K\) and keep their exact order by
the same construction. This argument supplies no bound on
the minimum field degree or its archimedean embeddings,
and it does not give a rational tableau.

These corollaries are mathematical consequences of the
exact geometry certificate, not additional Lean
HasOrder theorems.
