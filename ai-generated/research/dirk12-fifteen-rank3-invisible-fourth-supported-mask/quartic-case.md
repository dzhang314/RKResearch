# Exact exclusion of a quartic ghost-zero mask

Use the scope and notation of the [fourth-supported mask](README.md). If \(M(P)=0\), work with normalized \(T=X/a\), \(x=b/a,\ y=c/a,\ t=e/a\), and put \(P_0=T(T-1)(T-x)(T-y)\). A zero actual fourth diagonal forces both \(\mathcal A(P_0)(t)=0\) and \(\mathcal A(TP_0)(t)=0\): all earlier available ordinary live scalar values vanish and its own coefficient is zero. Here \(\mathcal A\) is normalized by \(1/a\) along with the physical matrix. The expressions of degree at most seven are known exactly from the geometry-free first three rows. Divide both by the monic \(P_0\); their zeros at its four roots are guaranteed by literal chronology and the vanishing origin factor. Call the two quotient equations \(T_2(t)=T_3(t)=0\).

## Characteristic-zero projection

Use \(J\) for integration from zero and \(\mathcal I(G)=JG(1)\). In the first nonroot case \(M\) is a nonzero multiple of \(\mathcal D(G)=JG(x)-R(x)\mathcal I(G)\) on \(G(0)=G(1)=0\), where \(R(s)=s L_6'(a s)/L_6'(a)\). For the quartic \(P_0\), \(\mathcal D(P_0)=x^3(x-1)^3(2xy-x-y)/(6(2x-1))\). Thus \(y=x/(2x-1)\), using the actual nonroot guards. In the first-root case \(M\) is proportional to \(\mathcal I\), and \(\mathcal I(P_0)=-(10xy-5x-5y+3)/60\). The vanishing equation excludes \(x=1/2\) and determines \(y=(5x-3)/(10x-5)\).

The exact [third-clock gates](../dirk12-fifteen-rank3-invisible-all-ordinary-prefixes/README.md), with the respective Möbius substitutions, give two polynomials in \(a,x\). In the nonroot case remove the factors \(x-1\) and \(x(x-1)^2\) from the two gates; these are excluded by distinct nonzero clocks. The remaining two polynomials each have degree five in \(a\). Their \(a\)-resultant has factors \(x^{15}(x-1)^5(2x^2-2x+1)^2\) times the retained \(x\)-factor of degree \(26\), up to a nonzero rational scalar. The quadratic is strictly positive on the reals.

In the first-root case start from \(L_6'(a)=0\) and remove the factors \(5x^2-5x+1\) and \(10x^2-10x+3\) from the cleared third gate. The former is excluded by the genuine first-root second pivot and the latter is positive. The \(a\)-resultant has factors \((x-1)^5(5x-2)^5\) times the retained \(x\)-factors of degrees \(8,32\), up to nonzero rational scalar. Clock distinctness excludes \(x=1\) and \(x=2/5\) (the latter gives \(y=1\)). For both branches the exact degree-one subresultant in \(a\) is carried along, with its two coefficients. As a Sylvester subresultant it vanishes at any literal common root, including a possible characteristic-zero degree drop in the inputs.

## Unit-leading specialization, not reduction of a tableau

For the degree-26, degree-8 and degree-32 scalar projections, choose primes \(17,17,19\), respectively. Their reductions have the same degrees and the following irreducible field factors:
\[
                 [13,13],\qquad [4,4],\qquad [4,4,24].
\]
In each residue field the coefficient of \(a\) in the carried linear subresultant is a unit. For an actual algebraic root \(x\), choose any valuation above the indicated prime in a number field containing the coordinates. The degree-preserving base polynomial makes \(x\) integral at that prime; the unit linear coefficient makes \(a\) integral and forces its listed formula. The Möbius denominator for \(y\), and all scalar denominators used in the two quotient equations, are units in each field. This includes the three-mode interpolation determinant, tested by the actual pivot operations; monic polynomial quotients reduce coefficientwise. The receipt checks that \(T_2\) retains degree two, its maximum possible degree since the quartic is a true grade-five ghost-zero mask and its primitive has degree at most six. Its leading coefficient is a unit, so a putative root \(t\) is integral above the same prime. In every residue field \(T_2,T_3\) have degrees \(2,3\) and are coprime by a literal Bézout identity. Hence no such integral \(t\) exists. This argument reduces only monic scalar coefficient algebras, not unknown tableau entries or algebraic ghost clocks.

The degree-two and -three prescriptions in the replay use \(JP_0-R\mathcal I(P_0)\) and \(J(TP_0)-R\mathcal I(TP_0)-V\mathcal D(TP_0)\) for the two nonroot primitive numerators. At a first Legendre root use \(JP_0-k\mathcal I(TP_0)\) and \(J(TP_0)-r\mathcal I(TP_0)-k[\mathcal I(T^2P_0)-\epsilon]\), with the actual \(r,k,\epsilon\) from the first-three solve. The upper degree of \(T_3\) is always three. The other scalar gates and positive-polynomial discards are in the exact characteristic-zero rebuild.

    python3 -B rebuild-quartic.py    # SymPy; regenerates/checks the JSON
    python3 -B verify-quartic.py     # independent standard-library field replay

The portable Lean receipts check the literal modular Bézout identities and the individual unit inverses; they do not reimplement the coefficient eliminants or the actual graded tableau argument.
