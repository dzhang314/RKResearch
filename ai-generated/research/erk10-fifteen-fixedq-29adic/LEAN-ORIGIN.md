# Native proof of the true origin residual

This adds the pre-cancellation scalar origin equation to the
[fixed-q scalar packet](LEAN-SCALARS.md). Write \(D=7257600\)
for the quadrature denominator, and set

\[
\begin{aligned}
H_d(c)&=8980-31725c+32120c^2,\\
F_d(c)&=2102470-14896392c+42748688c^2-61086000c^3+36040380c^4.
\end{aligned}
\]

The associated numerators and these denominators are connected
in Lean to the original \(h\) and \(f\) moment averages, by
**h_clear** and **f_clear**. The original origin residual is
\(A_{\rm org}(c)=j(c)+(1-2/c)k(c)\) with the raw formulas
in the scalar module, not a reduced rational function selected
after the fact.

The theorem **origin_clear** verifies the exact identity
\[
       D\,c\,H_d(c)\,F_d(c)\,A_{\rm org}(c)=-2880\,P(c)
\]
over any commutative ring satisfying the stated scalar payment
conditions. It uses the algebraic expansion of the original
integrals and exact finite symbolic polynomial arithmetic; no
finite residue testing substitutes for that identity.

When the residue map to \(\mathbb F_{29}\) reflects units and
\(c\) reduces to 2, the cleared denominators \(H_d(c),F_d(c)\)
reduce to \(2,17\). **origin_zero_of_decic** therefore proves
the actual origin scalar vanishes at any such exact decic root.

All these statements are in namespace
**RKResearch.Certified.ERK10FixedQ29Adic**. Lean/Mathlib 4.36.0
checked the endpoint using standard axioms only. This proof does
not establish the remaining \(h\)-phase contact, weighted quartic
remainder proportionality, coefficient reconstruction, or rooted
order through ten.

From the repository root:

    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.ERK10FixedQ29AdicOrigin:olean

Check the source manifest from the repository root:

    sha256sum -c ai-generated/research/erk10-fifteen-fixedq-29adic/lean-origin-sha256.txt
