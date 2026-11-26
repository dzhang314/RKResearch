# A sharp width bound for dense explicit Runge–Kutta charts

An explicit Runge–Kutta method of ordinary order at least six, or a strictly explicit tableau admitting an exact dense derivative decoder through tree size six, has at least five independent pure defects through size six over any field in which \(5!\) is a unit. No restriction on the support of its quadratic stage residual is needed.

For dense decoding through size \(m\ge6\), the result gives \(s\ge 2m-1\) stages. The same bound holds with coefficients in any nonzero commutative ring in which \((m-1)!\) is a unit, provided the decoder is linear over the coefficient ring on all stage data. At size six the [eleven-row construction](../erk-single-quadratic-defect/REPAIRED-ELEVEN-ROW-DENSE-SIX.md) attains the bound. This is a dense decoding minimum. An ordinary Runge–Kutta output is a scalar functional and need not recover all the derivative polynomials.

## The rank argument

For a tree \(t\), let \(\gamma_t\) be the product of the factorials of the trees attached to its root, so \(t!=|t|\gamma_t\) as integers. Define
\[
F_j\coloneqq
\operatorname{span}
\left\{\boldsymbol{\Phi}_t(A)-
\frac{\mathbf c^{\odot(|t|-1)}}{\gamma_t}: |t|\le j\right\}.
\]
This is the space of actual stage vectors obtained from formal tree combinations with zero exact polynomial. It suffices to subtract the appropriate multiple of the bush of each size, because the exact tree polynomials of that size are all multiples of the same monomial. The denominator \(\gamma_t\), not necessarily \(t!\), is a unit for \(|t|\le m\) when \((m-1)!\) is a unit.

The quadratic residual is nonzero: the first nonzero clock has no nonzero-clock predecessor, and its quadratic residual entry is minus its clock squared. The [chronological rank argument](../erk-signed-reverse/CHRONOLOGICAL-DEFECT-CHARGE.md) gives strict growth between successive \(F_j\). Hence the only way to have fewer than five dimensions in \(F_6\) is to have dimensions \(1,2,3,4\) through sizes three, four, five, six. The three case arguments rule this out according to the number of distinct clocks at which the quadratic residual is nonzero:

- [One clock, including multiple physical rows](ONE-DEFECT-CLOCK-MULTIPLE-ROWS.md)
- [Two clocks](TWO-DEFECT-CLOCKS.md)
- [At least three clocks](MULTIPLE-CLOCK-DEFECT-FLOOR.md)

Once the pure dimension at size six is at least five, strict growth gives \(\dim F_m\ge m-1\). A dense decoder has \(m\) independent exact monomial images through size \(m\), and it annihilates \(F_m\). This gives \(s\ge(m-1)+m\).

Over a nonzero commutative ring, specialize at a maximal ideal. The actual linear decoder and its identities specialize, so the field stage bound holds. At size six, the \(5\times5\) minors of the finite defect generator matrix generate the unit ideal because they cannot all vanish in any residue field. This does not assert a particular free direct-sum decomposition over the ring.

The case arguments were independently checked. These are mathematical proofs, not new Lean certificates.
