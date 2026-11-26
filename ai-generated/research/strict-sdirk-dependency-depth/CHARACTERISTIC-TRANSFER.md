# Paid-characteristic transfer of the local arithmetic floor

This audits the original seven-clock common-diagonal floor at \(p\ge15\).
It is mathematics and a Lean interface plan only. The companion
SCHUR-FREE-FLOOR.md gives a separate replacement for its characteristic-zero
block, not a claim that Schur irreducibility itself transfers.

## 1. Paid integers, bounded model, and local algebra

Work over a nontrivial commutative ring \(R\) and use the literal
denominator-cleared HasOrder through \(p\). The order-\(n\) bush gives
\[
 (n:R)\bigl(\mathbf b\cdot\mathbf c^{\odot(n-1)}\bigr)=1
 \qquad(1\le n\le p).
\]
Thus every displayed cast, and \(p!\), is a unit. Any residue field
has characteristic zero or prime \(\ell>p\); the same holds for any
field image. These are consequences of payment, not extra characteristic
assumptions.

The word model only needs the window of polynomials through degree
\(p-1\). Set \(X x^k=x^{k+1}\) and \(Jx^k=x^{k+1}/(k+1)\) for
\(k<p-1\), set both to zero on \(x^{p-1}\), and set the
scalar output on \(x^k\) to \(1/(k+1)\). These prescriptions use only
paid inverses. A word paid through \(p\) never loses a term to the
truncation. The identities
\([X,J^r]=rJ^{r+1}\) follow on monomials, and the diagonal shift is
the literal \(T=J-\gamma I\). One must not invoke an unbounded formal
antiderivative or exponential as a power series over positive
characteristic.

Equivalently put
\[
 A_j(\gamma)\coloneqq
 \sum_{u=0}^j\binom ju\frac{(j+1)!}{(u+1)!}(-\gamma)^{j-u}
 \in\mathbb Z[\gamma].
\]
Each factorial quotient here is an integer, or a product of consecutive
integers. Expanding the actual \(B^j\) and using the paid tall terms
gives the exact cleared equality
\[
 (j+1)!\,(\mathbf b\cdot B^j\mathbf1)=A_j(\gamma)
 \qquad(j+1\le p).
\]
The tall recurrence can first be verified as the integral polynomial
identity
\[
 A_{j+1}=(1-2(j+1)\gamma)A_j-j(j+1)\gamma^2 A_{j-1},
 \quad A_0=1,\quad A_1=1-2\gamma.
\]
For instance clear the known rational coefficient identity and use
the embedding of integer coefficients into the rationals. Only then
evaluate in \(R\) and use the paid factorial units. This gives the
published recurrence in its claimed range, not equality with unpaid
tableau moments. The usual nonzero-diagonal scalar cap \(s\ge p-1\)
over a field follows: if \(p\ge s+2\), the two paid values from
\(B^s=B^{s+1}=0\) would force all earlier values to vanish.
Division in the descent uses only the positive recurrence indices
and the nonzero field element \(\gamma\).

For a field with the paid units, the cyclic rectangle and its clock
classification are unchanged, as are the seven-clock local placements.
The clock comparisons in the rectangle subtract physical indices
whose distinct differences have absolute value at most \(p\);
their casts are units. In the local proof one divides only by the
nonzero \(L\), its actual adjacent factors, the nonzero scope-specific
clock step when needed, and paid small factorials. The surviving value
of a mark is exactly \(\delta^d d!\). The explicit coefficients in
\(F_1,F_2,F_3\) and the odd-part determinant require only 2 and 3 as
integer denominators. The determinant test and the two exceptional
slopes are therefore valid over such a field.

The fixed-quadratic recurrence rejection is also characteristic-safe.
The distinct-root shift calculation uses only the nonzero root
difference; its residual sequence has a monic recurrence of length
four. The repeated-root case uses a degree-at-most-two polynomial
at the first three distinct indices. The zero-root cases use the paid
units \(m\) and \(m-1\), where \(m\) is the reverse recurrence size.
The affine geometric residual has slope \(-(1+r)^2\) and value
\(\xi\) at \(r=-1\), with \(\xi=\gamma^{-1}\ne0\).
The two exceptional-slope arguments use only the same reverse recurrence,
2 as denominator, and field division at their explicit nonzero pivots.
There is no ordered-field or infinite-field step. Four residual rows
already suffice if the fixed recurrence is known through \(m_5\).

At \(\gamma=0\), the tall bound and cyclic rectangle give the strict
ERK floor \(s\ge p+1\) for \(p\ge5\) in these fields. At equality
\(s=p\), \(L=1/s!\) is a unit and the published obstruction reduces
to \(M=sL=4L\). The positive cast \(s-4\) is a paid unit. This
argument needs no Schur condition.

## 2. Precisely where the original proof needs a new certificate

After the scalar cap, the only sizes to exclude for its \(p\ge15\)
floor are \(s=p-1\) and \(s=p\). In the original proof the nonlinear
saturation step at \(s=p-1\), and the longest-chain noncancellation
step at \(s=p\), both invoke one and the same polynomial exclusion
with index \(m=p-1\). The first-row branching calculation and the
early broken-edge penultimate-slot calculation already produce
their polynomials using only paid integers and the stated nonzero
field pivots. The latter is not a second independent Schur condition.

The exact integer pair, with \(X=\gamma^{-1}\), is
\[
 \begin{aligned}
 F_m(X)&=\sum_{j=0}^m(-1)^{m-j}\binom mj
                \frac{(m+1)!}{(j+1)!}X^j,\\
 N_m(X)&=(m+1)(X-2)^3-4m(m-1)(X-2)^2\\
       &\qquad+2(m-3)(m-1)^2(X-2)+4(m-1)^3 .
 \end{aligned}
\]
The first is monic and comes from \(\lambda_m=0\);
the second is the cleared cubic at \(t=(X-2)/(m-1)\).
Define the single integer
\[
 \mathcal R_m\coloneqq\operatorname{Res}_X(F_m,N_m).
\]
Schur over the rationals gives \(\mathcal R_m\ne0\) for \(m\ge4\).
It does not give the degree of a root after reduction to a finite
prime field. The exact sufficient prime condition for replaying the
original proof is
\[
                    \ell>p,\qquad \ell\nmid\mathcal R_{p-1}.
\]
At a paid prime \(\ell>p\) dividing this determinant, the two
polynomials do have a common root over the algebraic closure of the
prime field;
\(F_m(0)=(-1)^m(m+1)!\) is a paid unit, so the common root is
nonzero. Thus this particular polynomial-pair argument alone cannot
exclude such a \(\gamma\) uniformly over all extensions of that field.
This does not assert that there is a bad prime larger than \(p\) at
a specified order, a common root in every field of that characteristic,
or any tableau realizing a common root.

An explicit finite integral version does not need a polynomial
quotient type: form the \(m\)-by-\(m\) matrix whose column \(j\) is the
coefficient vector of the monic remainder of \(X^jN_m\) modulo
\(F_m\), for \(0\le j<m\). Its determinant is \(\mathcal R_m\).
At a common root \(x\) over any commutative ring, the evaluation row
\((1,x,\ldots,x^{m-1})\) annihilates that matrix. Right multiplication
by its adjugate shows that the image of the integer determinant is
zero, because the first coordinate of the row is one. This is the
integral obstruction, without division by the determinant, leading
coefficient, or any individual coefficient in the row.

## 3. Diagonal distinctions over arbitrary rings

- In a field a nonzero \(\gamma\) is a unit. In a general ring
  nonzero is not enough for any normalization using \(\gamma^{-1}\);
  even regular but nonunit \(\gamma\) is not invertible.
- If \(\gamma\) is a nonunit, take a maximal ideal containing it.
  The residue tableau is strict ERK at the same physical stage
  count, so already \(p\ge5\) forces \(s\ge p+1\). This includes
  every nilpotent diagonal in a nontrivial ring. A nilpotent
  \(\gamma\) also makes each paid \(\lambda_j\) a unit in the
  original ring: its constant value \(1/(j+1)!\) is a unit and
  the rest is a multiple of a nilpotent. This is not an assertion
  that the original tableau itself is strict explicit.
- For a unit diagonal, \(\gamma\) remains nonzero in each residue
  field. Mere nonzeroness of \(L\), \(\delta\), or a rectangle pivot
  in the original ring does not license cancellation. If \(L\) is
  actually a unit, its factored adjacent terms are units, but this
  does not automatically make other pivots units. Transfer the
  stage-count proof through a field map rather than treating
  ring nonzero elements as field pivots.
- For the original proof alone, a single field image where the
  determinant is nonzero suffices. In particular a nonnilpotent
  image of the integer \(\mathcal R_{p-1}\) in \(R\) is sufficient:
  choose a prime ideal avoiding it and take the fraction field of
  the domain quotient. Requiring it to be a unit is stronger than
  needed. The companion proof removes this determinant premise
  in the published \(p\ge15\) range.

## Lean interface, not a body

Use reviewed HasOrder.map for an actual coefficient map; the already
proved HasOrder.natCast_isUnit supplies the bounded unit facts.
A first independent scalar theorem can expose the cleared tall equality
and integral recurrence before any characteristic case split. For the
conditional route, a measured remainder/determinant family could
later expose the evaluation-row certificate above, using monic
remainders and the adjugate identity, without AdjoinRoot or
irreducibility at runtime. Do not change the existing characteristic-zero
tall theorem's assumptions merely by replacing casts. Finite paid
words, the residue reduction, and any new matrix certificate should
remain separate layers. No Lean body, runner or repository operation.
