# A quadratic stage floor from a single clock-zero left-kernel direction

Mathematical proof on literal rooted order. The condition concerns
the **actual** lower triangular tableau. This is not an unrestricted
DIRK lower bound, an attainability claim, or a checked Lean result.

Let $e$ be the vector all of whose entries are one. Write
\[
 \mathcal Q(u)=\left\lfloor
           \frac{\lfloor(u+1)^2/4\rfloor+1}{2}\right\rfloor,
 \qquad D=[C,A]-A^2,\qquad C=\operatorname{diag}(Ae).
\]
Over any field, assume a lower triangular \(s\)-stage tableau \((A,b)\)
has rooted order through \(p\ge1\), its first physical diagonal is zero,
and \(\operatorname{rank}D=s-1\). Then
\[
                         \boxed{s\ge 1+\mathcal Q(p-1).}          \tag{1}
\]
In particular, if the first diagonal is the only zero, the rank
hypothesis is automatic. The remaining diagonal entries need not
coincide. No hypothesis on the signs or nonvanishing of the weights,
or on distinctness of the clocks, is used.

## 1. Paid tree and clock pairings

Let \(E_a\) be the span of actual stage-tree columns \(\Phi(t)\) with
grade \(|t|-1\le a\). Let \(Z_a\) be the image of formal combinations
of these trees with zero exact stage polynomial. This uses the
usual exact model \((|t|/\rho(t))X^{|t|-1}\), with tree factorial
\(\rho(t)\); it does not suppose that the model descends to every
linear relation between actual stage columns. The constant is \(e\),
root merging multiplies stage polynomials, attaching a leaf \(C\)
applies \(X\), and a unary lift \(A\) applies formal integration \(J\)
from 0 to \(X\). Hence
\[
                  [X,J]-J^2=0,\qquad D E_a\subset Z_{a+2}
                       \quad(a+2\le p-1).                       \tag{2}
\]
The polynomial identity follows by integrating a monomial, or by
subtracting the two formal one-fold integrals to get the two-fold
integral. Every term used in (2) has actual rooted size at most
\(a+3\). All denominators used through the paid order are units:
the bush conditions give \(k(b^T c^{k-1})=1\) for \(1\le k\le p\).
Thus the coefficient field has characteristic zero or characteristic
greater than \(p\). No characteristic-zero assumption is needed.

For \(q,\ell\ge0\) write \(\mathcal P_q=\operatorname{span}
(e,c,\ldots,c^q)\) and \(\mathcal B_q=\operatorname{span}
(b^T,b^TC,\ldots,b^TC^q)\). A clock probe of degree \(\ell\)
annihilates \(Z_a\) if \(a+\ell+1\le p\), by root merging and payment.
For \(u+v+1\le p\) the pairing of clock powers \(c^u,c^v\) is
\(b^Tc^{u+v}=1/(u+v+1)\). All square Hilbert blocks used below
are nonsingular over the achieved field: the Cauchy determinant
has numerator products of differences of distinct integers
of magnitude at most \(p\) and denominator products of the
specified paid positive integers. The same holds for the shifted
block \(1/(h+k+2)\) whenever its maximum denominator is paid.

## 2. Actual forward/reverse losses and the paid cut

Put \(n=p-1\), \(q_j=\min(j,n-j)\), \(w_j=q_j+1\) for
\(0\le j\le n\). The forward and reverse canonical flags on either
parity are
\[
 F_j=\mathcal P_{q_j}\oplus D F_{j-2},\qquad
 R_j=\mathcal B_{q_j}\oplus R_{j-2}D,
\]
with no transported summand at grades zero and one. These are
direct sums, even for singular \(D\). For the forward sum, \(DF_{j-2}\)
is in \(Z_j\) and is annihilated by the clock probe block
\(\mathcal B_{q_j}\). For the reverse sum, inductively \(R_a\) kills
\(Z_b\) when \(a+b+1\le p\): the clock part has this property, and
the transported part uses (2) and pays two more grades. Therefore
\(R_{j-2}D\) kills \(\mathcal P_{q_j}\), so the reverse sum is
separated by the same nonsingular Hilbert block. One can also
replace \(F_{j-2}\) by the whole measured \(E_{j-2}\) for a forward
lower bound on \(\dim E_j\).

The exact losses on each advance are
\[
 \lambda_j^F=\dim(F_j\cap\ker D),\qquad
 \lambda_j^R=\dim(R_j\cap\ker D^*),
\]
where \(D^* f=f\circ D\). Thus, for example,
\(\dim R_{j+2}=w_{j+2}+\dim R_j-\lambda_j^R\).
There is also an exact two-sided interpretation. If \(a+b\le n\),
every transported term in the \(F_a,R_b\) pairing is paid-zero.
The remaining rectangular clock pairing has rank
\(\min(w_a,w_b)\) by its initial square block. Hence
\[
              s\ge\dim F_a+\dim R_b-\min(w_a,w_b).
\]
When \(a+b=n\), the clocks have equal widths and reflection of
the reverse grades covers the far side of the same parity tent.
This yields its full parity census minus its actual forward
losses on one side and actual reverse losses on the other.
It spends each boundary packet only once.

The same reverse construction can use any increasing two-separated
list \(J=(j_1,\ldots,j_r)\): start with \(\mathcal B_{q_{j_1}}\)
and at \(j_{\nu+1}\) adjoin \(\mathcal B_{q_{j_{\nu+1}}}\) to the
previous space composed with \(D\). All the separation and silence
arguments still apply, because \(j_\nu+2\le j_{\nu+1}\).
The exact lower estimate is the sum of its widths minus the
kernel losses at its selected predecessor grades.

## 3. Why the left kernel pays no first-half loss

With a zero first diagonal, the first row of \(A\) is zero, so the
first clock \(c_1\) is zero and the first row of \(D\) is zero.
Corank one identifies the entire left kernel with the first
coordinate covector line \(K\epsilon_1\).

Consider any reverse flag at grade \(j\) as above, including
a flag built from a two-separated list, and let \(2j+2\le p\).
It cannot contain a nonzero \(\lambda\epsilon_1\).
Indeed its clock part is \(b^T g(C)\), where \(\deg g\le j\)
because \(q_j=j\); its transported part kills all \(c^h\) with
\(h\le p-1-j\), by (2) and the previous grade's silence.
Thus for \(1\le h\le j+1\) we get
\[
                  0=\lambda c_1^h
                    =\int_0^1 X^h g(X)\,dX .
\]
The shifted Hilbert block (largest denominator \(2j+2\))
forces \(g=0\). The paid test at \(h=0\) now says
\(\lambda=\lambda\epsilon_1(e)=0\), a contradiction.
Therefore an advance from \(j\le\lfloor p/2\rfloor-1\) has
**zero reverse loss**. Every later advance costs at most one
because the full kernel is one-dimensional.

## 4. Evaluating the resulting integer floor

For \(p\ge3\) write \(m=\lfloor p/2\rfloor\). Subtract one
from \(w_j\) at each \(j\ge m\), retaining \(w_j\) at \(j<m\).
The resulting sequence \(v_j\), for \(0\le j\le p-1\),
is precisely the usual parity tent for order \(p-1\) followed
by one zero. Choose grades of the parity of \(p-2\) up to
and including \(p-2\). Their \(v_j\)-sum is \(\mathcal Q(p-1)\):
for any positive order \(u\) the larger parity sum of its tent
is that of its last grade, and equals \(\mathcal Q(u)\).
For clarity, the total tent sum is
\(\lfloor(u+1)^2/4\rfloor\); for even \(u\) reflection swaps the
parities and their sums agree. For odd \(u=2k+1\) the last
parity is even; the unit interval layers \([i,2k-i]\) have
alternating imbalance \((-1)^i\), summing to zero or one.
This proves the claimed tent evaluation.

The final grade \(p-2\) is at least \(m\) for \(p\ge3\).
Its one-unit deduction in the adjusted sum is put back: the
final packet is not followed by another advance. This gives
(1). There is no polynomial extrapolation or finite-order
search in this argument. At \(p=1\), \(b^T e=1\) gives \(s\ge1\)
and \(\mathcal Q(0)=0\). At \(p=2\), \(s=1\) would make
\(A=0\) and contradict the two-vertex rooted order condition
\(2b^Tc=1\); so \(s\ge2=1+\mathcal Q(1)\).

For comparison the general nullity-only packet loss replaces
every predecessor loss by \(\kappa=\dim\ker D\). For
\(p>2\kappa\) the optimized bound is \(\kappa+\mathcal Q(p-2\kappa)\):
subtracting \(\kappa\) trims the two ends and yields the
shorter tent of order \(p-2\kappa\). Its optimal nonadjacent
sum is its larger parity sum. One way to see the latter fact
is to split at the unique middle vertex or the adjacent
middle pair: on each increasing or decreasing ramp an
optimal independent set alternates from the nearest available
peak; with a unique middle vertex compare keeping it or
omitting it. If \(p\le2\kappa\), every adjusted width is
nonpositive and the packet optimum is just \(\lceil p/2\rceil\).
The independent scalar stability bound is \(p\le2s-z\) for
\(z\) actual zero diagonals: numerator degree is at most \(s\),
denominator degree is at most \(s-z\), and exponential contact
through \(p\) costs at least \(p\) in the sum of those degrees.
For the last fact, for numerator \(P\), denominator \(Q\) with
constant term 1, the polynomial \(QP'-(Q'+Q)P\) vanishes
through degree \(p-1\) and has degree \(\deg P+\deg Q\),
because its leading term is that of \(-QP\).
This comparison does not assume equality in any stage bound.

| Order | Nullity-one generic packet bound | First zero, corank one | Nonsingular |
|---:|---:|---:|---:|
| 6 | 4 | 6 | 6 |
| 10 | 11 | 14 | 15 |
| 14 | 22 | 26 | 28 |
| 18 | 37 | 42 | 45 |
| 20 | 46 | 51 | 55 |

## 5. Physical mask and exact residue transfer

For the diagonal zero set \(Z\) and complementary set \(N\),
\(D_{NN}\) is invertible triangular from diagonal \(-A_{ii}^2\).
Its elimination gives the strictly lower triangular zero-mask
Schur complement \(S=D_{ZZ}-D_{ZN}D_{NN}^{-1}D_{NZ}\) and
\(\operatorname{rank}D=|N|+\operatorname{rank}S\).
These identities do not assume a nonzero shortest path sum.
If consecutive zero sites in their induced order all have a
nonzero \(S\)-subdiagonal entry, then \(\operatorname{rank}S=|Z|-1\)
and hence \(D\) has corank one. At two physically adjacent zero
sites the Schur correction is zero and the entry is
\((c_{i+1}-c_i)A_{i+1,i}\). This proves the criterion for an
initial zero block with nonzero actual adjacent edges and
unequal adjacent clocks within it, followed by nonzero
diagonals. When all diagonals are zero it likewise applies to
that particular explicit adjacent class, not to ERK in general.

More generally let \(R\) be a nonzero commutative ring with the
same literal rooted order and lower triangularity, and put
\(\bar R=R/(A_{11})\). Form \(D\) in \(\bar R\), or map down the
original one. It suffices that **one \((s-1)\)-minor of \(D\)**
be nonnilpotent in \(\bar R\). Indeed localize at powers of
that minor, obtaining a nonzero ring, and pass to a maximal
residue field. The first diagonal is then zero, the minor
survives, and the field rank is exactly \(s-1\) (the first
row is zero). Rooted order, clock sums, lower triangularity,
and \(D\) all map coefficientwise, so the same unchanged
stage count obeys (1). No regularity of that minor and no
injectivity or characteristic control of the map is needed.
Conversely a field image with first diagonal zero and rank
\(s-1\) must preserve some such minor, so this is exactly
the hypothesis for this residue route. The size-zero minor
for \(s=1\) is \(1\).

In particular if \(A_{11}=0\) in \(R\), and the product of the
remaining diagonals is nonnilpotent, the triangular tail minor
of \(D\), which is its signed square, suffices. This is true
when they are all units. Separate nonnilpotence of different
diagonals need not suffice to exhibit a common residue field.
The result is conditional on the actual mask/rank or residue
marker and gives no new unrestricted DIRK stage floor.
