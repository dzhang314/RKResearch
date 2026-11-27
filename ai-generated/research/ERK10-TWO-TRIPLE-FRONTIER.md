# Chronological endpoints in the surviving \((2,3,3)\) ERK10 chart

Continue the all-live two-carrier, zero-pooled, three-active-label
case from the [carrier atlas](ERK10-THREE-CARRIER-EXCLUSION.md).
The active pair has common clock \(a\), common nonzero \(r\)-value,
and opposite weights. Two separate active triples have clocks \(p,q\),
distinct nonzero \(r\)-values within each, and nonzero pooled ordinary
mass. The carriers have clock \(\theta\), and are rows 2 and 13.
The four true clean rows, together with \(p,q\), form the six
fixed Lobatto clocks (ordinary scalar quadrature).

The invisible pair's earlier row is physically **3, 4 or 5**,
and its later row **10, 11 or 12**. This is a necessary condition,
not a closure of this branch.

Put \(G(X)=(X-p)(X-q)\), \(T=G(c)-G(\theta)s\).
Then \(T\) has grade two and support only on the four true
clean and two paired rows. The preceding carrier atlas proves
the pair straddles the two interior true clean rows: if no
paired row precedes the first nonzero true clean \(u\), the
exact unary of \(CT\) there would give the forbidden fixed-four
Jacobi contact. The reflected statement is the same.

Until the earlier pair member there are no previously supported
values of \(CT\), because its value at the origin is zero.
Suppose two rows of the same active triple preceded the earlier
pair member. Their distinct \(r\)-values and the grade-four pure
shape \(F_4=\langle s,r,Cr\rangle\) would force
\(J[XG](p)=p^3(2q-p)/12=0\), or its copy with \(p,q\)
exchanged: the actual \(A(CT)\) is zero there and its pure
remainder is affine in the clock times \(r\).
The two inner Lobatto roots cannot differ by a factor 2:
the exact Bézout constant of \(L(X),L(2X)\) is 59, with
multipliers in [ERK10TwoTripleFrontierGate.lean](../lean/RKCert/Research/ERK10TwoTripleFrontierGate.lean).
Thus at most one active row of each triple, plus origin
and the first carrier, precedes the earlier pair member.
The pair member is neither origin nor carrier, so its
physical index is 3, 4 or 5. Reflection of the entire
argument proves the late assertion (the reflected
Lobatto labels are also roots of \(L\)).

An exact independent amplitude identity is available.
If \(\omega_p,\omega_q\) are the nonzero ordinary Lobatto
masses at the triple labels and \(r_{p,i},r_{q,i}\) their
three nonzero \(r\)-values each, their cubic charges satisfy
\[
       \omega_p\prod_{i=1}^3 r_{p,i}
             +\omega_q\prod_{i=1}^3 r_{q,i} = 0 .
\]
Indeed each group's first two positive-degree amplitude
moments vanish. Reducing \(r^3\) modulo the monic product
of its three amplitudes gives its pooled cubic charge
equal to its mass times their product. The overall \(br^3=0\)
test costs nine, and the uniform pair and carriers contribute
zero. The two products are nonzero and have opposite signs
in an ordered field (the Lobatto masses are positive).
The identity itself is characteristic-zero algebraic.

The Lean companion checks the doubling and amplitude identities.
The literal stage bridge is mathematical, and the unrestricted
ERK10 14–15 interval is unchanged.
