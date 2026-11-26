# Balanced two-sided proof of the nonsingular triangular RK floor

**Theorem.** Let a chronological lower triangular Runge–Kutta tableau have \(s\) stages, all actual diagonal entries nonzero, and full rooted order through \(p\ge1\) over a field of characteristic zero or characteristic greater than \(p\). Then
\[
  s\ \ge\ Q(p):=
  \left\lfloor \frac{\lfloor(p+1)^2/4\rfloor+1}{2}\right\rfloor.
\]
Equivalently, \(Q(2m)=m(m+1)/2\) and \(Q(2m-1)=\lceil m^2/2\rceil\). This includes genuine SDIRK at any common nonzero diagonal, and needs no nonzero top moment, common diagonal, clock separation, or hypotheses on the signs or support of the output. It is a short proof of the established quadratic lower bound, not a new numerical stage bound.

## The single commutator in both orientations

Let \(\mathbf c=A\mathbf1\), \(C=\operatorname{diag}(\mathbf c)\), and
\[
                         D=CA-AC-A^2 .
\]
The literal diagonal of \(D\) in the physical stage order is \((-a_{ii}^{\,2})_i\), so \(D\) is invertible. A rooted stage feature of grade \(j=|\tau|-1\) has exact formal polynomial \((|\tau|/\rho(\tau))x^j\), where \(\rho\) is the tree factorial. A left \(A\) applies \(Jf(x)=\int_0^x f(u)\,du\) and a left \(C\) multiplies by \(x\); each costs one grade. The first operation adds one unary root and the second one leaf at the root. Their formal actions follow from the tree factorial, and the paid output takes \(\int_0^1\). In particular all words in \(A,C\) on the column \(\mathbf1\) are literal linear-tree-context expressions and have polynomial witnesses.

Write \(X\) for multiplication by \(x\). Formally \(XJ-JX=J^2\): the difference applied to \(f\) has derivative \(Jf\) and vanishes at zero. Thus a left \(D\) raises grade by at most two and produces the zero formal polynomial. For actual reverse rows started at \(\mathbf b^\top\), right \(A\) applies the formal density operation \(J^*g(x)=\int_x^1 g(u)\,du\), and right \(C\) multiplies by \(x\). The adjoint identity \(\int_0^1 g\,Jf=\int_0^1 (J^*g)f\) follows on integrating the derivative of \((J^*g)(Jf)\), with zero boundary terms. Hence a right \(D\) produces density
\[
                         J^*(Xg)-XJ^*g-(J^*)^2g=0 .
\]
The order of the first two terms is important: \(CA\) on the right means \(C\) first and \(A\) second. The displayed identity also follows by differentiating the difference and evaluating it at \(1\). These are formal polynomial primitives; no analytic positivity is used.

For a row and column whose witness grades sum to at most \(p-1\), their literal pairing equals the formal integral of the product of their respective density and polynomial. Indeed concatenate the actual word to the forward feature, expand before paying the rooted conditions, then move the integrations by the algebraic adjoint identity. The highest size paid is one plus the sum of grades. In particular one formal-zero witness is sufficient for a vanishing literal pairing. No assumption that a vector has a well-defined polynomial independent of its witnesses is needed.

## Balanced low flags suffice

Let \(F_j\) be the actual span of all words of length at most \(j\) in \(A,C\) applied to \(\mathbf1\), and \(R_j\) the actual row span of all such words on the right of \(\mathbf b^\top\). Set both flags to zero for negative indices. Then \(D F_{j-2}\subset F_j\) and \(R_{j-2} D\subset R_j\) have formal-zero witnesses and dimensions \(\dim F_{j-2}\) and \(\dim R_{j-2}\), respectively.

Put \(q=\lfloor(p-1)/2\rfloor\). For each \(0\le j\le q\), the probes \(\mathbf c^{\odot i}\) and rows \(\mathbf b^\top C^i\), \(0\le i\le j\), have the paid Hilbert pairing \(H_{ik}=1/(i+k+1)\). This matrix is nonsingular over the stated fields. In fact a kernel vector \((v_k)\) would make \(\sum_k v_k\prod_{\ell\ne k}(Y+\ell+1)\) a polynomial of degree at most \(j\) vanishing at \(0,\ldots,j\); evaluating the resulting zero polynomial at \(-k-1\) gives \(v_k=0\). The denominators \(1,\ldots,2j+1\) and nonzero node differences of sizes at most \(j\) are invertible. The row probes kill \(D F_{j-2}\), and the column probes kill \(R_{j-2}D\), with total payment at most \(2j+1\le p\). Thus the corresponding power probes are independent modulo each defect space, giving
\[
 \dim F_j\ge j+1+\dim F_{j-2},\qquad
 \dim R_j\ge j+1+\dim R_{j-2}\quad(0\le j\le q).
\]
Both flags therefore have dimension at least \(f(j)=\lfloor(j+2)^2/4\rfloor\) at these indices, by summing \(j+1,j-1,\ldots\). Put \(f(-1)=f(-2)=0\).

Take the final split \(t=q,\ h=p-1-q\); thus \(h+t=p-1\) and \(h\in\{q,q+1\}\). The \(q+1\) forward probes are still independent modulo \(D F_{h-2}\), as the test row grade is at most \(t\). The reverse defect space \(R_{t-2}D\) annihilates all of this forward sum at the same paid total. Consequently
\[
\begin{aligned}
s&\ge q+1+\dim F_{h-2}+\dim R_{t-2} \\
 &\ge q+1+\lfloor h^2/4\rfloor+\lfloor t^2/4\rfloor
   =Q(p).
\end{aligned}
\]
The low-flag induction was never used at \(h=q+1\): even then \(h-2\le q-1\). The closed form follows by setting \(p=2m\), in which case \((h,t)=(m,m-1)\), or \(p=2m-1\), in which case \((h,t)=(m-1,m-1)\).

## Ring form and exact comparison

In a nonzero commutative ring the denominator-cleared paid tall tree of size \(p\) makes \(p!\) a unit. If the product of the diagonal entries is not nilpotent, choose a prime avoiding the product and pass from the quotient domain to its fraction field. The rooted conditions map to this field, each diagonal remains nonzero, and its characteristic is zero or greater than \(p\). Hence the same quadratic bound holds. In particular each diagonal being a unit suffices (for common diagonal, one common unit suffices), and the conclusion about a nonnilpotent product makes no assertion for merely nonzero nilpotent entries.

At the published baseline f0b74ea89e18f2033df7c21fcdbfc72e706f15ad, the strict SDIRK numbers in **ai-generated/lower-bounds/README.md** agree with this formula throughout orders \(1,\ldots,20\) for the ring column, including \(50,55\) at \(19,20\). The sharper characteristic-zero order-six entry \(7\) is not the quadratic bound \(6\).

The literal invertible commutator and one-sided parity recurrence already appear in **SDIRKStageFloor.lean**. The reviewed native **NonsingularDIRKQuadraticFloor.lean**, theorem **nonsingularStageFloor_eq_quadratic**, already proves the exact closed form at all positive orders; its field and unit-diagonal ring endpoints likewise have no order cap. The reverse orientation appears in the published **Exact bidirectional flag duality at nonsingular RK stage saturation**. The native **NonsingularDualCensus.lean** gives an exact iterated finite covector rank as well. The present proof only uses partner flags up through the middle; it is a shorter balanced proof of the same capacity, not a new scope, priority, certificate, or table claim. The nonnilpotent-diagonal-product ring form above is the elementary prime specialization of the field result; the cited native ring statement assumes unit diagonals.

For comparison the earlier parity census evaluates as follows. With \(N=p-1\), write \(a_j=1+\min(j,N-j)\), \(0\le j\le N\). Its two terminal census values are the two parity sums of \(a_j\) (the missing parity at \(p=1\) has sum zero). Their total is \(\lfloor(p+1)^2/4\rfloor\). If \(N\) is odd, reversal exchanges parity and the sums are equal. If \(N=2q\), reversal pairs the two halves with the same parity, and the signed parity difference is \(2\sum_{j=0}^{q-1}(-1)^j(j+1)+(-1)^q(q+1)\), equal to \(1\) for even \(q\) and \(0\) for odd \(q\). The larger parity sum is therefore \(Q(p)\) in all cases.
