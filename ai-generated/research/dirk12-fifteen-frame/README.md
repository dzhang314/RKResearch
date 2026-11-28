# The actual fifteen-stage order-twelve DIRK equality frame

Let \(A\) be an ordinary lower triangular tableau of real rooted order twelve in fifteen physical stages. Write \(\mathbf c=A\mathbf1\), \(C=\operatorname{diag}(\mathbf c)\), \(T_j\) for its actual numerical rooted stage span, and \(F_j\) for the genuine zero-profile span, with grade equal to tree order minus one. Write \(f_j=\dim F_j\). Use the established grade-six surplus \(f_6\ge f_3+4\) and fifteen-stage lower bound. The latter lets us trim a trailing zero output weight: an inactive last row could be deleted, contradicting that known floor. The following equality ledger is not a claim of a sixteen-stage lower bound.

## Rank and physical boundary

At grade six either \(C(2)\) supplies the true zero origin and seven separated scalar columns, and \(f_6\ge5\), or the nonzero quadratic seed supplies \(f_6\ge6\) and the six scalar columns through degree five separate. In both cases \(\dim T_6\ge12\). The paid reverse rank through level four contributes at least \(3+\operatorname{rank} B_1\) in its annihilator, where \(B_1\) contains both actual initial reflected defects. Thus \(\dim T_6=12\) and \(B_1=0\); both leading adjoints \(D(1),D(2)\) vanish. The strict reverse gains and the physical dimension cap give
\[
       (\dim T_6,\dim T_7,\dim T_8,\dim T_9)=(12,13,14,15).
\]
Neither term in this count silently replaces \(T_j\) with \(F_j\).

The last physical weight \(b_t\) is nonzero, and only the actual diagonal contributes at the adjoint pivot. Its two vanished seeds force \(c_t=1\) and \(A_{tt}=0\); chronologically the whole terminal column is zero. The three genuine level-four reverse dimensions annihilating \(T_6\) are terminal-zero and fill its annihilator, so \(\mathbf e_t\in T_6\). The paid unanchored endpoint-column exclusion at \(q=5\), costing \(2q+2=12\), gives \(\mathbf e_t\notin T_5\). There is no analogous paid unanchored \(q=6\) premise here. The actual paired product with \(\mathbf e_t\) now shows every \(F_5\) vanishes at terminal (total grade \(5+6=11\)). Since \(T_9\) is full, the quadratic defect
\[
                 \mathbf g=A\mathbf c-\mathbf c^{\,2}/2
\]
has \(b_i g_i=0\) everywhere, by the actual \(2+9=11\) product. This is stronger than merely summing to zero: every quadratic-dirty stage is unweighted.

Using the same paid unanchored reverse debit with \(T_5=P_5(\mathbf c)\oplus F_5\) gives \(f_5\le4\). With \(\mathbf g=0\) one has \(f_3=1,f_6=5\). With \(\mathbf g\ne0\) the exact ranks are \((f_3,f_4,f_5,f_6)=(2,3,4,6)\). This latter equality cannot have any literal zero row: such a row would also separate the seventh scalar column at grade six, leading to at least 16 stages.

The native **equality_frame** lemma takes the actual HasOrder 12 predicate, lower triangularity, the surplus, and the live **physical final** weight as explicit inputs; it gives all the ledger and the coordinate conclusions above without an ordered-field hypothesis. It does not silently import the mathematical earlier stage floor to discharge the trimming argument.

## Non-C(2): the scalar overlap and three-or-more dirty clocks are incompatible

Work in the non-C(2) branch. Exactly six degree-five scalar directions are separated from \(F_6\), so \(T_6=P_5(\mathbf c)\oplus F_6\). Let \(L_6=1-42x+420x^2-1680x^3+3150x^4-2772x^5+924x^6\) be shifted Legendre. The degree-six numerical column \(L_6(\mathbf c)\) lies in \(T_6\). Its lower scalar component is zero, since the six degree-five probes are paid on \(F_6\), vanish on \(L_6\), and the ordinary size-six Hilbert matrix is nonsingular. Hence \(L_6(\mathbf c)\in F_6\), with \(L_6(0)=L_6(1)=1\).

Suppose the quadratic defect \(\mathbf g\) has at least three distinct physical dirty clock labels. The unit gain \(F_4\to F_5\) forbids invariance of \(F_4\) (outgoing Hermite) and of \(F_5\) (incoming Hermite). If there were exactly three labels, \(F_4=\mathbf g P_2(\mathbf c)\) would be invariant; if exactly four, \(F_5=\mathbf g P_3(\mathbf c)\) would be invariant. Thus there are at least five. The actual ranks now show
\[
  F_3=\mathbf g P_1(\mathbf c),\quad
  F_4=\mathbf g P_2(\mathbf c),\quad
  F_5=\mathbf g P_3(\mathbf c),\quad
  F_6=\mathbf g P_4(\mathbf c)\oplus\langle L_6(\mathbf c)\rangle.
\]
The last additional scalar column is independent because it is nonzero at the clean terminal. In particular all of \(F_5\) vanish off the dirty rows. Since \(\mathbf g^{\,2}\in F_4\), one nonzero quadratic polynomial \(\gamma\) (degree at most two) gives \(g_i=\gamma(c_i)\) on every dirty row.

Let \(\mathbf v=\gamma(\mathbf c)-\mathbf g\). It is nonzero by separation of degree-two scalars from \(F_2\), and is supported on the clean rows. At its first nonzero coordinate \(i\), the genuine commutator \(R=CA-AC-A^2\) has \(R\mathbf v\in F_4\) and is lower triangular with diagonal \(-A_{ii}^2\). Since the clean row reads zero \(F_4\), this forces \(A_{ii}=0\). If \(u=c_i\ne0\), the three primitive columns \(A(C^j\mathbf v)\), \(j=0,1,2\), have grades at most five, and there is neither a prior numerical contribution nor a diagonal contribution at the pivot. Thus \(\int_0^u x^j\gamma(x)\,dx=0\) for \(j=0,1,2\). Scaling the fixed nonsingular size-three Hilbert matrix at nonzero \(u\) forces \(\gamma=0\). If \(\gamma\) is constant, applying the same pivot refund to \(C\mathbf v\) gives a nonzero pivot clock and the impossible first moment \(\int_0^u x\gamma(x)\,dx=0\). This latter masked contrast is nonzero at the literal terminal.

It remains only a nonconstant \(\gamma\) with a first nonzero contrast at a clean clock zero. Then \(\gamma(0)\ne0\). At every earlier row \(g_i=\gamma(c_i)\); also \(A\mathbf v=0\) through that earlier prefix. Its actual primitive differs from \(J\gamma\) by \(\mathbf g\) times a linear polynomial, by \(F_3=\mathbf gP_1\). Hence all earlier numerical clocks satisfy \(J\gamma=\gamma B\) for one affine \(B\). The difference polynomial, of degree at most three, is nonzero: if the equality held identically, its constant term would force \(B(0)=0\), its linear term would force the slope of \(B\) to equal 1, and the quadratic/cubic coefficients would force both positive-degree coefficients of \(\gamma\) to vanish. There are therefore at most three distinct earlier clocks.

At this clean zero pivot the diagonal is already zero. The actual primitive on \(1,c,c^2\) is zero there, by the genuine clean defects through grade three. Thus Vandermonde kills the aggregate tap to each of those at most three earlier clock fibers. Every genuine \(T_5=P_5(\mathbf c)+\mathbf gP_3(\mathbf c)\) vector is constant on each earlier fiber, because \(g_i=\gamma(c_i)\) there. So this actual row reads zero on all \(T_5\). Then all non-leaf stage elementary weights through grade six vanish there: each has at least one root branch whose child state is in \(T_5\) and is killed by that row. Consequently all \(F_6\) vanish at the pivot. This contradicts the genuine \(L_6(\mathbf c)\in F_6\), which has value 1 at clock zero.

Thus the non-C(2) face has **at most two distinct physical quadratic-dirty clock labels**, all unweighted. This conclusion is about actual physical support, not just the support of an aggregate weighted measure. The clock and scalar linear algebra above works over characteristic-zero fields; the referenced count and inclusive Hermite gain have the same field scope. The \(C(2)\), \(f_5=4\) cubic census is separate.

## Native replay

The native files use the human HasOrder and FiniteRootedTree definitions through the reviewed graded modules. **DIRKOrderTwelveFifteenFrame** proves the equality ledger with explicit premises. **DIRKOrderTwelveFifteenLegendre** proves genuine Legendre membership and the actual readless-row contradiction directly. The support/interpolation/first-pivot reduction above is mathematical, not yet a native theorem about the final number of dirty labels.

Both native modules and the typed audit check on Lean/Mathlib 4.36.0 with standard axioms only. No other Mathlib pairing is claimed. From the pinned ai-generated/lean environment:

    lake build RKCert.ReviewedNative.DIRKOrderTwelveFifteenFrame RKCert.ReviewedNative.DIRKOrderTwelveFifteenLegendre
    lake env lean AuditDIRKOrderTwelveFifteenFrame.lean
