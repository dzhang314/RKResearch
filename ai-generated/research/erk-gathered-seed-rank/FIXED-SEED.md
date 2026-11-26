# At most seven independent exact scalar functionals of order nine by stage twenty on the fixed gathered Stepanov seed

The proof uses exact ranks certified for the archived continuation. The two restrictions on appended stages are symbolic and do not assume that the new stages come from that continuation.

**Fixed-seed theorem.** Keep the actual gathered fifteen-stage Stepanov order-ten tableau used in our compact forward constructions, up to a nonzero rescaling of time. Append any five strictly explicit rows, with arbitrary real coefficients and clocks, in any causal order. The largest possible number of independent genuine scalar functionals through ordinary tree order nine is **seven**. In particular, no such twenty-row block supplies eight exact scalar functionals through order nine. This remains true if the first appended row is not the default exact endpoint, if that endpoint is delayed, or if a signed endpoint observation is produced in a new way. This is a fixed-seed obstruction rather than an unrestricted RK stage lower bound or a claim about every Stepanov tableau.

## 1. Literal order moments and the exact old coefficient spaces

Normalize the selected Stepanov method to endpoint 1. For an ordinary rooted tree \(t\), put
\[
 f_t(x)\coloneqq |t|x^{|t|-1}/t!,\qquad
 E_a p\coloneqq p(a),\quad
 \mu_j(p)\coloneqq \int_0^1 x^j p(x)\,dx,\quad
 Jp(x)\coloneqq\int_0^x p(s)\,ds .
\]
A row is genuine through size \(g\) for \(F\) if it returns \(F(f_t)\) on the actual Butcher weight vectors \(\boldsymbol\Phi_t(A)\) for every \(|t|\le g\). The pure bush at each size shows that a genuine row has a unique such scalar functional on the polynomial space: its scalar action is summation with its coefficients at the actual clocks. A zero row at size \(g\) here means a coefficient row whose action on all these numerical tree values is exactly zero, not a row of the stage matrix. Actual zero rows are relevant to cancellation of a literal coordinate.

Let
\[
 \begin{array}{ll}
 W_8^-=\operatorname{span}(E_0,\mu_0,\mu_1,\mu_2),
   &W_9^-=\operatorname{span}(E_0,\mu_0,\mu_1),\\
 W_8=W_8^-+\operatorname{span}(E_1),
   &W_9=W_9^-+\operatorname{span}(E_1).
 \end{array}
\]
On the actual fifteen-stage seed, \(\mu_j\) is represented by the gathered output row multiplied coordinatewise by the \(j\)-th power of the clock, whenever \(g+j\le10\). Attaching \(j\) leaves at the root proves this. On its usual 16-row version, the extra row is the literal gathered output at time 1, so its unit derivative coordinate represents \(E_1\) already through order eleven. These are the original (not fitted) tableau and clocks in
\`archive/stepanov15_exact_marked_fixture.md\`
and
\`archive/erk_stepanov_weighted_five_and_freed_three_anchor_multiplier_20261123.md\`.

The spaces just listed are the **complete** genuine scalar duals at sizes eight and nine, respectively, for these 15- and 16-row banks. The complete order-eight zero-row space in each case is the single transported \(D(2)\) line, supported at four distinct interior-clock pairs with opposite entries at each pair. At order nine there is no nonzero zero row. Here is a way to extract these completeness facts without replaying any tableau.

Use the accepted complete rank proof for the 19-row one-way jet branch in the last section of
\`archive/erk_causal_endpoint_jets_and_sixth_literal_port_20261123.md\`.
It begins with exactly the gathered fifteen and its usual literal endpoint. At order eight its complete scalar dual consists of \(W_8\) and the two first endpoint derivatives, and its zero-row space is spanned by the old \(D(2)\) and one relation whose latest nonzero slot is row 19. The accepted proof bounds the relevant difference rank by a separating modular minor and counts these explicit rows; only those already-certified ranks are used here. The signed actual rows from lifts 17 and 18 have independent first-derivative directions through order eight and have successive nonzero last pivots at 17 and 18. Thus any genuine coefficient row supported only on the first sixteen is a combination of the actual \(W_8\) rows and \(D(2)\): express it on the entire bank, eliminate the zero vector with last slot 19 by inspecting that slot, then the two signed rows by inspecting slots 18 and 17. This also locates the entire zero-row space. At order nine the archived rank and six independent genuine forms give the entire coefficient space with no zero relation, and lifts 18 and 19 are the two independent first-jet directions. Eliminating those same later pivots leaves exactly \(W_9\). Finally in either size the usual literal coefficient for \(E_1\) is the only one in the resulting basis with nonzero slot 16; restricting once more gives the two minus spaces above. The old \(D(2)\) has no endpoint coefficient. The independent fixed-tableau embedding certificate
\`archive/stepanov15_exact_embedding.md\`
also verifies that old zero support and its one-dimensionality.

## 2. Two necessary conditions for any single added row

Let an arbitrary new strict stage have clock \(r\), and let \(\boldsymbol h\) on the extended bank represent \(F\) through size \(g+1\). Two actual rows representing lower functionals have no coefficient at the new slot:
\[
 \begin{array}{c|c}
 \text{actual lower row on the extended bank}&
             \text{true functional through size }g\\ \hline
 \boldsymbol h A & p\mapsto F(Jp)\\
 \boldsymbol h(C-rI) & p\mapsto F((x-r)p).
 \end{array}
\]
The last column of the strict \(A\) is zero. The other new coefficient vanishes because its own clock is \(r\). The true identities follow from unary extension and attaching one leaf to the root, respectively. Consequently both scalar functionals must annihilate the kernel \(Q\) of the complete preceding size-\(g\) dual. This necessity holds for arbitrary added rows; it does not assume that they have been constructed by the Cauchy recipe or restrict their available predecessors to the weighted six sites.

Also, adding one physical stage increases the dimension of a scalar dual at any fixed size by at most one. If some genuine coefficient uses the added slot, subtract its multiple from all other genuine coefficients to set their new slot to zero; all those remaining representations then live on the old closed bank. This is a statement about actual rows, rather than a count of unspecified scalar moments.

## 3. The first two appended rows can provide at most one new order-nine read

Use \(g=8\). For the old fifteen-stage minus space, \(Q\) has dimension four on \(\mathcal P_7\). The primitives \(P=Jq,\ q\in Q\), have a double zero at 0, a simple zero at 1, and satisfy
\[
          \int_0^1 P=0,\qquad \int_0^1 xP=0,\qquad \deg P\le8 .
\]
These conditions are equivalent: the endpoint and moment equations use \(\mu_0(q)=P(1)\), then integration by parts for \(\mu_1,\mu_2\). For \(r\ne0,1\), an intersection element of \(JQ\) and \((x-r)Q\) has the form
\[
                 P_1=(x-r)P_2', \qquad P_i=Jq_i,\ q_i\in Q .
\]
It forces an additional zero multiplicity at both endpoints on \(P_2\): triple at 0 and double at 1. Conversely these multiplicities and the original two moments suffice, by integration by parts on \(P_1\) and \(xP_1\). Thus the intersection dimension is two. Indeed after factoring \(x^3(x-1)^2\), there is a degree-three free factor subject to two independent moments under the constant-sign weight \(x^3(1-x)^2\); independence follows from the positive Gram on \(1,x\). For \(r=0\) or \(1\), there is no additional multiplicity requirement at that coincident endpoint, and the same computation gives intersection dimension three.

The annihilator on \(\mathcal P_8\) of the two lower test spaces therefore has dimension three off the endpoints, and four at either endpoint. Off the endpoints it is exactly \(W_9^-\), whose genuine rows supply all three directions. At 0 the extra direction is precisely \(E'_0\): both lower test polynomials vanish doubly there. At 1 the extra direction is \(E_1\): both lower test polynomials vanish there. These displayed extra directions are independent of \(W_9^-\), either by elementary polynomial rank or by the already known independent augmented endpoint and first-jet rows.

An extra \(E'_0\) is *literally impossible*. Subtract the old \(W_9^-\) components if needed, leaving an actual coefficient row for the unit \(E'_0\). Its clock pullback at \(r=0\) would have to represent \(E_0\) through order eight. Every actual old representation of \(E_0\) differs from the initial unit row by a multiple of the old \(D(2)\); hence its total coefficient at clock 0 is 1. But the literal clock pullback vanishes on every coordinate at 0. This is a contradiction independent of any normalization convention or local support assumption.

Therefore the first new stage either gives no genuine order-nine gain, or is at clock 1 and adds exactly \(E_1\). In the latter case let \(\boldsymbol h_1\) be its actual signed representation, not assumed to be a new unit evaluation. Its new last coefficient is nonzero. The expanded order-eight scalar dual is exactly \(W_8\), by \(E_1\)'s independence and the per-row gain limit. Its entire zero-row space is still just the old \(D(2)\) line: if a new zero row had nonzero last coefficient, subtract a multiple of \(\boldsymbol h_1\) so that its last coefficient is zero. The old fifteen would then already represent a nonzero multiple of \(E_1\) through eight, a contradiction.

Moreover the total coefficient of \(\boldsymbol h_1\) at normalized clock 1 is exactly one. Its clock pullback \(\boldsymbol h_1(C-I)\) is an old zero row through eight and so is a multiple of \(D(2)\). At every clock \(\xi\ne1\), this zero row has sum zero by its opposite-pair shape. Dividing the summed relation by \(\xi-1\) shows that \(\boldsymbol h_1\) has zero total at every other clock. Its total is one by the constant tree.

Now apply the same two lower pullbacks to the second new stage, when one order-nine read was gained at the first. On the expanded genuine lower space \(W_8\), \(Q\) has dimension three; its primitives have double zeros at *both* endpoints, the two old moments, and degree at most eight. The intersection dimension is one off the endpoints and two at the endpoints by the same multiplicity argument, now with both baseline endpoint exponents two. Thus the allowable upper space is exactly \(W_9\) off the endpoints, and \(W_9\) plus the single matching endpoint derivative at 0 or 1. The literal obstruction rule now kills both endpoint derivatives: at 0 the actual \(E_0\) representative has total one there; at 1 the actual \(\boldsymbol h_1\) just proved has total one there. Adding the sole old zero row cannot change either total. The clock pullback is zero on all these coincident coordinates, a contradiction. Hence the second new stage brings no new order-nine read.

The two cases prove the bound. The seed has three order-nine directions. Among the first two added stages at most one direction is gained, and among the remaining three at most three. The maximum by row 20 is \(3+1+3=7\). The old symmetric twenty-row construction already exhibits seven, so the cap is attained on this fixed seed. There is no implication that a subsequent different 25-row route is excluded.

## 4. Transferable replacement test

The endpoint obstruction above has a positive counterpart. Let the earlier precise size-\(g\) scalar library be a polynomial moment chart with endpoint observations. Suppose a proposed next true scalar \(F\) passes both source-space tests \(FJ|_Q=F((x-r)\cdot)|_Q=0\). Let \(w\) be any actual earlier representative of the second functional, and \(Z_g\) the actual zero-row space on the same lower budget. Let \(U_r\) be the set of all old slots at the proposed clock \(r\). A necessary exact whole-slot payment is
\[
             w|_{U_r}\ \in\ (Z_g)|_{U_r}.
\]
Indeed every true representation of that commutator differs from \(w\) by a member of \(Z_g\), while any actual clock pullback is zero at all slots in \(U_r\). The test is on literal coordinates, not just their sum. If the test passes with an admissible local-support representative, then the standard repeated-column Cauchy lift supplies a genuine improvement: subtract the zero row to make all these coordinates zero, divide by \(r-c_i\) only on the other slots, and use one free coincident coefficient to make the normalizer nonzero. The primitive row and the normalized divided row must lie on sufficiently accurate earlier states for the single-inaccurate-child induction; in the present lower order-eight use, individual local four already suffices, since two inaccurate children would cost at least ten vertices. No unsupported actual rank identity is inferred from the scalar gates.

This distinguishes two genuinely new ways to seek the eighth read: a different seed with an extra true lower read beyond the moment family, or a different true lower zero row whose whole restriction can pay for an inner endpoint jet. A same-clock constant-preserving change of basis that carries all numerical tree vectors through order nine to their transformed vectors cannot help: it preserves the genuine scalar dual, and transforms old zero rows inside their same-clock fibres without modifying their summed coefficients there. Merely swapping or gathering those same interior pairs again does not change the obstruction. The repeated-jet mechanism does not exclude a changed nonlinear seed, a preparation inserted within its first fifteen rows, or a separate suffix-node reduction.

The conditional one-loss forward and physical refund remain in
The cap applies to this fixed block, independently of any later reverse coupling.
The present result decisively rules out their missing eighth read on *any* five-row continuation of the previously fixed 15-stage seed. It does not claim a new tableau or alter the real order-20 upper bound 51.
