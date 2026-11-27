# Seven DIRK prefix rows are necessary and sufficient for a full size-five decoder

Let \(K\) be a characteristic-zero field. Let \(A\) be a lower triangular \(s\)-stage matrix, let \(\mathbf c=A\mathbf1\), and write \(\boldsymbol\Phi_t(A)\) for the genuine rooted stage vectors. Suppose there is a linear decoder
\[
       \Pi:K^s\longrightarrow P_4(K),\qquad
       \Pi\boldsymbol\Phi_t(A)=\frac{|t|X^{|t|-1}}{t!}
       \quad (|t|\le5).
\]
Then **\(s\ge7\)**. Seven is attained by the explicit opening below. This is a **dense-prefix floor**, not an unrestricted order-ten DIRK lower bound or a claim about weaker decoders.

## Rank five, then a same-amplitude contradiction

The five bush vectors are \(\mathbf1,\mathbf c,\mathbf c^2,\mathbf c^3,\mathbf c^4\). The decoder sends them to \(1,X,X^2,X^3,X^4\), so its rank is five. If \(s\le6\), its kernel has dimension at most one. Put \(C=\operatorname{diag}(\mathbf c)\) and
\[
     \mathbf d=A\mathbf c-\mathbf c^2/2,\qquad
     \mathbf g=A\mathbf c^2-\mathbf c^3/3 .
\]
The vectors \(\mathbf d,\mathbf g,C\mathbf d,A\mathbf d,C\mathbf g,A\mathbf g\) all lie in the kernel. Indeed the first two are differences of genuine trees with equal scalar profiles, and attaching a leaf or adding one unary root preserves the zero scalar profile while still using tree size at most five.

Consider the first nonzero clock \(\delta\). At this row \(A\mathbf c\) and \(A\mathbf c^2\) receive their nonzero contributions only from the diagonal. They cannot both give \(\delta^2/2,\delta^3/3\) when \(\delta\ne0\). Thus at least one of \(\mathbf d,\mathbf g\) is nonzero there and the kernel is one-dimensional. Take its carrier \(\mathbf z=\mathbf d\) if \(\mathbf d\ne0\), and \(\mathbf z=\mathbf g\) if \(\mathbf d=0\). The vector \(C\mathbf z\) is proportional to \(\mathbf z\), so \(\mathbf z\) is supported at one clock; because it is nonzero at the first nonzero row, that clock is \(\delta\). Also \(A\mathbf z\) is proportional to \(\mathbf z\).

A second distinct nonzero clock must occur: otherwise \(\mathbf c^2=\delta\mathbf c\) would contradict the decoder's two distinct monomial images. Before its first occurrence, every row at \(\delta\) reads only 0 or \(\delta\), diagonals included. At such a row write \(t_i\) for the total taps with clock \(\delta\). Then
\[
 d_i=\delta t_i-\delta^2/2,\qquad
 g_i=\delta^2t_i-\delta^3/3=\delta d_i+\delta^3/6.
\]
If \(\mathbf d\ne0\), write \(\mathbf g=\mu\mathbf d\); then \((\mu-\delta)d_i=\delta^3/6\), so all these carrier values are the **same nonzero** number. If \(\mathbf d=0\), they are instead \(g_i=\delta^3/6\), again the same nonzero number. This treats the C(2) case separately; no nonzero quadratic defect is assumed there.

Now let \(v\ne0,\delta\) be the first new nonzero clock. At its row, \(\mathbf z\) and \(A\mathbf z\) vanish. The old amplitude is nonzero and constant on the \(\delta\)-rows, so the total historical taps into \(\delta\) are zero. At \(v\) both \(\mathbf d,\mathbf g\) vanish as well. Thus the two scalar action conditions rely only on the self tap and would give \(a_{ii}v=v^2/2\) and \(a_{ii}v^2=v^3/3\), the same contradiction as at the first clock. This proves the floor without choosing any special ordering beyond actual triangular chronology.

## Exact seven-row control

Take clocks \(0,1/4,1/2,1,3/2,2,5/2\). At rows 2, 3, 4 use the trapezoid and two Simpson rows, the second Simpson row skipping row 2. At each of rows 5–7 use cubic interpolatory integration on the literal nodes \(0,1/2,1,c_i\), including its own diagonal. Rows 1, 4, 5, 6, 7 then supply five actual local size-five sample values. Cubic primitive integration against size-four inputs is exact there; the only early quadratic primitive discrepancy is avoided by these rows. Interpolation on those five samples gives the desired decoder, and no prescribed final output is needed.

    python3 -B check_example.py

The independent exact replay tests all 17 rooted shapes through size five. The scalar gates **no_clean_self**, **defect_relation**, **same_amplitude**, and **amplitude_C2** check in Lean/Mathlib 4.36.0. The rank and physical chronology bridge above is a mathematical proof, not an imported universal tableau theorem.

## Coefficient-ring scope

The argument in the field uses only the units 2 and 3 after the decoder identities are supplied. Those identities are defined over any ring inverting 5!, so the lower bound applies directly to every field in that scope. For a nonzero commutative ring inverting 5!, reduce the entries of the lower triangular matrix and the linear decoder at a maximal ideal. The decoder identities survive, giving the same contradiction in the resulting field if there are at most six stages. Conversely, the seven-row control and its literal decoder have only factorial-paid denominators, as checked by the exact replay; the identities hold after specialization. Thus seven is also sharp over every nonzero commutative ring with 5! invertible. This ring transfer is mathematical and is separate from the Lean scalar gates.
