# DIRK12/15: the third and fourth live debuts of the one-active-label reverse head

Work in the ordinary real order-twelve \(C(2),f_5=3\), fifteen-stage equality frame with exactly **one weighted active cubic-dirty numerical label**. This note strengthens the [first reverse head calculation](../dirk12-fifteen-rank3-one-active-cubic-head/README.md). It does not exclude the whole one-active-label case or change the real stage interval **15–16**.

Use true physical reverse chronology, \(N=A^{\mathsf T}\) in that ordering, \(Y=\operatorname{diag}(\mathbf y)\) with \(\mathbf y=\mathbf 1-\mathbf c\), and \(\mathbf W(P)=\mathbf b\odot P(\mathbf y)\). The scalar primitive \(J\) is based at \(0\) in the reflected clock. The actual reverse initial defects at scalar input degrees zero and one vanish. The true cubic defect \(\mathbf G=N\mathbf W(X^2)-\mathbf W(X^3)/3\) is proportional to the weighted forward cubic, so it is supported on a single reflected clock \(d\) and vanishes at every zero-weight row. As in the previous packet, \(d\ne0\) is the first live nonzero clock, and \(v\ne0,d\) is the next distinct live clock. Put
\[
   \sigma_0=d^3/6,\qquad
   \mathbf H=N\mathbf G-\frac d2\mathbf G,\qquad
   \lambda=\frac{3(v-d)(v-2d)}{d^2}.
\]
The actual grade-four \(\mathbf H\) is zero before the live debut of \(v\), and nonzero there. The true global quartic primitive error is \((3d/2)\mathbf G+\lambda\mathbf H\). The true \(\mathcal B_4\) cannot be clock-invariant, since its next gain is one and the true outgoing weighted two-detector bound would be two. Thus
\[
  \mathcal B_4=\langle\mathbf G,\mathbf H\rangle,\qquad
  \mathcal B_5=\langle\mathbf G,\mathbf H,Y\mathbf H\rangle .
\]
This only uses the actual scalar weighted adjoint and its genuine grade rules, not a normalized reverse rooted-order assertion.

## Exact characterization of a missing third-live head

Let \(u\ne0,d,v\) be the third distinct **live nonzero** clock in reversed physical order, and \(i_u\) its actual first live row. If \(H_{i_u}=0\), the whole actual \(\mathcal B_5\) vanishes there. On \(P=X(X-d)(X-v)\), the genuine weighted degree-three input \(\mathbf W(P)\) is zero before \(i_u\): every earlier live row is at \(0,d,v\), and zero-weight rows automatically give zero. Its value at \(i_u\) is nonzero. The actual commutator \(YN-NY-N^2\) on the input is a pure weighted grade-five vector by the scalar identity \(XJ-JX=J^2\) and the two genuine primitive rules, hence vanishes there. The literal diagonal of the commutator is \(-N_{i_ui_u}^2\), so \(N_{i_ui_u}=0\).

Thus both \(N\mathbf W(P)\) and \(N\mathbf W(XP)\) are numerically zero at \(i_u\), even though the input may be nonzero on that row: earlier entries are zero and its diagonal is zero. Their true discrepancies have grades four and five, so the two scalar primitive values must be zero. After cancelling nonzero powers of \(u\), the exact equations are
\[
   15u^2-20(d+v)u+30dv=0,\qquad
   12u^2-15(d+v)u+20dv=0.
\]
They give \(5(d+v)=6u\) and \(10dv=3u^2\); the unordered pair \(\{d/u,v/u\}\) is exactly
\[
                        \left\{\frac35-\frac{\sqrt6}{10},\frac35+\frac{\sqrt6}{10}\right\}.
\]
In particular \(10v^2-12uv+3u^2=0\) and \(5v^2-14dv+5d^2=0\). This implication addresses all signs of the unknown clocks; its nonzero guards are only the distinct live debuts and nonzero live weight.

A missing head also requires **a live return to \(d\) with altered cubic amplitude before \(u\)**. If all earlier live rows at \(d\) still had \(G_i/b_i=\sigma_0\), then \(H_{i_u}=0\) implies \(N\mathbf G=0\) there, so the actual aggregate weighted tap to \(d\) is zero. Its diagonal is already zero. The remaining actual nonzero-source clocks are \(0,v\), inconsistent with exact degree-three scalar read, by the nonzero integral \(\int_0^u X(X-v)^2\,dX\). This premise tests every earlier live row at \(d\), including a possible live cubic-clean row at that same clock. No quotient by an unweighted row occurs.

The possible departure itself has an exact prior-row relation. For any live \(d\)-row \(i\) before \(u\), write \(\sigma_i=G_i/b_i\), and \(T_d,T_v\) for its actual aggregate weighted taps, already divided by \(b_i\). The true first two nonconstant scalar moments give
\[
       dT_d+vT_v=d^2/2,\qquad d^2T_d+v^2T_v=d^3/3+\sigma_i .
\]
On its source set \(0,d,v\) one has \(X^3=(d+v)X^2-dvX\). The exact quartic error relation therefore gives
\[
                   \lambda H_i/b_i=(v-d/2)(\sigma_i-\sigma_0).
\]
At the **first** such departure, writing \(a_i=N_{ii}\), local amplitudes on earlier live \(d\)-rows are still \(\sigma_0\). The identity \(H_i/b_i=(\sigma_i-\sigma_0)(a_i-d/2-d^2/[6(v-d)])\) follows by using \(T_d=d/2-(\sigma_i-\sigma_0)/[d(v-d)]\). Hence a departure must satisfy
\[
           \lambda\bigl(a_i-d/2-d^2/[6(v-d)]\bigr)=v-d/2 .
\]
For instance \(v=2d\) makes a departure before \(u\) impossible, even though the scalar quartic error itself then loses the \(H\) coefficient. No explicitness of this return is assumed.

## Consequences on the fixed scalar grid

In the all-cancelling one-label case, if the candidate active clean scalar union with its endpoints has exactly seven labels, this is the fixed Lobatto grid by the paid node-hull orthogonality. Reflection preserves it. Every live clock outside the sole dirty label \(d\) is clean, so \(v\) and \(u\) are distinct nonzero fixed-grid nodes. The exact coefficient check below excludes \(10v^2-12uv+3u^2=0\) on every ordered pair of such fixed nodes. Thus \(H_{i_u}\ne0\) in this fixed-grid chart **regardless** of an early altered amplitude at \(d\).

For a further restriction assume all live rows at the sole dirty clock have the same nonzero cubic amplitude \(G_i/b_i=\sigma_0\). This holds, for example, if all active dirty amplitudes are uniform and \(d\) is not a candidate clean clock. Let \(w\) be the next live nonzero distinct clock after \(u\), different from \(d,v,u\); it exists by the scalar count. If \(H_{i_w}=0\), then \(G_{i_w}=0\) and the true scalar primitive is exact at this row through degree four. The \(NG\) row there is zero, so uniformity of actual \(d\)-amplitudes kills the aggregate weighted tap to \(d\) on that row. Its only remaining possible source clocks are \(0,v,u,w\), with no diagonal assumption. Testing their degree-four nodal hull gives
\[
       \int_0^w X(X-v)(X-u)(X-w)\,dX
            =-\frac{w^3}{60}\bigl(3w^2-5(v+u)w+10vu\bigr)=0 .
\]
This too is excluded by the exact arithmetic on distinct nonzero fixed-grid nodes. Therefore in this uniform non-overlapping fixed-grid chart, \(H\) is nonzero at **three** live numerical labels outside \(d\), in addition to the local \(G\) support. In particular **the actual \(\mathcal B_5\) cannot be clock-invariant**: localization on those four distinct clock blocks would give four independent directions in its rank-three space.

## Arithmetic and receipts

The polynomial \(L_6'\) splits into five distinct interior residues \(347,468,507,546,667\) at \(1013\). The two coefficient gates are nonzero for all 30 ordered pairs and 120 ordered triples of distinct nonzero fixed-grid nodes (including \(1\)). These are tests of fixed rational expressions in the algebraic grid, not reductions of unknown dirty clocks or tableau entries. Choose a prime above \(1013\) in the fixed Lobatto splitting field; its five interior root reductions are the checked labels, and no leading divisor is zero. Nonzero residues certify nonzero real coefficients.

    python3 -B check.py

The portable Lean core checks the trial division, split and all pair/triple arithmetic. The separate Mathlib module proves the denominator-cleared third-debut, nodal-integral and same-clock scalar identities. The analytic deduction from the true table flags is mathematical rather than a native end-to-end lower-bound theorem. The remaining extra grade-six direction and the general one-active-label and invisible faces are not excluded here.

The arithmetic kernel replay passed Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 with no axioms. The field-algebra file passed Lean/Mathlib 4.36.0 with the usual propext, Classical.choice and Quot.sound only. No other Mathlib version is claimed for that file.
