# Distinct doubled endpoints cannot mutually reuse each other's labels in the opening triples

Assume strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field, with all quadratic residuals nonzero, exactly seven clocks, and a genuinely quadratic singleton graph. The two actual endpoints have distinct D (doubled) clock labels. Each actual opening triple in its own orientation has one extra D and one S (singleton). This packet excludes the case in which each extra D uses the other physical endpoint's label. Neither a sign restriction nor a full seven-clock or stage nonexistence claim is made.

## Two true overlap products

Normalize the diagonal to one and write \(\ell=1/\gamma=2m\), \(h=m-1\ne0\), \(t=x-m\). The D labels are \(-h,h,d\); the first is at \(-h\), the terminal at \(h\). The graph \(R=rW\) has one of two exact shapes by [odd projection](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md):
- even: \(d=0,\ W=t^2-S\), where \(S=(21m^2h^2-15m^4)/(35h^2-21m^2)\), allowing \(S=0\) and common D/graph roots;
- split: \(d\ne0\), \(W=t(t+d)\), and \(35h^2d^2-21m^2(h^2+d^2)+15m^4=0\), with \(d\ne\pm h\).

In the mutual reuse envelope the forward extra D is at \(h\) and reverse extra D at original \(-h\). Each has its own normalized clock \(1+2h\). Its literal phases A2 (arithmetic D second), A3 (arithmetic D third), and S (either genuine star order) are the [first-three formulas](../sdirk-eight-all-dirty-seven-quadratic-shared-one-extra-d/README.md) with the appropriate \(2h\) clock input. We do not use the shared-clock prohibition of arithmetic gap \(u=2\) in this distinct-endpoint chart.

Let \(\lambda\ne0\) scale reverse to original normalized residuals. Both true residual products, at \(-h,h\), require the same \(\beta_0=B\lambda\), and \(L_4(-h)=L_4(h)\ne0\). Since the first forward and reverse normalized values are both \(1/2\), the two extra normalized D residuals must be equal:
- A2 and S both have extra normalized residual \(\kappa(2h)/2\), with \(\kappa(u)=1+2u-u^2\).
- A3 has \(q(h)/2\); its difference from \(\kappa(2h)/2\) is \(2h^2(3h-2)/D(h)\), nonzero by literal arithmetic guards. Thus A3 paired with A2 or S is impossible.
- A3/A3 would make their supposed singleton labels both \(t=0\), so is impossible.

Thus only A2/A2, A2/S (up to genuine reverse), and S/S remain. Write \(g_D=\kappa(2h)/2\) for the common extra D residue and \(\beta_0=-2L_4(h)/g_D\). The actual forward singleton coordinate is \(\sigma=3h\) with residue \(q(2h)/2\) for A2, or \(\sigma=2-3h\) with residue \(g_D\) for S. The reverse singleton is the negative of its own such centered coordinate in original coordinates. Call these original labels \(\sigma,\tau\) and their respective normalized residues \(g_f,g_r\).

## Exact interpolation and normalized trace

The known singleton labels give \(r=g_f/W(\sigma)\), \(\lambda=rW(\tau)/g_r\); all denominators are nonzero by the actual singleton residuals. Therefore \(B=\beta_0/\lambda\). Put \(C=A_2+B R\), and use \(\lambda C\) to retain all scales without new rank factors. At the two doubled labels the actual quartic residual sums give:
\[
 \begin{split}
 \lambda C(-h)&=-\beta_0(1/2+\lambda g_D)+\beta_0rW(-h),\\
 \lambda C(h)&=-\beta_0(g_D+\lambda/2)+\beta_0rW(h),\\
 \lambda C(\sigma)&=\lambda L_4(\sigma)/g_f,\qquad
 \lambda C(\tau)=L_4(\tau)/g_r.
 \end{split}
\]
The interpolation at \(-h,h,\sigma\) fixes the entire quadratic. Check its fourth value at \(\tau\). All three interpolation denominators are actual distinct physical clock labels. In the even same-phase cases \(W\) is even, \(\lambda=1\), and the fourth fit is a genuine identity. In the even mixed and split cases the exact polynomial mismatches, after clearing only guard denominators, give:
- even A2/S: one irreducible degree-five projection;
- split A2/A2: a degree-ten factor and both \(d\) labels from its quadratic;
- split A2/S: degree eighteen (one \(d\) label);
- split S/S: degree four (both \(d\) labels).

The replay reconstructs every exact \(d\) fibre using the squared-root condition and the fourth-value equation and checks the actual guard list. None of the finite even-mixed or split fits satisfy the [normalized quadratic trace](../sdirk-eight-all-dirty-seven-quadratic-five-d-prefix/README.md), \(2\sum_i1/g_i=\ell\sum_i b_i/g_i\). This uses \(A_2=C-BrW\), the quotient traces at the \(W\) roots, and the coefficient of \(t^7\) modulo \(L_4^2\) for the weighted inverse sum. The weighted contribution is unchanged if a graph root repeats, and the even unweighted constant \(-2(2S-6m^2/7)/(rL_4(\sqrt S))\) is valid even at \(S=0\) by differentiating \(H'/H\). Thus no division by \(S\) or by \(W\) at D labels was made.

For the even same-phase identities, impose trace symbolically in \(\mathbb Q(h)\) with those same exact even formulas. Every nonconstant denominator factor is checked against the actual \(h\)-guards. The guarded trace numerator is one irreducible degree-thirteen factor for A2/A2, or one degree-seven factor for S/S. These are still only necessary scalar data, not actual methods.

## Actual fourth reads on the remaining two fields

Both endpoint D labels and the two known singleton labels have already been consumed by the two disjoint boundary triples. The actual fourth row must therefore be a D copy at the third label \(d=0\), or one of the two remaining singleton labels from \(H/[(t-\sigma)(t-\tau)]\), where \(H=L_4-RC\). The replay checks that \(H\) has degree four in both fields before this division.

Let \(T_f(x)\) be the quadratic interpolating the first three forward residues \(1/2,g_D,g_f\) at their actual normalized clocks. A star permutes the two later clock orders but both have normalized residue \(g_D\); the fourth gate depends on the same \(\kappa\) and the same interpolant. Write \(T_f=a_0+b_0x+c_0 x^2\) and \(J\) for the zero-based primitive. The [literal fourth identity](../sdirk-eight-all-dirty-clock-census/README.md#3-exact-two-ended-fourth-read-exclusion-on-every-mesh) is
\[
 g_4[1-\Lambda(x_4)+b_0+c_0\Delta(x_4)]
           =T_f(x_4)-JT_f(x_4),\qquad
 \Lambda=1+(x-1)/\kappa,\quad \Delta=\tfrac43+\tfrac{2(\kappa+1)}{3\kappa}(x-1),
\]
where \(\kappa=\kappa(2h)\). At \(d=0\) take the gcd in the unknown residual with its true quadratic \(U=0\). At a remaining singleton substitute \(g_4=rW(t_4)\) and take the gcd in \(t_4\) with \(H/[(t-\sigma)(t-\tau)]\). Both exact gcds are units in each field. The calculation never divides by the affine fourth coefficient, so singular fourth fits are retained if consistent. Hence even the last trace-compatible cases are impossible.

Run `python check_distinct_mutual_reuse.py` with SymPy 1.14 and python-flint 0.8. It imports `distinct_mutual_reuse.py`, which can also be run to check the preliminary projections. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticDistinctMutualReuse.lean) stages the exact mixed product numerator only. No end-to-end native build or finite-characteristic claim is made.
