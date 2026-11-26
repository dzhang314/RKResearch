# Why contributing support alone does not pay local stage accuracy

The grouped stage rule through \(p-K+1\) is best possible even for strictly common-diagonal real-algebraic SDIRK methods. A zero-mass clock can carry a nonzero weighted tree defect. Here is a family making that phenomenon explicit, with no conjectured tableau or computation.

Fix \(p\ge4\). Take an algebraic scalar quadrature of precision exactly \(p-1\) on some labels, and add more distinct algebraic labels if desired. Let \(K\le p-1\) be the total count and set
\[
                  d\coloneqq p-K+2,\qquad
                  F(X)\coloneqq\prod_{\eta}(X-\eta).
\]
Assign the original scalar weight \(\beta_\eta\) at each original label, and zero aggregate weight at each added label. Assume at least the usual quadrature-minimum number of original sites. Use a prescribed real-algebraic common diagonal \(\gamma\ne0\); the same argument allows \(\gamma=0\).

A chronological preparation with this common diagonal supplies a full actual decoder \(\mathcal D\) through tree size \(p-1\). One explicit way to obtain such a decoder starts with the single row \((\gamma)\) (which is pure through size one). From an available decoder through \(j\), append \(j+1\) independent rows at distinct rational clocks \(x\) with their own diagonal \(\gamma\) and strict feed \(E_x(J-\gamma\,\mathrm{Id})\mathcal D_j\). Those rows are pure through size \(j+1\), and interpolation gives the next decoder. This uses only finitely many old rows, all with zero output in the final method. No efficient stage count is asserted for this preparation.

Write \(\Lambda\) for the coefficient of \(X^{d-2}\) in the old decoder. At label \(\eta\) make as many independently fed rows as needed, with common diagonal \(\gamma\) and strict feed
\[
                  E_\eta(J-\gamma\,\mathrm{Id})\mathcal D
                                     +\tau\Lambda.
\]
Such rows have no strict taps into one another. Their clock is \(\eta\), independently of \(\tau\), since \(d\ge3\) makes \(\Lambda(\mathbf1)=0\). At parameter \(\tau=0\) each row is pure through size \(p\).

For a child \(u\) the actual primitive discrepancy at this row is
\[
  \tau\,{\bf1}_{|u|=d-1}
              +\gamma\bigl(N_u(\eta,\tau)-\eta^{|u|-1}\bigr).
\]
This follows from the exact old decoder and the literal diagonal. Here \(N_u(\eta,\tau)\) is the actual normalized stage coordinate of the new row. By rooted induction it is a polynomial in \(\tau\), of degree at most \(|u|-1\) for the grades used below. Its linear response \([\tau]N_t(\eta,\tau)\) is zero for \(|t|<d\), and for \(|t|\ge d\) is a polynomial in \(\eta\) of degree at most \(|t|-d\). To verify the last statement, differentiate the normalized product over the children at \(\tau=0\). The other branches are exact powers of \(\eta\). A direct marked branch with child size \(d-1\) has no further degree cost; any inherited derivative from the literal diagonal has degree at most one less than the target bound. This proves the bound inductively on tree size, also when multiple high branches could be affected at higher powers of \(\tau\).

At every clock take a signed weighted combination of the physical rows that acts on polynomials of \(\tau\) through degree \(p-1\) by
\[
        G(\tau)\longmapsto
              \beta_\eta G(0)+\frac{G'(0)}{F'(\eta)} .
\]
Exact Vandermonde interpolation at any \(p\) distinct rational parameters produces such weights. Their sum is \(\beta_\eta\); at least one is nonzero because this functional is nonzero. In particular added clock labels still have zero scalar weight, while their first-variation output need not be zero.

For any tree of size at most \(p\), the ordinary output is the scalar quadrature of its nominal monomial plus
\[
             \sum_{\eta}\frac{[\tau]N_t(\eta,\tau)}{F'(\eta)}.
\]
The second term is zero, since its polynomial numerator has degree at most \(p-d=K-2\); this is the barycentric identity in the companion note. Thus all rooted conditions through \(p\) hold. The next bushy condition fails by the original scalar quadrature, so the method has exact order \(p\). For a unary tree of size \(d\) whose child has size \(d-1\), the first-variation coordinate is exactly \(d-1\). Therefore at **every** active clock the weighted degree-\(d\) defect is nonzero. The actual aggregate grade cannot be improved from \(p-K+1\) on the basis of the scalar contributing count.

## One silent clock suffices at every even order

For the cleanest instance take \(p=2m\ge4\), the \(m\)-site Gaussian scalar quadrature, and one distinct additional label. Then \(K=m+1\) and \(d=m+1\). In this case the specified perturbations are already linear in \(\tau\) through order \(p\): two affected child branches would have total rooted size at least \(2(d-1)+1=2m+1\). Thus no co-site parameter interpolation is needed at the Gaussian clocks. Each of them is represented by only **one physical output row** with positive Gaussian weight and an appropriate perturbation parameter, chosen so its weight times that parameter is \(1/F'(\eta)\). At the added label use a perturbed row and a pure copy with weights \(1,-1\). Choose the parameter on the perturbed row to have the same barycentric amplitude. This realizes exact order \(2m\) with only \(m\) contributing labels and just one silent clock, while every contributing Gaussian group fails through local size \(m+1\).

This counterexample does not alter or compare absolute upper endpoints. It proves that the missing degree information at a zero aggregate is genuine, even when all physically contributing groups are singletons of positive weights and the actual diagonal is strictly common and nonzero.
