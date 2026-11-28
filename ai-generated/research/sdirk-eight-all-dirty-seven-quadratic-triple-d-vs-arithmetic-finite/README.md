# Seven finite D,D,D prefixes cannot oppose an arithmetic D,S,S

Keep an all-dirty strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field with exactly seven different clock labels and a genuinely quadratic singleton residual graph. Both physical endpoints are D (doubled labels). Orient its D,D,D prefix forward and an arithmetic D,S,S (two singleton labels) prefix backward, using the genuine weighted mirror. This packet excludes all such cases **except** distinct endpoint labels and a forward midpoint arithmetic prefix. The variable forward-midpoint gap is not specialized or excluded here. Signed weights are permitted, and no stage interval change is asserted.

## Visible finite forward meshes

Normalize the common diagonal to one, let \(\ell=1/\gamma=2m\), put \(h=m-1\), and use centered \(t=x-m\). The endpoint labels are \(-h,h\), with \(h=0\) exactly when the two physical endpoints share a label. The [D,D,D mesh and squared-root census](../sdirk-eight-all-dirty-seven-quadratic-five-d-prefix/README.md) applies without change. The only forward mesh not covered here is \((-h,0,h)\) with distinct endpoints and forward nonzero arithmetic gap \(h\). Retaining all other forward phase / endpoint combinations gives:

| Actual forward shape | Guarded finite fields, in each actual order |
|---|---|
| Distinct, arithmetic nonmidpoint \((-h,h,3h)\) | one irreducible quartic |
| Distinct, star with \(h,2-3h\) in either order | one rational central-D case and one irreducible quartic per order |
| Shared endpoint, arithmetic \((0,u,2u)\) | one irreducible quartic |
| Shared endpoint, star \((0,u,2-u)\) | one irreducible quartic |

The replay regenerates these seven cases using the exact paired squared-root condition \(35a^2 b^2-21m^2(a^2+b^2)+15m^4=0\) whenever the two known nonzero squared labels differ. If the third forward-D star label is zero, that rational shape is retained without that condition. Actual arithmetic denominators, distinctness of the first three labels, and nonzero Legendre values and residues are checked. No artificial ordering of roots is used.

At the exact D labels \(d_i\), the known forward normalized values \(g_i\) are fixed by the literal first-three formula. Let \(P(t)\) now be the monic cubic with these D roots. By [parity](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md), \(Q/B=L_3-\mu t L_4\), \(\mu\ne0\), and \(Q/B=-\mu P W\) for a monic quadratic \(W\) with \(R=rW\). The check verifies this exact factorization. It allows roots of \(P,W\) to coincide; neither root is divided by \(W\) at a D label. Let \(T,A_0\) interpolate \(g_i,L_4(d_i)/g_i\) on the three labels. If \(\lambda\ne0\) converts normalized reverse to original residual, Vieta at the terminal D clock gives \(\beta_0=B\lambda=-L_4(h)/(g_{\rm f}(h)/2)\). Therefore \(A_2=A_0-\beta_0T/\lambda\).

## Genuine reverse ratio and three affine rows

For the actual reverse gap \(v\), its original singleton coordinates are \(s_2=h-v,s_3=h-2v\). The actual reversed normalized residues are \(k(v)/2\) and \(q_{\rm num}(v)/(2D(v))\), where
\[
 k(v)=1+2v-v^2,\quad D(v)=-2+v+4v^2-v^3,\quad
 q_{\rm num}(v)=(1+4v-4v^2)D(v)+4v^2(3v-2).
\]
The true ratio \(R(s_3)/R(s_2)\) yields the polynomial equation
\[
 \mathcal R(v)=q_{\rm num}(v)W(s_2)-k(v)D(v)W(s_3)=0.
\]
The graph scale in the mirror is \(\nu=r/\lambda=k(v)/(2W(s_2))\), whose denominators are nonzero at the actual singleton. Thus \(H=L_4+\beta_0\nu W T-\lambda\nu W(A_0+\beta_0\nu W)\). At each singleton \(s_i\), \(\nu W(s_i)=n_i/d_i\) with its known numerator/denominator \((n_2,d_2)=(k,2)\), \((n_3,d_3)=(q_{\rm num},2D)\). The actual equation \(H(s_i)=0\), multiplied by \(d_i^2\), is the affine row
\[
 -n_i[d_i A_0(s_i)+\beta_0 n_i]\lambda
       +d_i^2L_4(s_i)+\beta_0 n_i d_i T(s_i)=0 .
\]
Use the [normalized quadratic trace including repeated \(W\) roots](../sdirk-eight-all-dirty-seven-quadratic-five-d-prefix/README.md): \(c/r+\mathcal T(A_2)=0\), with the required interval factor \(\ell\) on the weighted sum. Multiplying by \(\lambda k(v)\) yields the independent row
\[
 k(v)\mathcal T(A_0)\lambda+2c W(s_2)-\beta_0 k(v)\mathcal T(T)=0 .
\]
The unweighted contributions use exact sums in the two- and three-dimensional polynomial quotients, and the weighted contribution uses the usual remainder coefficient \(t^7\) modulo \(L_4^2\). The logarithmic-derivative formula explicitly branches before inverting \(W'\), retaining a repeated graph root.

All \(2\times2\) minors of this augmented two-column array must vanish. This condition holds even when every coefficient of \(\lambda\) vanishes, so the test makes no hidden nonzero rank assumption. In **every** finite field above the exact monic gcd of all these minors with \(\mathcal R\) is \(v\,k(v)\) up to normalization. Both factors contradict the actual nonzero gap and second residual. The two singleton clocks and trace are actual conditions; no next-order assumption, sign, solver approximation, or finite-characteristic transfer is used.

Run `python check_finite_arithmetic.py` with SymPy 1.14 and python-flint 0.8. The sibling `forward_mesh_spec.py` regenerates the exact phase descriptions. This packet uses the earlier staged scalar Lean companions; it adds no stock build or end-to-end Lean claim.
