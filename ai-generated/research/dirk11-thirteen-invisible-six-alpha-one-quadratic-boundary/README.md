# Quadratic first-gap carriers: the zero-fifth boundary and all beta two

**Result.** Over characteristic-zero fields, no normalized invisible-six
no-late DIRK11/13 chart with \(\alpha=1\) and quadratic carrier has
\((\beta,\gamma)=(2,3)\), or \((\beta,\gamma)=(1,4)\) with zero fifth
regular reverse diagonal. The beta-one nonzero-fifth case is not included
here, nor is an unrestricted stage lower bound. Real DIRK11 remains
**13–14**.

The normalization is the literal one of the [early census](../dirk11-thirteen-invisible-six-early-profile-census/README.md)
and [forward masks](../dirk11-thirteen-invisible-six-prefix/README.md):
actual order eleven, six distinct zero-weight ghost clocks,
the specified signed support and paid ranks, and the regular reverse
chronology
\[
 T,v,u,w,z,V,[\beta\text{ ghosts}],B,[\gamma\text{ ghosts}],O .
\]
The six ghost clocks are pairwise distinct, but no new noncontact
assumption between a ghost and an ordinary clock is added. At the five
nonendpoint ordinary rows the weights are live; the reciprocal
relation below supplies the live reverse heads; at the physical terminal \(G_T=H_{\rm bary,T}=0\).

## 1. Why the reciprocal multiplier and read degrees are valid

The actual relation \(G\phi=\tau H_{\rm bary}\), where
\(\phi=U(c)-g\), cannot have \(\tau=0\): the three distinct old
ordinary clocks where \(G\) is live would all be roots of a nonzero
quadratic. Normalize to \(\tau=1\). Thus the reflected carrier
\(U_r=U(1-Y)\) is live at each of the old ordinary sites, \(V,B\),
the origin, and all six ghosts (the ghost values are the actual
nonzero \(g\)-samples). In the usual old quotient
\(R=(Y-v)(Y-u)(Y-w)\), one has
\(mU_r=J_4\pmod R\). Therefore in the common adjugate gauge the
decomposition \(U=nU_r=\widehat M+tR\) has **\(t=0\)**, by the
cubic coefficient. Here \(\widehat M\) has degree at most two
and the old multiplier \(n\) is live. This is not a limit in a
generic cubic computation.

The actual weighted quintic primitive error and commutator still
land respectively in \(Z_6=G\mathcal P_3+H_{\rm bary}K\) and
\(Z_7=G\mathcal P_4+H_{\rm bary}\mathcal P_1\). Their paid
budgets are the same as before: the primitive of the weighted
degree-five comparator and the commutator pairing
\(5+5+1=11\). The independent rank/dimension arguments for these
spaces do not require a nonzero degree-three coefficient of
\(U_r\). In every cancellation below, degrees require only
\(\deg U_r\le3\).

## 2. The actual beta-two zero fifth diagonal

Use \(P_0=YR,\ P_5=(Y-V)P_0\), zero primitive \(I\),
\(D=(I(YP_0)-VI(P_0))/Y\), \(j=J_4(V),\ h=D(V)\).
The two physical middle ghost clocks are \(x,y\).
Every inclusive weighted input of \(P_5\) through \(y\)
is zero: the old rows, terminal and \(V\) annihilate this
polynomial, and the ghost weights vanish. Thus the paid quintic
error polynomial \(Q_5\) has the three distinct roots \(z,x,y\).
It is nonzero by the old determinant of
\(IP_0/Y,I(YP_0)/Y,J_4\) in the cubic old quotient:
if \(Q_5=0\), the first two old columns would have a vanishing
linear combination modulo the third. Hence \(Q_5\) is cubic.
Importantly this is a statement about **\(Q_5\)**, not about
the degree of the carrier.

Let \(B_5=j(Q_5+\theta U_r)\) using the actual quintic
error's clean coefficient. Its true samples give
\(B_5(V)=hU_r(V)\) and \(mB_5=jD\pmod R\).
For the actual commutator row, write its \(G\)-polynomial as
\(Q_c\) and its affine clean coefficient as \(\Theta\).
Its old zero samples give
\(Q_c+\Theta U_r=(u_0+u_1Y)R\) as a polynomial:
the left side has degree at most four, including when
\(U_r\) is quadratic. At \(V\) the weighted input is zero,
and the reciprocal relation gives \(u_0+u_1 V=0\).
At \(B\) only its own literal diagonal can read a nonzero
weighted input; hence with \(\chi=u_1\),
\[
 \chi J_4(B)=-d_B^2 U_r(B),\qquad
 Q_c=-\Theta U_r+\chi(Y-V)R .
\]
The first equality uses only a live weight and the distinct
nonendpoint ordinary clock factors in \(P_5(B)\).
The commutator also vanishes at \(z,x,y\), so
\(Q_c=\Lambda Q_5\) with affine \(\Lambda\), including zero.
Consequently
\[
 \chi(Y-V)R=(\Theta-\theta\Lambda)U_r+\Lambda B_5/j .
\]
At \(V\), cancel the live \(U_r(V)\) to see that the
affine polynomial
\(\Theta-\theta\Lambda+(h/j)\Lambda\) is
\(\eta(Y-V)\). Cancel the **polynomial** factor \(Y-V\), then
read the old three sites after multiplying by \(m\):
\[
 0=\eta J_4+\Lambda E\pmod R,\qquad
 E=(j D-hJ_4)/(Y-V).
\]
The [exact pure ordinary elimination](../dirk11-thirteen-invisible-six-alpha-one-beta-two-zero-fifth/README.md)
proves independence of \(J_4,E,YE\) in that quotient:
its only projected factors are \(J_4(V)\) and the forbidden
endpoint-pencil factor. It contains no carrier coefficients.
Thus \(\eta=0\) and \(\Lambda=0\).
The cancelled polynomial identity then gives \(\chi=0\);
the literal diagonal gives \(d_B=0\) since \(U_r(B)\) is
live. The affine \(\Theta\) vanishes too, by its three
ghost zeros and the live ghost carrier samples. No division
by a diagonal, old pivot \(A_1\), or ghost–ordinary clock
difference was used.

## 3. What really transfers after the diagonal is zero

Either beta two above or the beta-one assumption now pays the
same two independent literal prefixes as in the
[first-pin transfer](../dirk11-thirteen-invisible-six-alpha-one-zero-fifth-transfer/README.md):

* Forward at \(b=1-B\), \(A(C\phi)\) has only its
  diagonal input \(bU_f(b)\); the origin factor and every
  initial ghost entry are zero. Its true grade-five primitive
  gives \(J_b(U_r)=\int_B^1(1-Y)U_r(Y)\,dY=0\). No
  terminal grade-six coefficient belongs in this read.
* Reverse at \(V\), \(D_{\rm match}=(Y-z)G-W(Q_4)\)
  vanishes through \(V\) by its exact terminal/old samples,
  mark at the first gap, and the chosen fourth-site match.
  Triangularity gives \(ND_{\rm match}=0\) at \(V\).
  The actual cubic/quartic fits yield the same first primitive
  scalar \(H_V=0\). Neither a later ghost nor any tap into
  \(B\) is used.

The old-profile resultant is independent of the forward carrier
degree. Its **whole** ledger therefore applies with these degree
checks:

| Old profile | Checked exclusion and why degree two is included |
|---|---|
| Monomials; mixed contact; lost direct ratio | The first-pin calculation is polynomial in the unrestricted scalar \(t\). It uses the genuine \(H_V\) and \(J_b\), both valid at \(t=0\). The impossible monomial \(m=Y\) is excluded already at the first reverse ghost. |
| \(r=0\) and direct \(F_1\) | The old slope \(-1\) first-ghost bridge uses only true old matching. The subsequent finite degree-60 exclusion uses the matched read at \(V\), the weighted quintic at the first middle, and the commutator there. Its carrier variable is \(E=qK_*\), with no degree-three-carrier or nonzero-\(t\) assumption. No cubic-only forward determinant is used. |
| Direct \(F_2\) | \(m\mid R\) contradicts each live old \(m\) value. |
| Direct regular \(F_n\) | The [zero-fifth proof](../dirk11-thirteen-invisible-six-alpha-one-live-fn-zero-fifth/README.md) projects the common pin of \(J_b\), the literal adjacent marked read \(A\), and the first-middle quintic/commutator gate. The two quadratics at that ghost have their necessary resultant even at degenerate leaders, and all the polynomial dependence in \(t\) is an upper degree bound. It does not use the cubic forward grade-six/seven determinants. Its proof retains \(t=0\). |
| Alternate \(F_1,F_2,F_n\) | The old finite ingress uses only the old polynomial guards, exact affine/resultant and the just-verified slope exclusion. Each of the four finite reductions uses **only** the first pin at \(V\) combined with \(J_b\). Overlaps, repeated \(F_n\) roots, and both complementary ordinary assignments are retained. |

In particular, none of the cubic beta-one *nonzero* fifth-diagonal
carrier-rank arguments is reused. Nor is the distinct late-ghost
beta-zero second reverse pin used. All the old proof eliminations,
including the slope ranks and all direct regular guard caps, are
replayed unchanged in the supplied exact receipt; no unknown
tableau reduction is involved.

Run `bash verify.sh PATH/TO/ai-generated/research` with SymPy
and python-flint 0.9. The local Lean module checks the coefficient
specialization, the old three-sample scalar diagonal inference and
a homogeneous distinct-root divider. The exact rooted ingress and
finite-field lifting are the written/source proof, not a new
end-to-end `HasOrder` theorem.
