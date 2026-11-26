# A measured reverse width bound, and the exact owner-reuse guard

The lower bounds here apply to particular separated reverse pairings, not to unrestricted strict SDIRK. The exact summed-spine test in the simultaneous tail can be weaker. The constant diagonal is nonzero precisely where the invertible commutator is used; the causal recurrence and its adjoint budget also apply to ERK.

## 1. Lower bound with actual paid source grades

Use the actual paired seed source \(\boldsymbol\Delta_0(t)\), with first possible size \(m\), and put \(p=m+r\). Write \(U_n\) for its actual vector span through size \(n\); no independence is inferred merely from the number of trees. Let \(C_+\) be the physical plus clock diagonal, and let \(T\) be the strict lower feedback matrix on these plus-minus differences. There are \(a\) physical plus positions. A separately paid reverse word takes the starting column \(\mathbf w\) (the plus weights) and uses \(C_+\) for a clock mark and \(T^{\mathsf T}\) for a reverse strict transition. The formal actions are multiplication by \(X\) and \(J_\gamma^*\), respectively.

For each \(1\le k\le r\), define the genuinely needed target map on its full word-paid rectangle by
\[
 \Lambda_k:\mathcal P_{<k}\longrightarrow U_{p-k}^*,\qquad
 \bigl(\Lambda_k(P)\bigr)(v)
       \coloneqq\widehat{\mathbf b}\cdot\bigl((J_\gamma^*P)(\mathbf x)\odot v\bigr).
\]
The degree sum is paid. A separate reverse word decoder need only give \(\Lambda_k(P)\) on \(U_{p-k}\) for a word of length at most \(k-1\); the fixed source taps give that read by restriction. Full polynomial recovery is strictly stronger than this requirement. Conversely these paid rectangles describe the separated word assumption, not the complete-tree summed requirement.

When \(\gamma\ne0\), every solution of these separated constraints satisfies
\[
                    a\ \ge\ \sum_{j\ge0:\,k_j>0}\operatorname{rank}\Lambda_{k_j},
                           \qquad k_j\coloneqq r-2j .                    \tag{1}
\]
For the proof define
\[
         \Pi\coloneqq C_+T^{\mathsf T}-T^{\mathsf T}C_+
                                      +(T^{\mathsf T}+\gamma I)^2.
\]
It is triangular with diagonal \(\gamma^2\) and is invertible. Its formal action is zero: if \(U P=\int_X^1P\), then \([X,U]=-U^2\). Each \(\Pi\) costs at most two letters. At each \(j\), choose \(P_{j,1},\ldots,P_{j,h_j}\) of degree less than \(k_j\) with independent images under \(\Lambda_{k_j}\). The numerical vectors \(\Pi^jP_{j,i}(C_+)\mathbf w\) are independent. In a relation divide by the least power of \(\Pi\) still present, and apply the exact read on \(U_{p-k_j}\) for that least \(j\). Every remaining word is within length \(k_j-1\). Terms with positive powers give zero formal action; the least-power terms have independent targets. This contradiction proves (1). The argument only needs the actual triangular feedback and the measured word identities. It is not a count of virtual copies. At \(\gamma=0\) the commutator need not be invertible, so this width lower bound does not transfer to ERK merely from its analogous pairing equation.

In particular full ranks in all rectangles force \(L(r)\) plus rows. Any gain over that number in the separated architecture must come from actual rank losses, not a free diagonal or endpoint without a lost pairing. If the last rectangle alone drops from rank \(r\) to \(h\), the remaining budget is at least \(h+L(r-2)\).

## 2. Generic ranks for a fixed minimum cached forward donor

Now fix a normalized minimal cached Laguerre donor through grade \(m-1\) and scale it by any nonzero \(\gamma\). Use the standard virtual base pure rows; the theorem of §3 about replacing scalar owners is not assumed here. For each \(n\), let \(D_n\) be the span of the **polynomials** whose evaluation gives \(\boldsymbol\Delta_0(t)\) through size \(n\). On the pure base, each such polynomial is a product of shifted primitives of the older decoded children, minus the old decoded polynomial. Its degree is at most \(|t|-1\) even when its evaluation is taken on fewer than \(|t|\) sites. For this particular source there is no extra high cardinal term. Re-scaling substitutes \(X/\gamma\) into the normalized span, up to nonzero row factors for the different tree sizes, because the literal prefix weights and the exact profiles are homogeneous in stage scale.

The exact first-excess dimension of the minimum cached donor, as in `EXACT-DENSE-EXTENSION-WITH-DEEP-FEEDBACK.md`, is \(d=\lceil m/2\rceil\). On size \(m\) the base already gives the exact shifted profile, so \(\dim D_m=d\). For every additional size \(j>m\), the bush source has nonzero leading term of degree \(j-1\), whereas every older source has smaller degree: the base bush is \((X-\gamma)^{j-1}\) and the decoder has degree at most \(m-2\). It follows that
\[
                             \dim D_n\ge d+n-m\qquad(n\ge m).
\]
For any scalar grid of the paid precision, the matrices of \(\Lambda_k\) on these sources are the integrals \(\ell((J_\gamma^*P)Q)\), with \(P\in\mathcal P_{<k}\) and \(Q\in D_{p-k}\), by degree. Thus the actual evaluation may be used without committing to one particular scalar grid.

For a fixed normalized source span of dimension \(d'\), take a polynomial basis with distinct lowest degrees \(e_1<\cdots<e_{d'}\). After scaling and normalizing each basis element by its lowest power of \(1/\gamma\), its limit as \(\gamma\) tends to positive infinity is a nonzero multiple of \(X^{e_i}\). At the same time \(J_\gamma^*/(-\gamma)\) tends to the identity on the fixed test polynomials. Testing by the successive monomials of degrees 0 through \(\min(k,d')-1\) gives in the limit a nonsingular Cauchy submatrix with entries \(1/(1+i+e_j)\). The original determinant, after an overall scale, is a nonzero polynomial in \(1/\gamma\); only finitely many nonzero \(\gamma\) can fail it. Over the real algebraic numbers this proves the generic exact rank \(\min(k,d')\), also on the actual evaluations. Indeed any numerical relation among the evaluated source polynomials already annihilates all these integral pairings by the paid quadrature. No limiting tableau or numerical approximation is being declared to have order.

Apply this to (1) for all the finitely many grades. Away from finitely many diagonal exceptions the number of plus rows is at least
\[
              L(r)-\sum_{j\ge0}(r-d-4j)_+,
                      \qquad t_+\coloneqq\max(t,0).
\]
For a distinct-owner construction retaining the full forward donor and no owner mergers, add \(\lfloor m^2/4\rfloor\) and at least \(\lceil p/2\rceil\) scalar rows. The latter follows by testing the square of the contributing-site polynomial if too few distinct sites occur; weights need not be positive. The expression is minimized at \(m=\lceil p/2\rceil\): as \(m\) increases and \(r\) decreases the sum of the two full donor counts cannot decrease, and the rank-loss subtraction cannot increase. At orders 11–20 the resulting generic stage floors are respectively
\[
                         22,24,29,32,37,40,46,50,56,59.
\]
These meet or exceed the corresponding unrestricted real-algebraic bounds before any extra reflected reference rows are charged. Thus a generic separated paired receiver, even allowing a thinner reverse word chart, cannot get a new absolute entry there with this full-forward architecture. At order 19 it would require at least three more actual rank losses to go below 54, or savings from a changed forward or owner architecture; at order 20 at least one more actual loss is needed to go below 59. An exceptional algebraic \(\gamma\), an altered donor, or the genuinely summed criterion remains open. This does not say that any rank loss automatically yields a strict causal solve. The exact tensor and row/column chronology conditions must still be met on the actual stages.

## 3. Adopting a genuinely local old scalar owner is different from rebasing a minus

Consider any old prefix plus any new pure owners, with genuine order-\(m\) local derivatives at the chosen owner rows. This last condition is stronger than being a usable short minus reference unless \(r=m\). It is cellwise order on actual stage coordinates, not the formal clock alone. Let \(P\) extract the owner coordinates from this actual early block, write \(B_E\) for its shifted strict matrix, and keep the collocation reference \(M=EJ_\gamma R\). The literal source needed to recouple any owner replacements is
\[
              \chi(t)\coloneqq(MP-PB_E)\boldsymbol\Phi_t(B_E).
\]
It vanishes through size \(m-1\), because the owner derivative and its unary extension give the two exact polynomials on that grade. There is no inverse of \(M\). If \(\mathbf Z(t)\) is the dense owner deviation from these actual rows, at the unique active child \(u\) it now satisfies
\[
                 \mathbf Z(t)=F(C)\bigl(\chi(u)+M\mathbf Z(u)\bigr),
\]
where \(F\) is the product of the other short primitive children. The same correspondence on the physical paired tail uses \(S'\chi\) rather than \(S\Delta_0\). In the reflected decoder formula the outer extra \(J_\gamma^*\) disappears from the source tap: it is already accounted for by \(\chi\). This permits genuine earlier-owner reuse without equality of their full arbitrary-data incoming rows, **if** the needed paired word adjoints remain valid.

Here the degree guard is substantive. An arbitrary \(\chi(u)\) after adopting an old owner may interpolate to degree \(q-1\), even at size \(m\). For a word of depth \(d\), there are at most \(d-1\) adjoints before the last source \(\chi\); the polynomial testing each moved primitive has degree at most \(r-2\). Consequently precision \(q+r-2\) is a uniform sufficient gate for this mixed adjoint (no gate is needed if \(r=1\)). Under original precision \(p-1\) it holds whenever \(q\le m+1\), including a minimal Gaussian/Radau owner grid. It cannot be assumed when most reflected pins have inflated \(q\) close to \(p\). The counts in the first note did not adopt scalar owners and do not rely on this extra gate.

There is a precise measured alternative. For any actual input column \(v\) in a moved primitive and any test \(f\), write \(Rv=\sum_b v_bX^b\), and let \(\varepsilon_j\) be the scalar rule's degree-\(j\) moment error. When \(q\le p\), the adjoint failure for the monomial \(f=X^i\) is exactly
\[
   \sum_{b:\,i+b+1\ge p}v_b
      \left(\frac1{b+1}+\frac1{i+1}\right)\varepsilon_{i+b+1}.
\]
Indeed both shifted diagonal terms cancel; applying the ordinary integral gives zero, and the lower monomials of the quadrature defect are paid. This exposes which numerical top interpolation coefficients and which unpaid moments enter the real early/late covector. For example at \(q=p\) with a nonzero first moment error the unrestricted input \(v=E X^{p-1}\), \(f=1\) already fails, at every \(\gamma\). A transfer must check the actual \(\chi\)-generated vectors, or solve their summed causal tensor instead; an apparent clock alias alone does not move a reverse read legally. No fixed upper tableau or held computation was replayed here.
