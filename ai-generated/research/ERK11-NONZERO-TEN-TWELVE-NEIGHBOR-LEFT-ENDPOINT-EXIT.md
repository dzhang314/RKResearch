# The sole left profile endpoint zero is impossible at the neighboring singleton

**Scope.** In the fixed ordered, all-live, half-clock two-carrier \(17\)-stage ERK11 chart with both seventh boundaries new, \(q=10,n=12\), both full plateau pairs, and sole dormant row 9 sharing active physical row 8's singleton \(s=c_8\notin\{0,1,a,d\}\), this excludes the actual branch \(Q(0)=0\). The \(K_0=0\) alternative is already [closed](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-ZERO-COMPLETE.md); here use \(K_0\ne0\). Both physical endpoint zeros are already impossible, so the opposite actual endpoint is live. Reflection gives the exclusion \(Q(1)=0\) when the dormant row instead shares physical 10's singleton. It does not exclude \(Q(1)=0\) in the present \(s=c_8\) orientation, the both-endpoints-live case, or an unrestricted stage count.

## Width equations, leading fibers, and independent normalization guards

Use the [anchored endpoint proof](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-ENDPOINTS-AND-FIXED-RANK.md). It measures \(Q\) projectively by the actual primal row quotient \(Q_*=k_L/(X-a)\), \(k_L(X)=[\ell_X,R_9]\). Because \(Q(1)\) is live, the opposite product and \(P\) are measured in the full calibrated basis even if a sparse moment or affine pivot fails, then the left product is measured by the simple origin root. Thus \(P=\gamma P_*,Q=\gamma Q_*\) for one actual nonzero scale and both hulls are width-measured with no sparse-pivot assumption.

The two exact necessary width equations are the normalized endpoint width \(A=[\ell_a,R_9]_{\rm cleared}\) of bidegree \((16,14)\) and the actual opposite temporal width polynomial \(B\) of bidegree \((48,44)\), from the [finite mask proof](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-INDIVIDUAL-MASK-FINITENESS.md). All physical divisions in their construction are earned. The two coordinate fibers \(a=1\) and \(d=0\) (i.e. \(b=1\)) have exact univariate joint gcd one. In particular one may now use \(bd\ne0\) separately from any modulus.

Handle the exact leading coefficient \([b^{14}]A\) first. Its irreducible factors are a quartic \(J_4=42a^4-84a^3+56a^2-14a+1\), an octic, and \((12a^2-9a+2)^2\), up to rational scale. The quadratic discriminant is negative. At the exact quartic or octic \(a\)-field the \(b\)-degrees of \(A,B\) are respectively \((13,44),(13,43)\). At the simple \(a\)-places \((p,a)=(19,15),(17,10)\), the specialized degree 13 of \(A\) is retained and the **whole** residue \(b\)-gcd is one. Therefore any candidate \(b\), integral by the unit leading coefficient in its proper specialized degree, is impossible. No width is excluded by treating a lost leading coefficient as invertible.

A normalization-only exception also closes exactly. If \(Q_*\) had degree one, \(k_L\) would be proportional to \(X(X-a)\). The actual \(R_9=r_s^{\rm ev}+\eta r_d^{\rm ev}\) kills each right anchored model \((1-X)(X-s)(X-d)f(X)\) for \(\deg f\le2\). The left primal pairing forces the monic cubic \((X-a)(X-s)(X-d)\) to be orthogonal to degrees at most two with weight \(X(1-X)\). It must be the monic normalization of \(14X^3-21X^2+9X-1\). Its distinct roots are \(1/2,(7+\sqrt{21})/14,(7-\sqrt{21})/14\). The replay tests all six exact allocations to \((a,d,s)\), and each gives \(C_2-sH\ne0\) in \(\mathbb Q(\sqrt{21})\), contradicting the measured \(s=C_2/H\). Thus \(r=Q_*/X\) is nonconstant (and has degree at most three), not a vacuous constant ghost quotient.

## Reduced ghost law and the genuine opposite plateau

Use the actual normalization of \(R_9\) in \(k_L\), not a row-direction scale. Then \(k_L(s)=1/b_9\) by the reciprocal diagonal, because \(L_9=\ell_s+\epsilon\ell_a\) and \(k_L(a)=0\). With \(\omega=X(1-X)(X-a)(X-d)\), \(\rho=b_9\omega(s)\), this yields
\[
 \rho Q_*(s)=s(1-s)(s-d).
\]
Put \(\Omega=-\omega\), \(R=\Omega Q_*=X(X-1)(X-d)k_L\), and \(M_R(Z)=\int(R(X)-R(Z))/(X-Z)\). At \(0,d\) the anchored right row read evaluates the divided integrals directly:
\[
 M_R(0)=-(1-s)(s-d),\qquad
 M_R(d)=-s(1-s)-\eta b d,
\]
so \(M_R(d)-\rho Q_*(s)/(d-s)=-\eta b d\). These are exact identities of the true profile, not assumed equality of the shared dormant and active states.

With \(f=-4Q_*(e)/P_*(e)\), \(e=1-b/2\), write \(p=P_*(d),q=Q_*(d),t=B_{\tau,*}(d),\delta=q-fp\). The true right pair has first state \(f\) and other state \(g\), both nonzero and distinct, so \(\delta\ne0\), \(t-fq=g\delta\). The [actual ordinary affine plateau law](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-AFFINE-PLATEAU-LAW.md) now simplifies to
\[
 \gamma\lambda_*\delta=\eta f(t-fq),\qquad
 \gamma\lambda_*=\eta f g ,
\]
using the already live \(b,d\). In particular \(\eta\ne0\) on this chart. The unmultiplied law remains valid if \(P_*(d)=0\). It neither assumes \(Q_*(d)\ne0\) nor divides by an ordinary plateau mass.

For the active singleton hull \(D_s\), both polynomials
\[
 A_{\rm gh}=D_sM_R-\rho Q_*(s)D_s/(X-s),\qquad B_{\rm gh}=P_*^2 X(X-1)
\]
have zero constant coefficient: the former by the exact \(M_R(0)\) read. Thus the ghost congruence reduces exactly to
\[
 \widetilde A+\gamma\widetilde B=0\pmod r,\qquad
 \widetilde A=A_{\rm gh}/X,\quad \widetilde B=P_*^2(X-1).
\]
No independently chosen constant ghost coefficient is presumed live; in fact the **unreduced constant row is identically zero**. The reduced denominator class \(\widetilde B\) is invertible modulo \(r\): opposite endpoint live gives \(r(1)\ne0\), and \(P,Q\) cannot share a root by \(P_* B_{\tau,*}-Q_*^2=\lambda_*D_s\) with \(\lambda_*\ne0\) and \(P\) live at every singleton. This covers all reduced normalization-only zero cases, at the true degree of \(r\). In particular a lowered quartic leading coefficient was not used as a stage contradiction.

Use the homogeneous \(D_\lambda,L_\lambda\) of the affine plateau proof, with \(\lambda_*D_\lambda=L_\lambda\), valid also for constant \(P_*\). The compact version of the simplified true right plateau row is
\[
 U+\gamma V=0,\qquad
 U=-\eta f\bigl(D_\lambda q\delta+L_\lambda D_s(d)\bigr),\qquad
 V=L_\lambda p\delta .
\]
It follows by multiplying the unmultiplied law by \(pD_\lambda\), not by inverting \(p\) or using a degree-one assumption on \(P\). A necessary compatibility is
\[
 V\,\widetilde A-U\,\widetilde B=0\bmod r .
\]
This uses a true ordinary two-row plateau and is smaller here than recovering a cubic-response polynomial and an ordinary mass by eight-node inversion.

## Exact projection and complete guard fibers

Take primitive integer representatives of \(A,B\). For their Sylvester determinant, use the \(a\)-degree bound \(16\cdot44+48\cdot14=1376\) and absolute coefficient bound
\[
 \|A\|_1^{44}\|B\|_1^{14}.
\]
The latter follows by expanding the determinant and bounding the univariate coefficient norms by the products of row sum norms. It has 6880 bits for these inputs. The replay takes 115 distinct prime reductions at retained \(b\)-degrees, with a 6901-bit combined modulus (strictly greater than twice the coefficient bound), then reconstructs the exact signed integer coefficients. This is not inferring a characteristic-zero factorization from a small-prime specialization. The norm has degree 1294. Exact squarefree and irreducible factorization gives all \(a\)-factor degrees and multiplicities
\[
 1^{24},\,2^8,\,2^{16},\,8,\,8^2,\,8^3,\,8^{56},\,
 12^3,\,12^3,\,12^4,\,20^3,\,258,\,288 .
\]
The linear factor is the forbidden width \(a=0\); the two quadratics have negative discriminants. The simple octic is the leading-loss octic already checked.

The following small factors divide the indicated **exact** guard norm with \(A\). At each place the exact \(a\)-factor is simple and \(A\) retains \(b\)-degree 14. The whole joint residue gcd of \(A,B\) and the whole gcd of \(A\) with the named guard are the same linear root. The derivative of \(A\) there is a unit. The exact guard-zero root exists by its exact norm; both it and any exact candidate are integral by \(A\)'s leading unit and reduce to the same root. Hensel uniqueness makes the two exact \(b\) roots equal.

| Degree, multiplicity | Exact lost guard | \((p,a,b)\) | Guard norm degree |
|---|---|---|---:|
| 8,2 | \(b\) | \((17,14,0)\) | 16 |
| 8,3 | \(H\) | \((19,12,9)\) | 60 |
| 12,3 | \(z_D\) | \((23,20,5)\) | 120 |
| 12,3 | \(U\) from the measured width equations | \((29,28,23)\) | 176 |
| 12,4 | \(J_0\) | \((17,3,2)\) | 58 |
| 20,3 | \(s-d\) | \((41,26,31)\) | 76 |

For the octic of multiplicity 56, the whole residue \(b\)-gcd has degree four; do not replace it by an arbitrary selected simple branch. In the exact octic \(a\)-field the replay derives an \(H\)-zero \(b\)-root from the linear subresultant of \(A,H\), verifies that root in both, and removes **all four exact copies** of its factor in \(A\). The remaining exact degree-ten \(b\)-polynomial retains its degree at the simple place \((19,13)\) and has whole residue gcd one with \(B\). Thus every actual root either kills the already-live \(H\) or is excluded by the residual gcd. This uses no inference from the vanishing of an \(H\) residue alone.

## The two large factors

For degree 258 the lost guard is \(P_*(0)\). On this sole-left-endpoint branch it is live: \(P_*(0)=Q_*(0)=0\) would kill \(\lambda_*D_s(0)\), and 0 cannot be an active singleton if \(Q_*(0)=0\). Form its width numerator from the **right** measured orientation by evaluating its first-pool line at \(Y=1\), with all endpoint/shape coordinate factors kept live. The companion's normalized width polynomial has bidegree \((68,67)\); a common coefficient factor of a true nonzero first-pool line may be removed. Its exact resultant with \(A\) has degree 1864 and is divisible by the degree-258 factor. This exact norm is verified by the same bounded CRT method (10220-bit coefficient bound, 171 primes, 10261-bit combined modulus). At the simple \(a\)-place \((41,10,28)\) the two whole residue gcds, with \(B\) and with the \(P_*(0)\) guard, are \(b-28\); \(A\) retains degree 14 and has derivative 35 there. The same simple-root lifting forces actual \(P_*(0)=0\) in characteristic zero.

For degree 288 use the simple place \((47,12,9)\). The whole joint residue gcd is \(b-9\) and \(A\)'s leading coefficient is a unit. All actual width, shape and plateau denominators are units. Both products are measured without a spare pivot, with residues \(t_L=44,t_R=5\). The profiles and two oriented hulls, in increasing coefficient order, are
\[
 P_*=(46,7),\quad Q_*=(0,18,38,0,4),\quad
 B_L=(27,35,7,1),\quad B_R^{\rm oriented}=(30,3,36,1).
\]
The reduced \(r=Q_*/X\) retains its full cubic leading unit. The right plateau has \(\eta=29,(D_\lambda,L_\lambda)=(13,38)\), and the compact true coefficients are \((U,V)=(7,4)\) modulo 47. Instead of the required zero, the exact reduced ghost/plateau remainder is
\[
 7+31X+30X^2\bmod47 .
\]
All actual width roots of this degree-288 factor therefore fail; no tableau entry was reduced before being width-measured.

These are all exact width factors, including the leading and normalization-only cases. The checkpoint-free replay uses python-flint 0.9.0 and SymPy 1.14.0 (reference wall time 98.139 seconds). The proof is ordered-field at its inherited geometric ingress and exact characteristic-zero arithmetic thereafter; it is not a fully formalized Lean tableau theorem.
