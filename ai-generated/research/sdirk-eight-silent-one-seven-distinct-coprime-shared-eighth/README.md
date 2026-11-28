# Coprime extra aggregate shared by a literal silent and silent eighth

Use the [strict SDIRK8 detected seven-distinct chart](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) at ten stages over a characteristic-zero field. Only the individually weight-zero physical first stage has nonzero quadratic residual. Here \(k\ne0\), \(Q\) is affine nonconstant and coprime to \(L_4\), and exactly one literal front is active. The other literal front is physically silent and shares its actual clock \(z\) with physical silent eighth. This is the separate nonzero reverse aggregate; it is distinct from the active clocks and from the pole of \(Q\). The proof uses neither silent's actual cubic defect nor any assignment of its virtual amplitude. Other physical placements remain separate.

## The actual tail pins the reciprocal diagonal and affine shape

Write \(\boldsymbol h=N\boldsymbol g,\ \boldsymbol w=\boldsymbol b^{\mathsf T}M\), with \(N=A-\gamma I,\ M=CA-AC-A^2\). Let \(a\) be the active literal normalized clock and \(b\) the silent literal normalized clock, \(z=\gamma b\). The actual silent eighth has nonzero individual \(w_8\), so its clock geometry
\[
 2(1-\gamma-\gamma b)+\gamma k(u-2)=0,\qquad k=1+2u-u^2
\]
pins \(\gamma=1/D\), \(D=1+b-k(u-2)/2\). Put \(X=D-1\), \(C=X-u\), the normalized terminal and penultimate clocks. Define \(\widetilde L(Y)=D^4L_4(Y/D)\), polynomial in \(u,Y\). The actual ninth comparison, after canceling the nonzero \(k\), is \(A\,Q(X)=B\,Q(C)\) with
\[
 A=(u-2)\widetilde L(C),\qquad B=(2u+k(u-2))\widetilde L(X).
\]
Both are nonzero on the chart. The exact zero-gap padding of \(A-B\) gives \(F=(A-B)/u\). As \(X-C=u\ne0\), the affine denominator is proportional to
\[
 Q_*(Y)=B-F(Y-X).
\]
This is the actual \(Q\) shape up to scale, with \(Q_*(X)=B\), \(Q_*(C)=A\). Both facts are at active sites, not at either individual silent stage. The actual nonzero active literal defect \(h_a\) then gives the normalized profile \(Q_0 h=P\), where
\[
 Q_0(Y)=\widetilde L(a)Q_*(Y),\qquad
 P(Y)=h_a Q_*(a)\widetilde L(Y).
\]

## Exact literal fourth/fifth gap projection

Physical fourth and fifth are active. The padded fourth equation is \(\Phi=(Q_0H_4-P)/(Y-a)=0\). At actual fourth \(s\) use the two [cleared pure fifth equations](../sdirk-eight-silent-one-seven-distinct-gauss-nonliteral/README.md), now with affine \(Q_0\) and quartic \(P\). Their two earlier factors \(y-a,y-s\) may be removed: the polynomial remainders at \(y-s\) are exactly the respective defect-free literal values times \(\Phi\), and these earlier actual active sites are distinct from fifth. The resultant in \(y\) of the two residual cubics has degrees 27 in \(s\), 162 in \(u\). A pseudo-remainder by the fourth cubic reduces the second Sylvester determinant to size five. If \(n,m,j\) are the fourth, input, and pseudo-remainder degrees in \(s\), its standard redundant power of the fourth leading coefficient is \(j+n(m-n+1)-m\). The code verifies exact removal of that power; the actual leading-zero branch is retained by including the leading factor separately. The deflated gap projection has exact degree 1245.

Guarded gap degree is 757. Removed factors have only actual nonzero meanings: \(u,k,u-2,D\); the distinctness of the active literal from active tails; active \(L_4\) readings; the nonconstant \(Q_*\) coefficient, the active or separate-root denominator values, \(A,B\); and coprimality of \(Q_*,\widetilde L\). The guard arithmetic uses exact rational coefficient norms for \(\mathbb Q(t)\), \(2t^2=1\). A degree-preserving modular gcd of one only certifies exact coprimality; any factor *removal* is exact. A reduced multiplicity can suggest a batch of factors, but an exact division is required. If a rational norm is irreducible, the corresponding factor over \(\mathbb Q(t)\) is irreducible as well; a nonconstant factorization would factor its norm.

At stage four \(H_4(s)=0\) is impossible: its actual \(Ah\) must also vanish, but the exact literal \(H_4,Ah\) gcd is one. Intersect the guarded gap with \(\operatorname{Res}_s(H_4,\widetilde L(s))\) (exact intersection degree 36). Recover the common linear carrier by two small pseudo-remainders, and check its leading coefficient is a unit on this exact component. Its pseudo-divisions into both \(H_4\) and \(\Phi\) have exactly zero remainder there. Its root is therefore genuinely forbidden at actual stage four, so each exact common copy can be removed. This leaves fourth degree two on the 36-degree component. Outside it, the exact fourth leading split has a degree-311 gap component with fourth degree three and a degree-26 gap component with actual fourth degree two. These numbers count guarded projection factors before any repeated-root reduction used by the finite calculation. No reduced zero of \(H_4\) or leading coefficient is simply ignored.

## Signed masked test and replay

Let \(\xi\) be the physical pole of \(Q_*\). The exact signed rational functional \(f\mapsto\sum b_i f(c_i)/(c_i-\xi)^2\) is known through degree nine. Four active pegs \(\gamma a,1-\gamma,1-\gamma-\gamma u,\gamma s\) leave three distinct ordinary nodes. Their six masked moments give the cleared missing cubic by the Hankel/Cramer rule, without any positive weight assumption. Actual fifth is ordinary and is a root of that cubic and both padded literal fifth reads. The three pairwise padded resultants generate the unit ideal on the entire retained finite algebra. The true \(\gamma\) denominator, affine pole denominator and rational moment denominator are verified units; no individual reverse weight of the silent literal is required.

Run `python3 check_coprime_shared_eighth.py` in the sibling proof tree with `sympy==1.14.0` and `python-flint==0.9.0`. Its dependency paths include the anchored/reverse/shared six-clock packets, the literal-pole and Gauss helpers, and the constant nonliteral finite helpers. All four complete orientations use \((1103,t-161)\) for the final finite checks; other primes are only degree-preserving exact coprimality accelerators. Every reduced gap/fourth component is visited. The local-unit lift proves the characteristic-zero exclusion, without assuming an actual tableau admits a good reduction.

The [native Lean file](../../lean/RKCert/ReviewedNative/SDIRK8TailPinnedAffine.lean) kernel-checks the reciprocal diagonal and the actual tail-to-affine pin on Lean/Mathlib 4.36.0. The full chronology and exact arithmetic remain source-level. This is one coprime separate-aggregate placement, not the unrestricted **10–11** interval.
