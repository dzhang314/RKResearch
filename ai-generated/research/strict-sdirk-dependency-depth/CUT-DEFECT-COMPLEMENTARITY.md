# Paid adjacent-cut complementarity for the full stage-defect space

A field-linear necessity theorem across orders, not a new unrestricted
DIRK stage floor. The base form is a literal physical cut pairing; its
weights can be zero or signed. The useful rank is the rank of new
**defect directions** transported by the cut masks, not the number of
individually zero readout equations.

## 1. Paid setup

Work over a characteristic-zero field \(K\). Let \(A=\gamma I+B\) be a
common-diagonal triangular tableau, \(B\) strictly lower triangular,
\(c=Ae\), and assume literal rooted order through \(p\). The grade of a
stage tree \(\Phi(t)\) is \(|t|-1\). Its exact stage polynomial is
\((|t|/\rho(t))X^{|t|-1}\), where \(\rho\) is the tree factorial.
Let \(P_j\) be the actual span of stage trees of grade at most \(j\).
Let \(Z_j\) be the actual image of the combinations of these trees whose
exact stage polynomial is zero. This is the full defect space of the
grade. The definition does not assume that the model descends to a
function on all actual stage vectors.

Componentwise multiplication merges roots, adds grades, and multiplies
the exact polynomials: this follows from
\(\rho([t_1,\ldots,t_k])=(1+\sum_i|t_i|)\prod_i\rho(t_i)\).
The operation \(A\) lifts by one unary root, and applies formal integration
\(J\) from 0 to \(X\) in the model. Thus \(B\) raises grade by at most one
and applies \(J-\gamma I\). The output \(b^T\) applies integration from
0 to 1 to every paid model.

Fix incoming and outgoing lengths \(\ell,r\ge0\), residual stage grade
\(\nu=p-1-r-\ell\ge0\), and the physical window
\[
 I=[\,\ell+1,s-r\,],\qquad
 w_i=(b^TB^r)_i(B^\ell e)_i.
\]
A positive shift of either length restricts the physical window.
A shifted mask, optionally decorated with an actual \(f\in P_j\), is
\[
 \eta_i=(b^TB^{r+u})_i(B^{\ell+v}e)_i f_i,\qquad
       u,v\ge0,\qquad \operatorname{cost}(\eta)=u+v+j .
\]
For \(z\in Z_a\) and \(y\in P_b\), the literal product identity is
\[
 \sum_{i\in I}\eta_i z_i y_i=0
                  \quad\hbox{if }a+b+\operatorname{cost}(\eta)\le\nu .
 \tag{1}
\]
Indeed the maximum rooted order is
\(r+\ell+\operatorname{cost}(\eta)+a+b+1\), and the exact merged model
contains the zero model of \(z\). This includes true branch/defect products.
There is no claim that (1) is an identity of scalar clock words alone.

## 2. Complementarity and the near-saturation test

Put \(J_0=\{i\in I:w_i\ne0\}\), \(n=|J_0|\), and use the nondegenerate
diagonal form \(W=\operatorname{diag}(w_i)_{i\in J_0}\).
Fix \(q,m\) with \(2q\le\nu\), \(q+m\le\nu\). Write
\(D=Z_q|_{J_0}\), \(d=\dim D\), and let \(U\subset P_m|_{J_0}\)
be a nondegenerate probe subspace for \(W\), of dimension \(g\).
By (1), \(D\subset U^\perp\), and \(D\) is totally isotropic (all its
pairings, not just each chosen column square, vanish). Since \(U\) is
nondegenerate, \(U\cap D=0\). Consequently
\[
 L=(U+D)^\perp,\qquad D\subset L,\qquad
                 \dim L/D=n-g-2d=:\sigma\ge0.                \tag{2}
\]

For each chosen paid mask \(\eta_j\), take a possibly smaller input
defect grade \(a_j\le q\), and require
\[
       a_j+\max(q,m)+\operatorname{cost}(\eta_j)\le\nu.       \tag{3}
\]
If \(\operatorname{supp}\eta_j\subseteq J_0\), multiply literally by
its diagonal ratio \(T_j=\operatorname{diag}(\eta_{j,i}/w_i)_{i\in J_0}\).
Both types of pairings in (1) show \(T_j(Z_{a_j}|_{J_0})\subset L\).
This gives the simultaneous defect-rank test
\[
 \boxed{\quad
 \dim\!\left(D+\sum_j T_j(Z_{a_j}|_{J_0})\right)-d
                   \ \le\ n-g-2d .
 \quad}                                                       \tag{4}
\]
In particular an independently witnessed direction modulo \(D\) consumes
one cut dimension after the two per defect mode are already reserved.
For a measurable subspace \(D_0\subseteq D\), any rank witnessed just
with its columns and paid transfer columns also works: if their joint
rank is \(a+t\) and \(\dim D_0=a\), then \(n\ge g+2a+t\), since the joint
span lies in \(L\) and \(d\ge a\).
This measures a sum of subspaces, never a sum of separate mask ranks.

At exact saturation \(\sigma=0\), every fully paid mask (\(a_j=q\))
must preserve \(D\). In particular, nearby strict donor/readout cuts
\((u,v)=(0,1),(1,0)\) give simultaneous invariance under their
two ratios when paid. With no spare grade for a full shift, the same
test can still force \(T_j(Z_{q-1}|_{J_0})\subset D\), not invariance
of the full \(D\). The leaf multiplier \(C=\operatorname{diag}(c_i)\)
is a further fully paid mask when (3) permits cost one.
For one defect line, and for masks whose paid input contains that line, (4) says the affine dimension of the joint ratio
labels on its nonzero support is at most \(\sigma\): multiply the rows
of the matrix of labels with a leading column of ones by the nonzero
defect coordinates. Thus even one extra slot bounds how the literal
adjacent ratios can differ on that support.

At saturation the commuting diagonal operators split \(D\) as a direct
sum over their joint label fibres. To obtain the projector onto a fibre,
for each other fibre choose one distinguishing operator, subtract its
other-fibre value and divide by the difference at the selected fibre,
then multiply these factors. This is an algebraic consequence of
invariance, not a new higher-order payment. On every fibre the projected
defect space is isotropic for the restricted \(W\). A singleton or any
anisotropic fibre cannot carry a defect. Over an ordered field, a
defect-bearing fibre needs both positive and negative weights; its
defect dimension is at most the smaller sign count (project onto
either sign block). Over an unordered field anisotropy is the correct
condition, not a sign assertion. In particular a paid ratio can
separate repeated clock labels; distinct clocks are not a hypothesis.

A separate optional strengthening uses actual extra *leaves*. If
\(C^jD\subset L\) for all \(0\le j\le t\) by (3), \(D\ne0\), and
the clocks are injective on its support, then \(\sigma\ge t\).
Indeed any stall of the increasing sums
\(D+CD+\cdots+C^jD\) makes the preceding sum \(C\)-invariant.
A clock projector there would then produce a coordinate line at
a nonzero defect coordinate, contradicting orthogonality to \(D\)
in \(L\). Arbitrary powers of an adjacent cut ratio are **not**
automatically paid; this argument uses literal leaf degrees.

## 3. Exact treatment of zero base weights

Do not set \(\eta_i/w_i\) to zero when the numerator can be nonzero
and the denominator zero. For the original \(J_0\), take input tuples
\(z=(z_j)_j\) in \(\bigoplus_j Z_{a_j}|_I\). Put
\[
 \Lambda(z)=\left.\sum_j\eta_j z_j\right|_{I\setminus J_0},
 \qquad
 \Psi(z)=\frac{\left.\sum_j\eta_j z_j\right|_{J_0}}{w|_{J_0}}.
\]
Choose stage lifts of \(U\) on \(I\). Equation (1) and zero outside
leakage give \(\Psi(\ker\Lambda)\subset L\), and hence
\[
 \dim(D+\Psi(\ker\Lambda))-d\le\sigma.
 \tag{5}
\]
Allowing all tuples instead adds at most \(\operatorname{rank}\Lambda\)
to the right side, since passing to the kernel loses at most its
codimension. The masks can thus overlap and their outside leakage can
cancel; there is no assumption that any stage is active for every cut.

There is also a leakage-free test for fully paid masks. Suppose each
chosen shift or mark is paid with \(a_j=q\) in (3). Take a scalar linear
combination \(w^*\) of those masks and \(w\). It can be chosen nonzero
at every site of their support union while keeping the lifted probe
Gram nonsingular: multiply the nonzero linear coordinate polynomials by
the Gram determinant polynomial, which is nonzero at the original
base coefficients, and avoid its zero locus over the infinite field.
The same payment proves (2) for \(w^*\), and all original masks
(including \(w\)) act without leakage. Their joint ratio fibres are
exactly the projective signatures of the actual rows
\([w_i:\eta_{1,i}:\cdots:\eta_{k,i}]\) on this union.
This chooses an auxiliary testing form, not perturbed tableau
coefficients or a positive physical form. Its \(n,d\) are measured
on the union; one must recompute the slack there. Zero slack for the original base form does not by itself imply saturation for the union form.

## 4. Physical adjacent pivots and a stage-support consequence

Let \(z=Ac-c^{\odot2}/2\in Z_2\). Its first nonzero possible pivot is
\(f=1\) with value \(\gamma^2/2\) if \(\gamma\ne0\). In the strict
case \(\gamma=0\), if \(B_{21}\ne0\) the first pivot is \(f=2\)
with value \(-B_{21}^2/2\). Whenever the required adjacent edges from
\(f\) onward are nonzero,
\[
 (B^jz)_i=0\ (i<f+j),\qquad
 (B^jz)_{f+j}=z_f\prod_{k=f+1}^{f+j}B_{k,k-1}\ne0 .
\]
The entry uses the unique length-\(j\) increasing path with those
endpoints. Also \(B^jz\in Z_{j+2}\).
For \(0\le j\le q-2\), use the columns whose pivot lies in the
actual active set \(J_0\): at those pivot rows the minor is triangular
with nonzero diagonal. Thus
\[
 d\ \ge\ \big|J_0\cap\{f,\ldots,f+q-2\}\big|.                \tag{6}
\]
Only adjacent edges up to the last stated pivot are needed; this
doesn't assert every middle window contains a pivot. Full isotropy,
the cut transfer test, and this triangular lower rank are independent
parts of the argument.

For example set \(r=\ell=0\) and \(q=\lfloor(p-1)/2\rfloor\), \(p\ge5\).
The \(q+1\) power probes through \(c^q\) have the exact nonsingular
Hilbert Gram \(1/(i+j+1)\), \(0\le i,j\le q\), by paid bushes.
If \(e_0\) physical pivot sites in (6) and \(l_0\) other physical
sites have \(b_i=0\), then (2) and (6) give
\[
              e_0-l_0\ge 3q-1-s.                            \tag{7}
\]
In particular an all-active tableau with the stated adjacent prefix
obeys \(s\ge3q-1\), with no positivity of \(b\) and no constraint on
the sign of \(\gamma\). More generally equality in (7) forces equality
in both the pivot rank and the cut dimension. At even \(p\) there is
one spare leaf at this cut. If at least one pivot is active and the
clocks are distinct on defect support, equality is impossible. A
fully paid adjacent ratio marking an isolated defect-bearing joint
signature upgrades equality in the same way whenever the support
or union-form conditions apply.

At a genuinely shifted strict cut (\(\gamma=0\)), the clock Gram
through degree \(m\) is automatically nonsingular for \(2m\le\nu\).
Its moments are
\[
 \sum_i w_i c_i^a=\frac{(\ell+a)!}{\ell!(r+\ell+a+1)!}
 =\frac1{\ell!r!}\int_0^1 X^{\ell+a}(1-X)^r\,dX .
\]
The beta integral of a real nonzero polynomial square is positive,
so the rational Gram determinant is nonzero over every
characteristic-zero field. Over an ordered field the same
nondegeneracy holds for \(\gamma\le0\): expand
\((J-\gamma I)^r\) and \((J-\gamma I)^\ell\) as nonnegative combinations
of the corresponding strict beta forms, with the original beta
form having coefficient one. Each rational beta form remains positive
over any ordered field (for example by rational positive-pivot
diagonalization). No such automatic claim is needed for
\(\gamma>0\) on shifted cuts; use the literal measured probe Gram.
Always \(n\le|I|=s-r-\ell=\nu+1+(s-p)\) for a nonempty window, so
(4) bounds the *physical* room when \(s-p\) and \(\nu\) are small.
It counts neither timed copies nor clock multiplicities as new stages.
Neither (7) nor (4) proves an unstructured stage increment in the absence
of the stated adjacent pivots, measured cut rank, or separation.
