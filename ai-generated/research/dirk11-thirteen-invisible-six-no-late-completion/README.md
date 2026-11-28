# The three-ghost torsion gate and the complete no-late invisible-six census

**Results.** In the normalized no-late invisible-six DIRK11/13 chart,
\(\alpha\ge3\) is impossible before introducing any polynomial carrier
or reciprocal multiplier. The exact new cleared prefix certificate
keeps the ghost head factors and ordinary weights, so it is a
torsion identity over any commutative ring admitting the indicated
paid reads. The older carrier closures for \(\alpha=0,1,2\) together
cover all possible no-late arrays over characteristic-zero fields
with the given signed/support/rank hypotheses. No unrestricted stage
bound changes: real DIRK11 remains **13–14**.

## 1. The actual low-grade reverse chronology

Use the normalized support and paid annihilator spaces of the
[no-late count](../dirk11-thirteen-invisible-six-no-late/README.md).
There are exactly six zero-weight physical cubic-dirty rows at
distinct clocks, with both cubic heads live, and seven distinct
ordinary clean rows including the physical endpoints. In reverse
the array is \(T,v,u,w,[\alpha],V,[\beta],B,[\gamma],O\).
The brackets are physical blocks, not counts of aggregated weights.
The first three nonendpoint ordinary clocks are distinct and
nonzero and their ordinary weights are live. There is no assumption
that a ghost cannot share an unrelated ordinary numerical label.

Put \(Y=1-c\), \(N=A^{\mathsf T}\) in literal reverse order,
\(W(f)=b_{\rm wt} f(Y)\), and \(P_*=Y(Y-u)(Y-v)\).
For the true weighted primitives of \(P_*,YP_*\), the paid
grades give \(G p(Y),G q(Y)\) as errors with \(\deg p\le1\),
\(\deg q\le2\), respectively. Here \(G\) is the true reflected
cubic, not an arbitrary auxiliary row. At a physical first-gap
ghost the only possibly nonzero weighted input of either
polynomial is the literal stage \(w\): the other ordinary
values through the ghost are zero, and ghost weights vanish.
Thus at that ghost \(G_z(q(z)-w p(z))=0\).
At literal old \(u,v\), even the \(w\) input is not available,
so the read is the weighted zero-start primitive there.

Scale the primitive polynomial profiles by \(P=12p,Q=60q\)
and write \(k=5w\). For any three ghosts \(z_0,z_1,z_2\)
in the first gap, the cleared inputs are
\[
 G_{z_i}(Q(z_i)-kP(z_i))=0,\quad i=0,1,2.
\]
At the old \(u\), the genuine two reads are
\(G_uP(u)=b_u\,I_{12}(u,v)\) and
\(G_uQ(u)=b_u\,J_{60}(u,v)\), with the switched equations at \(v\).
Here
\[
 I_{12}(u,v)=u^3(2v-u),\qquad J_{60}(u,v)=u^4(5v-3u).
\]
These are exactly \(12IP_*(u)\) and \(60I(YP_*)(u)\)
with the same orientation. Nothing has been canceled, including
at a ghost with a head or clock difference that is a zero divisor.

## 2. Denominator-free torsion transfer

For \(H=Q-kP\), a quadratic or less, put
\(D=(z_0-z_1)(z_0-z_2)(z_1-z_2)\), \(M=G_{z_0}G_{z_1}G_{z_2}\).
The polynomial interpolation identity says
\[
 D H(Y)=
 H(z_0)(z_1-z_2)(Y-z_1)(Y-z_2)
 +H(z_1)(z_2-z_0)(Y-z_0)(Y-z_2)
 +H(z_2)(z_0-z_1)(Y-z_0)(Y-z_1).
\]
It is an integer coefficient equality, regardless of zero divisors
or signs. The weighted ghost reads give \(MD H(Y)=0\) after
multiplication. Multiply by \(G_u,G_v\) at the appropriate old
clock, and substitute the old reads. This proves
\(MD b_u(J_{60}(u,v)-kI_{12}(u,v))=0\), and likewise at \(v\).
Cross-multiply these two equalities to eliminate \(k\).
The exact nodal identity is
\[
 J_{60}(v,u)I_{12}(u,v)-J_{60}(u,v)I_{12}(v,u)
       =6u^3v^3(u-v)^3 .
\]
Consequently all the actual cleared prefix reads give
\[
 \boxed{6u^3v^3(u-v)^3\,b_u b_v\,G_{z_0}G_{z_1}G_{z_2}\,D=0.}
\]
The companion checks every step over a commutative ring. In a
characteristic-zero field every displayed factor is live for this
chart, so three first-gap ghosts are impossible. Over other rings
the conclusion transfers when the actual cleared reads are paid and
the displayed product is nonzero, for example if its factors are
regular in a nontrivial ring. **Individual nonzero factors need not
suffice in a ring with zero divisors.** This is not a new
positive-characteristic full RK theorem: the required primitive
and paid-rank ingress must itself be justified in the chosen
coefficient ring (the conventional unscaled formulas pay
denominators including 2, 3 and 5).

For completeness the same style of forward certificate implements
the other chronology cut. At the first nonorigin forward clean row
of clock \(x\), with two prior ghosts of clocks \(p,q\), taps \(l,r\)
and cubic entries \(g,h\), the actual \(Ag,A(Cg)\) equations give
\(lg+rh=0,\,lpg+rqh=0\). Multiply by \((p-q)gh\) to kill
the two taps. The cleared \(C(2)\) and zero cubic ordinary equations,
\(2(lp+rq+dx)=x^2,\ 3(lp^2+rq^2+dx^2)=x^3\), then give
\((p-q)gh\,x^3=0\). The native one- and zero-ghost versions give
\(g x^3=0\) and \(x^3=0\), respectively, without a fictitious dummy
clock in a small field. The actual origin contributes no positive
power. Thus in the characteristic-zero normalized shape
\(\gamma\ge3\). These two cuts use the original tableau and not
order conditions of any truncated or reweighted scheme.

## 3. Complete no-late branch ledger

The two chronology cuts and \(\alpha+\beta+\gamma=6\) leave
only these counts, verified by the portable Lean module:

| \(\alpha\) | \((\beta,\gamma)\) |
|---:|---|
| 0 | \((0,6),(1,5),(2,4),(3,3)\) |
| 1 | \((0,5),(1,4),(2,3)\) |
| 2 | \((0,4),(1,3)\) |

The [actual grade-six carrier](../dirk11-thirteen-invisible-six-prefix/README.md)
is a nonzero \(U\) of degree at most three: it agrees with the
nonzero \(g\) at all six ghosts. Its reciprocal multiplier
\(\tau\) in \(G(U(c)-g)=\tau H_{\rm bary}\) is not assumed
nonzero. If \(\tau=0\), the old three distinct ordinary rows
with individually live \(G\) require three roots of \(U\).
This forces a cubic old-node hull, and at each nonold
ordinary nonterminal row forces \(G=0\). In particular no
lower-degree \(\tau=0\) case is discarded by a generic
division. For nonconstant \(U\), the genuine grade-five
masked primitive before the first forward positive clock
\(I(XU)+UQ_2\) vanishes at the \(\gamma\) distinct ghost clocks.
The polynomial degree bound of \(\deg U+2\) gives
\(\gamma\le\deg U+2\): otherwise \(U\mid I(XU)\) forces a
monomial, which fails the first clean reads and the origin
liveness. Thus degree one allows only \(\gamma=3\);
degree two allows \(\gamma=3,4\); and a cubic
\(\gamma=3,4,5\). Constants are not subject to this latter
nonconstant cutoff.

* **\(\alpha=0\):** the [forward mask](../dirk11-thirteen-invisible-six-prefix/README.md)
  excludes degree zero and degree one in the entire
  \(\alpha=0\) shape and hence excludes \((\beta,\gamma)=(0,6)\).
  The [quadratic closure](../dirk11-thirteen-invisible-six-quadratic-closure/README.md)
  covers \(\gamma=3,4\), including the [separate double leader and
  fixed Lobatto contacts](../dirk11-thirteen-invisible-six-quadratic/README.md).
  Cubic \(\tau=0\) is covered in \((1,5)\) by the
  [five-prefix proof](../dirk11-thirteen-invisible-six-cubic-zero-five/README.md)
  and in \((2,4),(3,3)\) by the
  [two-middle-root proof](../dirk11-thirteen-invisible-six-cubic-zero-two/README.md).
  Cubic \(\tau\ne0\) is covered for all three by the
  [exact live global proof](../dirk11-thirteen-invisible-six-cubic-live-global/README.md),
  including the earlier separate exceptional guard cases.
* **\(\alpha=1\):** the [complete alpha-one ledger](../dirk11-thirteen-invisible-six-alpha-one-completion/README.md)
  covers degree zero for all counts, degree one at \(\beta=2\),
  degree two at \(\beta=1,2\), and cubic in both reciprocal
  branches at all three counts. The actual fifth-prefix bound,
  not a cubic-only assumption, removes the inadmissible lower-degree
  cases. Each cubic proof uses its true middle count.
* **\(\alpha=2\):** the [unified degree-24 ordinary proof](../dirk11-thirteen-invisible-six-alpha-two-completion/README.md)
  first excludes \(\tau=0\) from a fourth-row nonzero signal
  common to both counts. It then closes each live branch by a distinct
  exact rank-72 test, for every actual degree at most three.
  No withdrawn combined grade-seven calculation is used.

This is an exhaustion for the stated no-late invisible-six chart.
The separately [paid late exclusion](../dirk11-thirteen-invisible-six-paid/README.md)
handles a ghost appearing **before** the third ordinary
nonendpoint row in reverse chronology. Combining them also exhausts
the normalized **exact six unweighted distinct dirty clocks**
shape at that earlier proof's signed and clock-reduction ingress.
This is **not** a classification of arbitrary aggregated \(r=0\)
support, other dirty counts, all tableaux with 13 stages, or other
coefficient domains. The full characteristic-zero no-late statement
starts after the exact normalized ranks and support are supplied.

## Reproduction and Lean scope

Run **python3 verify.py PATH/TO/RKResearch** with SymPy and
python-flint 0.9. It recomputes the integer polynomial identities,
the exact nine-count enumeration, verifies the frozen closure
manifests and independently multiplies the two previously
stored finite-field Bézout witnesses. The companion cold logs
rerun the late certificate, both zero-cubic alpha-zero cases,
the quadratic closure and separate contacts, and the exact
stored alpha-zero live guard-support ranks. The historical
large raw alpha-zero live QQ projection was **not** regenerated
by this wrapper; the cited hashed proof and its separate replay
retain that role.

The commutative-ring scalar module checks on Lean/Mathlib
4.36.0 with standard axioms. The separate count module uses
no Mathlib and checks on Lean 4.34.1, 4.35.0, 4.36.0 and
4.37.0-rc1. Neither is advertised as a native proof of the
full rooted/tableau ingress or a whole HasOrder endpoint.
