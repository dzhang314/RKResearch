# The strong cubic tests follow generically from actual order ten

This adapts the [scalar obstruction](README.md) to a literal
six-opening cubic decoder. Under the stated reverse first- and
second-defect assumptions, a rational order-ten tableau in this
chronology must have a **last opening donor pure through derivative
size five**. It is not an exclusion of that remaining pure-donor
case, or of a different opening or chronology.

## Literal low and high blocks

The canonical six-row opening has clocks \(0,e,s,p,q,r\), where
\(s=2p/3\); \(e,p,q,r\) are nonzero and \(p,q,r\) distinct.
The \(e\) row reads only the origin; the \(s\) row has \(e\)-tap
\(s^2/(2e)\); the \(p\) row has \(s\)-tap \(3p/4\) and origin
tap \(p/4\). The \(q,r\) rows have no \(e\)-tap. They may read
the origin, \(s,p\), and additionally \(q\) for the \(r\) row.
Their tap sums are their own clocks, and their first and second
scalar primitive moments are exact. In the \(s\) row the origin
tap likewise fills the row sum. Only the opening origin has an
output weight.

Let \(\Pi\) interpolate the old entries at \(0,p,q,r\) as a
cubic, \(E\) evaluate at the actual high clocks, and
\(J f(X)=\int_0^X f(Z)\,dZ\). The actual forward high-to-old
block is \(EJ\Pi-BE\Pi\), with strictly causal high-to-high
block \(B\). Use the reverse weighted transpose \(L\) of \(B\).
In scalar statements this means
\[
 \sum_i w_i f(x_i)(BEg)_i
   =\sum_i w_i (LE f)_i g(x_i),
\]
written in one consistent high-row indexing; forward and reverse
versions are conjugate by reversing indices. Require
\(L\boldsymbol 1=\boldsymbol y\) and that the raw first and
second reflected defects
\[
 \boldsymbol u=L\boldsymbol y-\boldsymbol y^{\odot2}/2,\qquad
 \boldsymbol g=L\boldsymbol y^{\odot2}-\boldsymbol y^{\odot3}/3
\]
have zero weighted aggregate at **every** scalar high clock.
This holds in the intended signed-triple raw setup with exact
singleton primitives. Even if an individual singleton weight
vanishes, the weighted identities used in the scalar obstruction
still hold. One may require all weights nonzero to define \(L\)
by division; the argument only needs the displayed pairing.

The origin and the donor rows \(p,q,r\) have every elementary
stage derivative through size four equal to its scalar model.
Indeed, through size three the \(s\) row is pure by its exact
first scalar moment. All non-origin taps of the donor rows read
that row and earlier donors, and their next scalar moment is paid.
It follows inductively from the literal high-to-old block that
every high stage derivative through size five is pure: on a
child of size at most four, its low interpolation and high
profile are evaluations of the **same** scalar monomial.
This argument does not assume that the \(s\) starter is pure
through size four.

## True source trees force the cubic pressure

Normalize the elementary stage derivative
\(\boldsymbol\Phi_t\) by its tree constant so that its pure model
is \(\boldsymbol c^{\odot(|t|-1)}\); a child of size \(m\) then
contributes the primitive factor \(m A\boldsymbol\Phi_t\).
For a tree \(t\) of size \(m=5\), or of size \(m=6\) whose
immediate children have size at most four, its high source
profile is pure. Its projected low error is
\[
              f_t=\Pi\boldsymbol\Phi_t^{\rm old}-X^{m-1}.
\]
The true rooted order condition for the parent with this child
and three leaf children, of size \(m+4\le10\), implies
\[
            \sum_i w_i x_i^3[(EJ-BE)f_t]_i=0.
\]
There is no other exceptional child; the opening output at the
origin vanishes. The exact scalar moments through degree nine
identify the model part and allow integration by parts:
\[
    \int_0^1 X^3 J f_t(X)\,dX
       =\int_0^1 (1-X^4) f_t(X)/4\,dX .
\]
Both scalar integrands have degree at most nine;
\(Jf_t(0)=f_t(0)=0\), so the origin term can be included.
The weighted transpose pairing and exact reverse row sums then
turn the rooted condition into the weighted pairing of \(f_t\)
with \(-3\boldsymbol u+3\boldsymbol g-\boldsymbol k\).
The \(\boldsymbol u,\boldsymbol g\) terms vanish by their
weighted aggregates. Thus the literal cubic defect functional
\(K(f)=\sum_i w_i k_i f(x_i)\) annihilates **all these actual
source errors**.

Write the two three-coordinate donor vectors
\[
 \boldsymbol Q=(A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4)|_{p,q,r},
 \qquad \boldsymbol V=(A_{i,s})_{i=p,q,r},
 \qquad C_0=\operatorname{diag}(p,q,r).
\]
At size five, use (i) the bush; (ii) the single child equal
to the size-four bush; (iii) the single child equal to the
size-four tall tree. Case (i) gives the degree-four interpolation
error. Subtracting (i) from (ii) gives \(4\boldsymbol Q\) at
the three donors. Subtracting (ii) from (iii) gives
\(-4s^3\boldsymbol V\): the normalized size-four tall profile
at the \(s\) starter is exactly zero, because the earlier
normalized size-three tall is zero at \(0,e\).
The origin and donors have zero difference of their size-four
tall and bush profiles, and the donor rows have no tap on \(e\).

At size six, use the size-six bush and the two trees with
children a leaf and the size-four bush or tall tree. The same
differences are clock-marked, giving \(4C_0\boldsymbol Q\) and
\(-4s^3 C_0\boldsymbol V\). The bush gives degree-five
interpolation error. All six source trees have pure high profile;
no size-six subtree with a size-five child has been used.

The \(p,q\) restriction has exact minor
\[
             Q_p V_q-Q_q V_p=3p q^2(p-q)^2/16\ne0.
\]
One direct calculation uses
\(Q_p=-p^4/36,\ V_p=3p/4,\ Q_q=5p q^3/9-p^2 q^2/3-q^4/4\),
and \(V_q=q^2(9p-6q)/(4p^2)\). The two-dimensional span of
\(\boldsymbol Q,\boldsymbol V\) is invariant under \(C_0\)
only if it is an eigencoordinate plane, since the three
eigenvalues are distinct. The nonzero \(p,q\) minor forces
the plane to omit only \(r\). Therefore if \((Q_r,V_r)\ne(0,0)\),
the original and clock-marked donor vectors together span all
three donor coordinates. Their cubic interpolation fills
\(X\mathcal P_2\), and the two higher-degree bush errors
complete \(X\mathcal P_4\). This gives **exactly** the strong
tests \(X,\ldots,X^5\), from actual rooted order ten.
The [19-adic obstruction](README.md) now excludes the tableau.

## The one real degeneracy and a new narrower necessary chart

If \(Q_r=V_r=0\), the opening row \(r\) is pure through size five.
Its two nonzero-clock possible taps are \(p,q\); the paid moments
then give
\[
               3r^2-4r(p+q)+6pq=0.
\]
This case is not vacuous: \(p=1/3,\ q=5/6,\ r=1\) works
for the pure opening row, with taps \(1/10,1/2,2/5\) on the
origin, \(p\) and \(q\), respectively. No full tableau is
claimed for this local example.

Now the true source space above is exactly
\(X(X-r)\mathcal P_3\): the primitive donor directions fill the
two-dimensional cubic subspace vanishing at \(0,r\), and the
degree-four and degree-five interpolation errors both vanish
at \(r\) and add independent degrees. Thus there is only one
relaxed cubic direction, \(K(f)=\lambda f(r)\) on
\(X\mathcal P_4\). For the six offsite moments this means
\[
          x(x-r)H'(x)\sum_{i:x_i=x} w_i k_i
                       = \alpha x+\beta .
\]
The reason is that weights on six distinct sites annihilating
degree at most three have the two cofactor basis vectors
\(1/H'(x)\) and \(x/H'(x)\). If \(r\) equals one of the **last
three** offsites \(E,F,G\), the affine numerator must vanish
at \(r\). After cancellation it gives the strong cofactor ratios
at all of \(A,T,D\), so the same 19-adic obstruction still
applies. This cancellation makes no assertion about the value
of \(K\) at the coincident site. If \(r\) is distinct from
\(A,T,D\), the remaining early scalar requirement is that the
three values
\[
                  (x-r)\rho(1-x)\mu_{1-x}
                  \qquad (x=A,T,D)
\]
are affine in \(x\) (the common sign from reverse cofactors is
immaterial). This is a linear scalar aperture on \(r\), in
addition to the pure-row equation above. It is not sufficient
for full order; the other ordered reverse-word tests remain.

The rooted reduction here is mathematical. The mod-19 finite
residue arithmetic is separately checked in the referenced
Lean Core module and exact replay.
