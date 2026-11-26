# Six-row paid fork fans: a one-seed branching check on short middle cuts

Let \(A=\gamma I+B\) be a
common-diagonal triangular RK tableau over a characteristic-zero
field, \(B\) strictly lower triangular, with \(s=p+1\) physical
stages and order at least \(p\), \(p\ge5\).
The paid identities below apply in the nonzero-diagonal
determinant-root chart, including orders 18--20, without any
minimum length of a middle clock run and without any assumption
that determinant roots or actual clocks are distinct.
Physical cyclicity, when used, is stated separately.
No value is given to an unpaid tall moment.

The local test has a genuine order-five fork, shifted by
paid unary legs. It gives ten linear readout equations and
one quadratic equation in a six-site cut. With physical
cyclicity, all the branch vectors in these tests depend
on one global scalar seed, \(d_3\), and each square gives
a degree-at-most-two eliminant in that seed. This is a
necessary compatibility theorem; it does not claim to
exclude all determinant-root candidates.

## 1. Local fork and the exact paid fan

Use \(e=1,\ c=Ae\), and write the componentwise order-two
stage defect as
\[
                         d=Ac-\tfrac12 c^{\odot2}.
 \tag{1}
\]
Here the superscript denotes a componentwise power.
For the rooted convention
\(\Phi(\bullet)=e,\ \Phi([t_1,\ldots,t_j])=
\prod_k A\Phi(t_k)\),
\(Ac=\Phi([[\bullet]])\) and \(c^{\odot2}=
\Phi([\bullet,\bullet])\) both have rooted order three.
The exact stage model of a rooted tree \(t\) is
\((|t|/\rho(t))\,x^{|t|-1}\), with \(\rho\) the tree
factorial. The two summands in (1) have the same model
\(x^2/2\), so \(d\) has exact model zero.
A componentwise product of stage factors merges their
roots; sizes combine as \(|t|+|u|-1\), and the exact
stage models multiply, by the same factorial formula.
Multiplying by \(c^j\) appends \(j\) leaves to the
common root. Expanding \(B=A-\gamma I\) uses unary lifts
and fixed scalar factors. Thus a mark involving \(d\)
has stage degree two, and a mark involving \(d^{\odot2}\)
has degree four. In the latter, the \((Ac)^{\odot2}\)
term is the genuine rooted fork \([[\bullet],[\bullet]]\).

Choose nonnegative \(r,\ell\) with \(r+\ell=p-5\).
Define actual two-sided path weights
\[
   w_i^{uv}=(b^TB^{r+u})_i\, (B^{\ell+v}e)_i,
                                \qquad u,v\ge0,\quad u+v\le2 .
\]
Their support lies in the physical interval
\[
       I_{uv}=[\ell+v+1,\ s-r-u]\subseteq
                 I=[\ell+1,\ell+6].
 \tag{2}
\]
Indeed the two factors vanish outside their strict prefix
and suffix ranges. No assertion of nonzero weights at
every site in those ranges is needed.
The following tests are exact:
\[
 \boxed{\quad
   \sum_{i\in I} w_i^{uv} c_i^a d_i=0
                  \quad(u,v\ge0,\ u+v\le2,\ 0\le a\le2-u-v),
       \qquad
   \sum_{i\in I} w_i^{00} d_i^2=0 .
             \quad}                                          \tag{3}
\]
There are three base linear rows, four with one extra hop,
and three with two extra hops. The total order of a linear
test is at most
\[
   (r+u)+(\ell+v)+1+a+2=p-2+u+v+a\le p .
\]
For the square it is \(r+\ell+1+4=p\).
These are literal ordinary rooted conditions:
the \(B^{\ell+v}e\) factor is a root-merged tall stage
polynomial, and the outside \(B^{r+u}\) is a linear combination
of unary lifts. In particular a linear test at a middle cut
may itself merge two non-leaf children; it need not be
mistaken for a decorated single spine.
The exact model is zero because it contains the zero model
of \(d\). This proves (3) without assuming positivity of
weights, invertibility of \(B\), or a shape of the cut clocks.

Every consecutive physical block of at most six indices is
contained in a window (2) for some \(0\le\ell\le p-5\),
since its possible window starts are \(1,\ldots,s-5\).
Thus a short portion of the determinant-root middle recurrence
can be tested, even if the window also touches a boundary
clock or includes a repeat. The proof does not need the
long-middle conclusion available only at larger orders.

## 2. Exact rank and square obstructions on an actual cut

Let \(R_I\) be the \(10\)-by-\(6\) actual readout matrix of
the linear rows in (3), with columns indexed by \(I\).
Let \(W_I=\operatorname{diag}(w_i^{00})\) on those columns.
Then the actual defect row restricted to \(I\) satisfies
\[
                    d_I\in\ker R_I,\qquad d_I^T W_I d_I=0.
 \tag{4}
\]
This includes repeated clocks and zero weights literally.
If \(R_I\) has rank six, \(d_I=0\).
If it has rank five, any nonzero \(d_I\) forces the
unique kernel line to be isotropic for \(W_I\).
For example choose five independent rows and let \(z_i\)
be the signed \(5\)-by-\(5\) column deletion minors.
They form a nonzero kernel vector, so a nonzero defect
requires \(\sum_i w_i^{00} z_i^2=0\).
This is a genuine polynomial restriction on the literal
cut data in the rank-five case, not an interpolation step.
At the initial cut \(I=[1,6]\) and \(\gamma\ne0\),
\(d_1=\gamma^2/2\ne0\); hence rank six is impossible
there outright, and at rank five the displayed isotropy
and \(z_1\ne0\) are mandatory. At other cuts a nonzero
defect must be known or tested; it is not automatic.

There is a second sign-free small-support test.
Let \(J\subseteq I\) be the actual nonzero support of \(w^{00}\)
and let
\[
   G=(m_{a+b})_{0\le a,b\le2},\qquad
                    m_j=\sum_{i\in I} w_i^{00}c_i^j .
\]
If \(G\) is nonsingular, the three polynomial probes
\(1,c,c^2\) on \(J\) span a nondegenerate subspace of
the active diagonal form \(W\).
The base three linear equations in (3) and the square
put \(d|_J\) in that subspace's orthogonal complement
as an isotropic vector.
If \(|J|\le4\) the complement is zero or is a nondegenerate
line, so \(d|_J=0\) over any characteristic-zero field.
If \(|J|=5\) and \(d|_J\ne0\), the two-dimensional
complement must be isotropic. Its determinant is
\((\prod_{i\in J}w_i^{00})/\det G\) modulo nonzero squares,
since the active form splits as the two orthogonal summands.
Thus the necessary square-class condition is
\[
             -\frac{\prod_{i\in J}w_i^{00}}{\det G}
                            \text{ is a nonzero square}.     \tag{5}
\]
Over an ordered field it in particular must be positive.
The argument does not assume an order on the coefficient
field, a sign pattern on the weights, or a nonzero defect at
an inactive row. If \(\gamma\ne0,\ \ell=0\), and \(w_1^{00}\ne0\),
then \(d|_J\ne0\) automatically and these are actual support
restrictions.

## 3. One global seed from the physical cyclic reverse flag

Now assume true physical cyclicity:
\(b_s\ne0\) and \(a_j=B_{j,j-1}\ne0\) for all \(2\le j\le s\).
Write \(L_h=b^TB^h\) for the actual row (not an unpaid scalar).
It is supported in columns \(\le s-h\) and its entry at column
\(s-h\) is
\[
          (L_h)_{s-h}=b_s\prod_{j=s-h+1}^s a_j\ne0.
\]
The unique contributing path for that entry uses the entire
adjacent suffix, by strict chronology.
Paid unary shifts of (1) give
\[
                      L_h d=0,\qquad 0\le h\le p-3=s-4.
\]
Thus all actual \(d_k\), \(k\ge4\), are determined
by the first three:
\[
         d_k=-\frac{\sum_{i<k}(L_{s-k})_i d_i}
                              {(L_{s-k})_k},\qquad 4\le k\le s.
 \tag{6}
\]
This is reverse triangular elimination through the actual
nonzero adjacent pivots. It does not use an unpaid
normalization for \(b^TB^{s-1}e\).

The first two values are fixed by the clocks and diagonal,
and the third by a short local row. Put \(x_i=c_i-\gamma\).
Since \(Ac=\gamma^2e+2\gamma x+Bx\), one has
\[
 d_1=\gamma^2/2,\qquad
 d_2=\gamma^2/2+\gamma x_2-x_2^2/2,\qquad
 d_3=\gamma^2/2+\gamma x_3-x_3^2/2+B_{32}x_2 .
 \tag{7}
\]
In particular under physical cyclicity the genuine
defect need not be recomputed independently on six middle
rows. Form the two arrays \(u,v\) by the homogeneous
recursion (6), with starting triples
\((d_1,d_2,0)\) and \((0,0,1)\). Then every actual
defect vector is
\[
                            d=u+t v,\qquad t=d_3 .
 \tag{8}
\]

This makes the exact cut test a one-seed eliminant,
not a search over independent local branch values.
For each fan row \(R_j\) define \(A_j=R_j u\),
\(B_j=R_j v\), restricting the arrays to its cut.
For the genuine square at cut \(I\), let
\[
    Q_{I,0}=u_I^T W_I u_I,\quad
    Q_{I,1}=u_I^T W_I v_I,\quad
    Q_{I,2}=v_I^T W_I v_I .
\]
All cuts must obey the same scalar
\[
          A_j+t B_j=0,\qquad
          Q_{I,0}+2Q_{I,1}t+Q_{I,2}t^2=0,                 \tag{9}
\]
with the actual (7). If any \(B_j\ne0\), elimination
against that row gives the division-free compatibility
equations
\[
  A_k B_j-A_j B_k=0,\qquad
  Q_{I,0}B_j^2-2 Q_{I,1}A_j B_j+Q_{I,2}A_j^2=0,
\]
for the other chosen linear rows and squares.
If all \(B_j=0\), all \(A_j\) must vanish and the
remaining quadratics must still share the same actual
seed \(t\); an arbitrary root over a larger field
is not enough for a coefficient-field claim.
A candidate for which (4) forces \(d_I=0\) must
likewise have the restrictions of \(u+t v\) zero
there; if their two columns are independent on
that window, no seed can achieve it.

This test can be used on any short part of the middle
clock/skip recurrence: first get its actual stage
weights (or leave them as literal symbolic cut data),
then apply (6)--(9) on a covering window.
In the determinant-root middle the known clock
defect recurrence gives the adjacent gaps and the
corresponding centered cut formula gives \(\sigma_i\);
where a gap is nonzero this also gives
\(U_i/L=\sigma_i/g_i\) and hence the corresponding
normalized singleton skip factors.
If a candidate is supplied by the earlier one-mark
run inverse, (9) is an additional low-branching
compatibility check on that very candidate. If the
inverse is unavailable due to repeats, (3), (4) and
(9) still apply to its actual cut weights without
clock inversion. Nothing here infers an affine or
geometric shape on an unresolved short interval.

## 4. Pure paid weight data and a small Gram diagnostic

The same windows have explicit scalar clock moments.
For the subcut \(I_{uv}\) set \(N=6-u-v\),
\(h=r+u+\ell+v\), and \(q=\ell+v\).
For all \(0\le j\le N-2=4-u-v\), its paid
univariate moments are
\[
 \begin{aligned}
  m^{uv}_j
      &=\sum_i w_i^{uv} c_i^j
        =\mathcal I(T^{r+u}X^j T^{q}1)\\
      &=j!\sum_{a=0}^j
        \frac{\binom ja}{a!}(q)_{\underline a}
                    \mathcal I(J^{j+a}T^{h-a}1).
 \end{aligned}                                               \tag{10}
\]
Here \(J\) is formal integration from 0, \(X\) is multiplication
by the variable, \(T=J-\gamma I\), and \(\mathcal I\) is formal
integration from 0 to 1; a zero falling-factorial term is
omitted. The coefficients follow from
\(X J^b T^v1=(b+1)J^{b+1}T^v1+v J^{b+2}T^{v-1}1\).
One can equivalently iterate this two-term identity.
The highest scalar tall index in (10) is \(h+j\le p-1\).
No formal high-order or unpaid scalar enters.

If the \(N\) clocks in a subcut are distinct, these \(N-1\)
moments give the entire subcut weight row up to one scalar.
Explicitly the null direction has coordinates
\[
          \beta_i=\bigg(\prod_{\substack{j\in I_{uv}\\j\ne i}}
                                      (c_i-c_j)\bigg)^{-1}.
\]
This follows from Lagrange interpolation of degree at most
\(N-2\). Equivalently choose the value of the next
(unpaid on that cut) clock moment as a single actual seed.
The branching constraints remain (3) or (9) after this
projection. This optional inverse is not needed when weights
are known, and has no claimed uniqueness with repeated clocks.

For the base \(u=v=0\) let \(G(\ell)=(m^{00}_{a+b})_{a,b=0}^2\).
For \(p\ge9\), (10) extends the entries polynomially in
\(\ell\) with degree at most \(a+b\) and nonnegative formal
integration powers. The determinant has degree at most six.
Furthermore it is symmetric under \(\ell\mapsto p-5-\ell\):
formal adjoint and reflection on \([0,1]\) exchange the two
\(T\) legs and replace the middle clock \(x\) by \(1-x\).
Concretely \(J^\ast f(x)=\int_x^1 f(t)\,dt\) under
\(\mathcal I(fg)\); reflection conjugates \(J^\ast\) to \(J\).
Each moment has degree at most four. The adjoint identity holds at all
paid integer positions, at least five for p >= 9, so it holds as a polynomial
identity before taking the determinant.
The reflection is an invertible triangular basis change on
\(1,x,x^2\) with determinant of square one, so it preserves
the Gram determinant. Thus \(\det G(\ell)\) is a polynomial
of degree at most three in \(\ell(p-5-\ell)\).
If nonzero as a polynomial for a prescribed coefficient
field and diagonal, it leaves at most six exceptional cut
positions for the nondegeneracy assumption in (5).
We do not assume or claim that this polynomial is nonzero
at every scalar determinant root. The literal fan and
one-seed obstruction do not need that assumption.

The new square condition checks a rooted fork, not a
consequence asserted from equality of all scalar clock
words. Conversely passing these local tests does not
certify higher branching or full order.
There is no per-root enumeration, no long middle run
hypothesis, no use of unpaid scalar coefficients, and
no claimed blanket stage exclusion.
