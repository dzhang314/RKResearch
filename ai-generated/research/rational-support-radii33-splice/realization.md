# Exact order-20 RK realizations on the 19-site radii/33 support

**Theorem.** The rational scalar rule below has a rational 101-stage
ERK realization and a rational 117-stage strict SDIRK realization
with common diagonal \(1/66\). The ERK realization also gives a DIRK.
Both tableaux have **exact order 20** and preserve all 19 contributing
sites and their positive aggregate weights. Individual output weights
are nonnegative. The all-tree proof is independent of the direct
small-tree replay. These are prescribed-support constructions, not
global stage upper-endpoint improvements or Lean certificates.

## 1. The actual scalar input

The squared radii \(r_i^2\) for
\[
r_i \in \{0,6,11,16,21,25,29,31,32,33\}/33
\]
are ten distinct interpolation nodes. Their radius masses are chosen
by the ten exact moments \(\sum_i M_i r_i^{2j}=1/(2j+1)\) for
\(0\le j\le9\). Splitting \(M_i/2\) at \(x=(1\pm r_i)/2\) for
\(r_i\ne0\), and taking the center mass once, produces the reflection-
symmetric 19-site scalar rule. Centered odd moments vanish by symmetry,
so every ordinary moment through degree 19 is paid. For an exact
positivity check, the ten radius masses have common denominator
`3653911936877887745754262716288960000000` and the following numerators in the displayed order:

```text
338471245288990157134920669623903355900, 629275055153634998912539792747980455936
505121510796019993753242280655037939810, 599795721315289983772306070389772875440
475181365439475166946585645781640214822, 450897552084287974935773021825056206600
395664826536754645490900872479358438968, 40658683176050019008052085652614715649
191809404171316537552799581557365212500, 27036572916068268247142695576230584375
```

Substitution verifies the ten defining moments, and all radius
masses are strictly positive. The first unpaid defect is
\[
 Q(X^{20})-\mathcal I(X^{20})
 =-\frac{46431074773795189}{273343678068076808693733872640}.
\]
This is also the negative integral of the squared-radius nodal
product divided by \(2^{20}\), since all lower terms in
\(X^{20}=(1+Y)^{20}/2^{20}\), \(Y=2X-1\), are paid. The rule includes
both endpoints and the reflected pair \(1/66,65/66\).
It is **not** the [published \(u/128\) rule](../rational-quadrature-four-shift/standalone-19.md),
which is strictly interior and has a different residual.

The splice argument uses no Gaussian property of these nodes:
distinct samples for Lagrange, a positive weight per reverse
cluster, and exact scalar moments are the only grid requirements.
The 19 sites satisfy them and include the chosen diagonal for each
reverse bank.

## 2. Dense cores and the ERK origin

For a true rooted tree \(t\), write \(d_t=|t|-1\) and
\[
 f_t(x)=x^{d_t}/\mathrm{ff}(t),\qquad
 I_xf_t=x^{|t|}/t!.
\]
These are the reviewed normalizations: the forest factorial is the
product of the child factorials, and a stage response is the product
of its actual primitive child columns. At any bank level \(k\),
the selected \(k\) stage values must be their pure \(f_t\) values
for every \(|t|\le k\). Their Lagrange interpolation \(\Pi_k\)
is then exact for that whole tree packet.

Start at the row \((\gamma)\). The leaf and the only order-two
stage response are always \(1,c\). Add the second sample at a
different grid node, with off-diagonal \(x-\gamma\), so the first
two selected rows give the order-two interpolation.
For later levels take new rows with off-diagonal functional
\[
       (I_x-\gamma E_x)\Pi_{k-1}
\]
on the earlier samples, and diagonal \(\gamma\).
For any child tree of size at most \(k-1\), preceding samples
give the pure \(f_t\), and the new diagonal reads the value
proved by induction on that smaller tree. The strict-lower tap and
the diagonal contribution add to \(I_x f_t\). This proves each
new sample has response \(f_T(x)\) for every \(|T|\le k\),
including row sum \(x\). Appending these lower-triangular rows
does not change any earlier response. Neither this step nor the
Lagrange solve divides by \(\gamma\).

**The ERK reuse is exact.** At \(\gamma=0\) the first row is
the literal all-zero row (also after padding by future columns).
There \(\Phi_\bullet=1\); every nonleaf has at least one child and
all its primitive values in that row are zero. Thus every nonleaf
response is zero, equal to \(f_t(0)\). The row is a genuine sample
at **every** tree order, not a hypothetical off-table evaluation.
At level \(k\), keep this row and add just \(k-1\) new nonzero-clock
samples. For \(\gamma=1/66\), the initial two stages supply the level-2
pair and every later level adds \(k\) new samples as above. A strict
order-\(k\) core therefore uses \(k(k+1)/2-1\) rows for \(k\ge2\);
an explicit one uses \(1+k(k-1)/2\). At forward order \(q=10\)
and reverse order \(J=9\), these are sizes \(54,44\) (strict) and
\(46,37\) (ERK).

## 3. Reverse representatives, including the omitted origin

Let \(R\) denote the reverse pure bank and \(\Pi_R\) its
order-\(J\) interpolation. All its stages have their clocks in
the reverse scalar grid. In each cluster at \(y\), distribute its
positive aggregate \(W_y\) evenly among the old rows and one
new representative. Give the representative diagonal \(\gamma\)
and only old-core strict taps. It is chosen to make the
following equality of *linear functionals*, for all reverse
columns \(v\), not just polynomial inputs:
\[
 \sum_{i:c_i=y} w_i (L v)_i
 =
 W_y(I_y-\gamma E_y)\Pi_R(v_R)+
          \gamma\sum_{i:c_i=y}w_i v_i.                       \tag{1}
\]
Explicitly, for the new row \(v_y\) the old-core tap is
\[
 L_{v_y,R}=\frac{W_y(I_y-\gamma E_y)\Pi_R
       -\sum_{i\in R_y} w_i(R_{i,\cdot}-\gamma e_i^T)}
      {w_{v_y}},\qquad L_{v_y,v_y}=\gamma.
\]
Here \(R_y\) is the set of old rows at \(y\) and \(e_i\) is the
coordinate vector in the old bank. There are no
old-to-representative or between-representative strict couplings.
Both sides therefore automatically have zero strict coefficients
in the appended representative columns; the checked identities
on all old-core columns suffice for (1). Substituting \(v=1\)
gives the new row sum \(y\), since \(\Pi_R1=1\).

For ERK \(y=0\), the only existing reverse row at that site is
the origin. Its strict and diagonal row is zero. The right side
of (1) is also the zero functional, because \(I_0=0\) and
\(\gamma=0\). Giving the origin the full \(W_0\) therefore
satisfies (1) identically without a new representative. After
reflection and reindexing this weight is at the **physical
site \(x=1\)**; reversal need not make it a physical zero row.
It is not an off-table derivative, and no weightless reverse
row is introduced. Every weight used in the reverse transpose
remains strictly positive.

A reverse word in \(L\) and multiplication by \(1-y\), applied
to \(1\), has its restriction to \(R\) equal to the corresponding
word in \(R\) and \(1-y\). Applying \(R\) makes a unary root,
and multiplication by \(y=R1\) adds a leaf at the root on actual
tree columns. Multiplication by \(1-y\) is their linear
combination with the unchanged vector. Thus a word of length
\(\ell\le J-1\) on the bank belongs to the actual tree packet
through size \(J\), and \(\Pi_R\) extracts the polynomial
obtained by replacing \(L\) with \(I_y\) and \(1-y\) by scalar
multiplication. Inducting on the full reverse word, (1) now
gives the exact aggregate \(W_y P(y)\) for every word of length
at most \(J\). The added \(L\) step uses \(\ell\le J-1\),
so the required dense interpolation is always paid. The
\(\gamma\)-terms in (1) cancel even for general \(\gamma\),
and at zero they simply disappear.

## 4. Weighted reversal and complete tree proof

Let \(U\) reverse the reverse-stage order, \(D=\operatorname{diag}(w)\)
and \(w_f=Uw\). In forward chronology the suffix matrix and
physical clocks are
\[
       T=U D^{-1}L^T D U,\qquad x=U(1-y).
\]
Each above-diagonal entry of \(T\) comes from an above-diagonal
entry of \(L\), so \(T\) is lower triangular. Its diagonal is
exactly \(\gamma\), including zero. Only the nonzero reverse
shares are inverted. For the bilinear pairing with diagonal
weights \(w_f\), the adjoint of \(T\) is \(ULU\);
clock multiplication is self-adjoint. These are matrix
identities over \(\mathbb Q\) and require no nonzero diagonal
entry of \(L\).

With \(G,\Pi_G\) the forward dense core and \(E\) physical
suffix evaluation, use the actual tableau
\[
  A=\begin{pmatrix}G&0\\(E I-T E)\Pi_G&T\end{pmatrix},
  \qquad b=(0,w_f).
\]
Its suffix row sums are \(x\), since \(\Pi_G1=1\);
reflection preserves \(W_y\) as aggregate weights at \(x=1-y\).
The zeros at \(G\) contribute no new site.

Let \(\rho_t=f_t-\Pi_G\Phi_t^G\) and
\(e_t=\Phi_t^{\rm suffix}-Ef_t\). Then \(\rho_t=0\) for
\(d_t<q\), and otherwise \(\deg\rho_t\le d_t\).
The actual deviation of the primitive child column is
\[
 D_t=T e_t+(T E-E I)\rho_t.
\]
The formula follows by multiplying the displayed block tableau,
not a simplifying assumption. It gives \(e_t=0\) at every
\(d_t\le q\) by tree induction, and \(D_t=0\) whenever \(|t|\le q\).
Consequently at grade \(\le19=q+J<2(q+1)\), no root can have
two children whose erroneous primitive might be nonzero:
their sizes alone would sum to at least \(2(q+1)=22\).
Every other child primitive equals its pure monomial. Expanding
the actual product at a root and recursively replacing any
\(e_t\) in its single-child error yields a sum of terms
\[
      \alpha\, B(T E-E I)\rho_s,
           \qquad d_s\ge q,\quad \ell(B)+d_s+1\le19.        \tag{2}
\]
Here \(B\) is a word in \(T\) and multiplication by \(x\).
The length budget is literal: a parent with siblings of total
size \(a\) multiplies by \(x^a\); continuing to a child error
uses one \(T\). At the final primitive source the child-to-parent
step is the displayed \(+1\), so the length plus source grade
plus one equals the contributing root grade. This justifies
(2) for all actual reviewed trees of the requested order,
including branching ones.

Transpose the output applied to one term of (2) with the
diagonal weight pairing. In reverse order \(B^\dagger1\)
has the exact cluster profile of a polynomial \(P(y)\) of
degree \(\le\ell(B)\le8=J-1\), and the extra adjoint \(T\)
of the first summand becomes \(L\). Its aggregate is \(I_yP\),
paid through length 9. Writing \(S(x)=P(1-x)\) changes this
integral to \(J^*S(x)=\int_x^1 S(z)\,dz\), without a minus
sign. The two contracted terms are the scalar quadratures
of \((J^*S)\rho_s\) and \(S(I\rho_s)\); each has degree
at most \(\ell(B)+d_s+1\le19\). Their exact integrals
coincide, because the integral of the derivative of
\((J^*S)(I\rho_s)\) is zero (one factor vanishes at each
endpoint). Hence every term in (2) has zero output.
The pure output is the paid integral of \(f_t\), exactly \(1/t!\).
This proves all literal tree order conditions through order 20.

The scalar residual at degree 20 is nonzero, so the order-21
bush fails unchanged. All-tree sufficiency and exactness are
therefore independent facts, not an extrapolation from the
85 small-tree tests.

## 5. Exact evidence and limits

| Class | Forward bank | Reverse bank | Appended representatives | Physical rows | Nonzero raw weights | Contributing sites |
|:--|--:|--:|--:|--:|--:|--:|
| Strict SDIRK \(\gamma=1/66\) | 54 | 44 | 19 | 117 | 63 | 19 |
| ERK \(\gamma=0\) | 46 | 37 | 18 | 101 | 55 | 19 |

Run the [deterministic exact replay](replay.js) with `node replay.js`
(BigInt and `Array.prototype.toReversed` required);
see the [expected output](expected-replay.json).
It verifies all 836 strict / 703 explicit reverse strict-tap
identities, 329/285 forward and 239/204 reverse bank row checks,
the literal shapes and aggregate weights, every paid bush and
the next failure, and 85 direct tree tests through order seven
for each tableau. The JSON key `clusters` counts **physical reverse
suffix rows**, not distinct clock clusters; the distinct cluster
count is 19 for both. No order-20 enumeration or Lean certificate
is claimed.

The [generic donor construction](../quadrature-donor-realization/realization.md)
would use 209 physical rows on this support. The smaller counts
here are for these prescribed nodes and weights. They do not
improve the global physical-stage endpoints, establish any
minimum width, change the 17–19 rational contributing-support
interval, or claim the same counts for the \(u/128\) rule.
