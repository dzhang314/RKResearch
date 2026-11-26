# Graded occupied paths, omitted runs, and exactly paid reconstruction

Mathematical checkpoint, not kernel-checked. Let \(A=\gamma I+B\) be a
triangular RK tableau over a characteristic-zero field, with common actual
diagonal \(\gamma\), \(B\) strictly lower triangular, \(s\) physical stages,
\(c=Ae\), and \(e=1\). Include ERK by taking \(\gamma=0\). The physical
path expansions below do not need common diagonal; the formal paid model
does. The point is a common recovery framework, not a new numeric lower
bound for general SDIRK or DIRK.

## 1. One actual transducer and one formal paid transducer

Fix a hole grade \(h\in\{0,\ldots,s-1\}\) and occupied count \(m=s-h\).
A strict path of \(m-1\) edges is an increasing list
\(v_1<\cdots<v_m\) in \(\{1,\ldots,s\}\), with weight
\[
       w(v)=b_{v_m}\prod_{i=1}^{m-1} B_{v_{i+1},v_i}.
\]
Any list is allowed combinatorially, with weight zero if the physical
support or final output excludes it. Its complete clock word is
\((c_{v_1},\ldots,c_{v_m})\). At occupied position \(i\) the transducer state
is the number \(u=v_i-i\) of holes passed so far. Thus \(0\le u\le h\);
a transition \(u\to u'\) is possible only for \(u'\ge u\), with matrix
entry \(B_{i+1+u',i+u}\). Start state weights are all 1, terminal state
weights are \(b_{m+u}\). A mark at position \(i\) is a diagonal multiplier
\(c_{i+u}^{d_i}\) (or a polynomial in that clock); the state width is at most
\(h+1\), including zero-weight states. This forward product gives
\[
       \sum_v w(v)\prod_i c_{v_i}^{d_i}
        =b^T C^{d_m}B C^{d_{m-1}}\cdots B C^{d_1}e,
             \qquad C=\operatorname{diag}(c).
\]
This is a finite distributive expansion, valid over a commutative
semiring and without invertibility or nonvanishing.

The rooted-order payment of these marks is exactly the upper budget
\[
                            m+\sum_i d_i\le p.                 \tag{1}
\]
Indeed a leaf starts the word; \(A\) adds a unary ancestor and \(C\)
adjoins a leaf to the current root. Expand every \(B=A-\gamma I\).
The exact model sends \(A\) to formal integration
\(J f(y)=\int_0^y f(t)\,dt\), \(B\) to \(T=J-\gamma I\), and \(C\) to
multiplication \(X\) by \(y\). To see this normalization, a tree \(t\)
with tree factorial \(\rho(t)\) has exact stage model
\((|t|/\rho(t))y^{|t|-1}\). Both operations give precisely the new
shape's model, and the final \(\int_0^1\) gives \(1/\rho(t)\).
All polynomial degrees at each step and the final reciprocal integer
are within (1). This part also works over a commutative ring with the
needed integer units. It does not model a differing physical diagonal
as an unmarked scalar.

There is a small formal normal-order recursion complementary to the
physical one. Since \([X,J]=J^2\) and \([X,T]=J^2\),
\[
   X J^uT^v1=(u+1)J^{u+1}T^v1+vJ^{u+2}T^{v-1}1 ,
\]
omitting a term with zero coefficient. Process the word from its first
occupied position toward the output. After \(t\) operators \(T\)
and \(k\) marks \(X\), write the formal state as a combination of
\(J^{k+j}T^{t-j}1\) with \(0\le j\le\min(k,t)\).
A \(T\) leaves \(j\) unchanged and increments \(t\). An \(X\) sends this
state to \(j\) with coefficient \(k+j+1\) and to \(j+1\) with
coefficient \(t-j\), incrementing \(k\). Thus at fixed total number
\(d\) of marks the exact outputs require at most \(d+1\) scalar atoms
\(\int_0^1 J^{d+j}T^{m-1-j}1\). No extra clock marks or stage count are
inferred from these formal states.

## 2. Exact determinant for arbitrary signed path weights

Let \(\alpha=(\alpha_1,\ldots,\alpha_m)\) record the holes immediately
before each occupied slot: \(v_i=i+\sum_{j\le i}\alpha_j\).
Precisely the vectors in \(\mathbb N^m\) with \(|\alpha|\le h\) occur;
the trailing holes number \(h-|\alpha|\). Denote the resulting clock
point by \(Y(\alpha)\). There are
\(\binom{m+h}{h}=\binom{s}{h}\) points counted with physical indices,
and as many monomials of total degree at most \(h\).

Order these multi-indices lexicographically and define a Newton
polynomial of degree \(|\alpha|\) by
\[
 N_\alpha(Y)=\prod_{i=1}^m\prod_{d=0}^{\alpha_i-1}
                 \left(Y_i-c_{i+\sum_{j<i}\alpha_j+d}\right).
 \tag{2}
\]
Its leading monomial is \(Y^\alpha\); the change of basis from
monomials is unit triangular, since all other exponent vectors are
componentwise smaller. At an earlier point \(Y(\beta)\), the first
index \(i\) where \(\beta_i<\alpha_i\) and previous indices agree gives
a zero factor in (2). At its own point the factors are the clock
differences
\[
       c_{i+\sum_{j\le i}\alpha_j}
                 -c_{i+\sum_{j<i}\alpha_j+d}.
\]
Consequently the determinant of the square degree-\(h\)
point-by-monomial matrix, in these identical lex orders, is exactly
\[
    \prod_{|\alpha|\le h}\prod_{i=1}^m\prod_{d<\alpha_i}
       \left(c_{i+\sum_{j\le i}\alpha_j}
                      -c_{i+\sum_{j<i}\alpha_j+d}\right).
 \tag{3}
\]
Every difference is between distinct physical indices in one local
window \(\{i,\ldots,i+h\}\). Conversely, for every \(r<t\) with
\(t-r\le h\) set \(i=\min(r,m)\) and choose
\(\alpha_i=t-i\) with all other coordinates zero. The factor for
\(d=r-i\) exhibits this pair in (3).

Thus over a field arbitrary signed weights on all candidate paths
of this fixed length are identified by the degree-\(h\) mark bank
if and only if no two physical clock indices at distance at most
\(h\) coincide. Over a ring a unit version is obtained when all
these differences are units. The failure with repeated clocks is
exact, not just a missing determinant trick. If \(c_r=c_t\) with
\(0<t-r\le h\), choose \(m-1\) common retained stages outside
\([r,t]\); enough exist since \(s-(t-r+1)\ge m-1\).
Insert \(r\) or \(t\) in the remaining slot. The two distinct
physically indexed candidate paths have the identical clock word,
so no polynomial marks of any degree separate their arbitrary
weights. This does not assert that both weights are nonzero in a
given tableau or that they can be varied independently in one
actual matrix.

At \(p=s\) the degree \(h\) bank is exactly paid by (1).
If \(s=p+r\) with \(r>0\), at most degree \(d=h-r\) is paid at
hole grade \(h\). When \(0\le d<h\),
\(\binom{m+d}{d}<\binom{m+h}{h}\), so no arbitrary signed inverse
can follow from this paid bank alone, even with distinct clocks.
This dimension statement does not apply to weights with their
actual multiplicative constraints, which we use next.

## 3. Multiplicative actual run model

Assume the physical longest product
\[
               L=b_s\prod_{i=2}^s a_i\ne0,\qquad a_i=B_{i,i-1}.
\]
This is the cyclic branch. It is an actual support condition and,
when \(p<s\), is not a paid tall value merely by definition.
Write \(w_H\) for the actual weight when the omitted set is \(H\),
and \(w_\varnothing=L\). If \(I\) is a contiguous interval of
holes and not the whole stage set, put \(\theta_I=w_I/L\).
Then for every omitted set with at least one retained stage,
\[
                    \frac{w_H}{L}
               =\prod_{I\in\operatorname{Runs}(H)}\theta_I ,
 \tag{4}
\]
where the runs are the maximal contiguous intervals of \(H\).
For an interior run \(\{u+1,\ldots,v-1\}\) the factor replaces
\(a_{u+1},\ldots,a_v\) by the actual strict entry \(B_{v,u}\).
At the initial run it drops the leading adjacent factors;
at a terminal run it drops the trailing adjacent factors and
changes \(b_s\) to the new last weight. These modifications of
the full product use disjoint edge sets and commute. A shared
retained vertex is harmless. This proves (4) without dividing
by any individual interval weight, which may be zero.

Equivalently one can put virtual endpoints at 0 and \(s+1\):
a transition from retained \(u\) to retained \(v\) is normalized
by \(\prod_{j=u+1}^v a_j\), and the beginning and ending factors
are the matching interval weights. Adjacent gaps have normalized
weight one. The state in Section 1 records the degree of each
hole run; the width \(h+1\) is for a fixed grade, not a bound
on the requisite number of physical stages.

## 4. First marks already propagate the actual interval coefficients

Fix \(h\ge1\). Assume every interval weight of smaller length is
known. All disconnected sets of \(h\) holes then have known weight
by (4). Subtract their contributions from the total and the
first-mark moment at each occupied slot. Let the resulting
residual total be \(W\), residual slot moment \(M_i\), and let
\(\zeta_j\) be the remaining unknown weight of the contiguous run
starting at \(j\), \(1\le j\le m+1\). At slot \(i\), this run gives
clock \(c_i\) when \(j>i\) and \(c_{i+h}\) when \(j\le i\). Hence
\[
       \sum_{j=1}^{m+1}\zeta_j=W,\qquad
       (c_{i+h}-c_i)\sum_{j\le i}\zeta_j=M_i-c_i W
                             \quad(1\le i\le m).              \tag{5}
\]
This is the one-hole cumulative triangular recurrence reused at
every grade. It requires only \(c_{i+h}\ne c_i\), not distinctness
of the intermediate clocks within that window. Differences of
the cumulative values, together with \(W\), recover all newly
contiguous intervals. Higher marks then supply compatibility
constraints, not new interval degrees of freedom at this grade.

There is also an exact repeat diagnosis after the shorter
intervals have been fixed. If some \(c_{i+h}=c_i\), equation (5)
imposes the corresponding residual equality, with no information
on that cumulative weight. The length-\(h\) contiguous runs
starting at \(i\) and \(i+1\) have identical clock words. More
generally starts \(j<k\) have identical clock words precisely
when all those gaps from \(i=j\) through \(k-1\) vanish.
Thus the connected-run test rank, over a field, is exactly
\((m+1)-\#\{i:c_{i+h}=c_i\}\), already attained by total and first
marks. Arbitrarily many higher marks in this same band cannot
separate that split. Later grades may couple the hidden weights,
so no general failure of full-tableau identification is asserted
from a single band.

The paid inputs of (5) are explicit. Write
\[
 \lambda_j=\sum_{u=0}^j\binom ju\frac{(-\gamma)^{j-u}}{(u+1)!}.
\]
The raw total is \(\lambda_{m-1}\); for slot \(i\) the raw
first moment is
\[
 \lambda_m+\gamma\lambda_{m-1}
       +(i-1)(\lambda_m+2\gamma\lambda_{m-1}
                                        +\gamma^2\lambda_{m-2}).
\]
The last term is omitted when \(i=1\). This follows from the
formal one-mark recursion (or moving one \(X\) past \(i-1\)
copies of \(T\)). The total needs \(m\le p\); the first
moments need \(m+1\le p\).

For a cyclic \(s=p+r\) tableau with \(p\ge2,\ r\ge0\), the exact
seed frontier is now clear. Grades \(h<r\) are unpaid, grade \(r\)
has total only, and from \(h=r+1\) onward the first marks are paid.
Take the actual \(L\) and the interval weights of lengths
\(1,\ldots,r\) as seeds, imposing the total \(\lambda_{p-1}\)
at grade \(r\). At \(r=0\) this means \(L=\lambda_{s-1}\) and
there are no extra seeds. For \(r>0\) there are at most
\(\sum_{j=1}^r(s-j+1)\) interval seeds besides \(L\), with that
one total check. If all clocks at index distance greater than
\(r\) are different, (5) propagates every longer interval.
Short-distance clock repeats among the seed grades do not
prevent this propagation. In particular \(s=p+1\) leaves only
the longest product and the one-hole weights as seeds, with
total already prescribed; no independent higher-hole path
weight has to be introduced.

## 5. Recovery of the actual tableau and a finite frontier

All interval weights and the cyclic \(L\) recover the literal
coefficients, including inactive output rows. Let
\(P_1=1,\ P_v=\prod_{i=2}^v a_i\).
For every \(v\ge2\), the initial hole interval gives
\(w_{\{1,\ldots,v-1\}}=L/P_v\), so this nonzero interval
determines \(P_v\). For \(u<v\) the internal interval gives
\[
        B_{v,u}=\frac{P_v}{P_u}\frac{w_{\{u+1,\ldots,v-1\}}}{L},
\]
with ratio one for the empty hole interval. The terminal intervals
give \(b_u=w_{\{u+1,\ldots,s\}}/P_u\), including \(u=s\) by the
empty interval. The physical diagonal is the prescribed \(\gamma\).
Any candidate obtained by this inverse must pass its actual
row sums \(Ae=c\), and the as-yet-unused order conditions.
Conversely, if the reconstructed coefficients have these row sums
and nonzero leading interval weights, the recovered run factors
are exactly the candidate factors; they realize the generated
total/first-mark equations. This is not a converse for full RKOC.

In particular a cyclic \(p=s\) tableau with globally distinct
clocks is determined by \((\gamma,c)\) from the paid totals and
first marks alone. In the separately proved nondegenerate
rectangle branch at \(p=s\ge8\) these clocks must be
\(c_i=\gamma+(i-1)\alpha\) with \(\alpha\ne0\), and \(\gamma\)
must be a root of the nonzero polynomial of degree at most
\(6s-18\); the paid step equation has degree at most two and
is not identically zero in that branch. Thus over an algebraic
closure there are at most \(12s-36\) full ordered tableaux
in that nondegenerate cyclic branch. Each lies over the field
generated by its diagonal and step. This is a finite candidate
reduction, not attainment, and it leaves the degenerate clock
branch separate.

## 6. Why this is not yet the next stage lower bound

The transducer provides one unified exact system and a short
seed frontier in the next-stage cyclic case. It does not show
that all seeds fail, cover a noncyclic tableau, or resolve a
collision in a required grade. Dimension loss for arbitrary
path weights is not evidence of incompatibility of actual
factorized weights. There is also an exact obstruction to
turning full clock-word agreement into full rooted order in
general.

Indeed start with an active strict-support sink \(t\), with two
strictly earlier donor clocks different. Replace it by two
same-clock sinks with equal split weights \(b_t/2\) and inherited
diagonals. Compare identical strict rows on the two sinks with
rows differing from that old row by \(+z\) and \(-z\) respectively,
where the strict donor row vector \(z\) has \(ze=0\) and
\(zc\ne0\). No other row changes or uses either sink. All actual
clocks and weights agree between these two tableaux. Every
scalar \(B,C\) path word, of any length and mark degree, has the
same output: a path using a twin uses it only as its terminal
occurrence, and its final incoming factor is linear in the
modified row. The identical clocks and equal weights cancel
the two changes (with no change at zero hops). But the rooted
order-five tree with two children \([\bullet]\), i.e.
\([[\bullet],[\bullet]]\), has stage value \((Ac)^2\).
Its output changes by \(b_t(zc)^2\ne0\) after the symmetric
split. Thus these can have the same entire word data at the
same stage count and different genuine rooted order.

Such order-\(p\) bases exist over \(\mathbb Q\) for every \(p\):
use a block union of \(p\) distinct equal-step Euler marches of
sizes \(n_i\ge3\), with rational Euler-extrapolation weights.
For an Euler march of \(n\) stages, the tree output is \(n^{-|t|}\)
times the number of assignments of its vertices to \(n\) ordered
levels with every child strictly earlier than its parent. Group
by the number of distinct levels to see this count is a polynomial
in \(n\) with zero constant term; its top coefficient is
\(1/\rho(t)\) because the rooted poset has \(|t|!/\rho(t)\)
linear extensions (induction by shuffling the child subtrees).
Thus the output is polynomial in \(1/n\) of degree at most
\(|t|-1\) with constant \(1/\rho(t)\). Lagrange extrapolation to
\(1/n=0\) gives order through \(p\), and each nonzero-node
Lagrange weight is nonzero. The last stage in a block is active
and a sink, with two distinct earlier clocks. Applying the split
for \(p\ge5\) compares a genuine order-\(p\) tableau with one
failing that fork, without changing any clock-word outputs.
This example is not cyclic or globally clock-distinct after
the split; it separates the general logical sufficiency of
clock words from the cyclic recovery results above.

## Exact recovery after grouping repeated clock words

Choose the lexicographically first \(\alpha\) among physical realizations of each distinct complete clock tuple. Each representative has a nonzero Newton diagonal: a zero factor would mean that, immediately before its occupied stage \(v_i\), a skipped index \(r\) lies after \(v_{i-1}\) and has the same clock (use \(v_0=0\)). Replacing \(v_i\) by \(r\) leaves a valid increasing list and the same clock tuple, but decreases its first differing hole coordinate. This contradicts minimality. Restrict both the Newton columns and evaluation rows to these representatives; the same triangularity now gives invertibility over the field. The general degree-\(h\) bank therefore already separates the masses *summed over each complete clock-word class*. Its rank is exactly the number of distinct complete clock words, and its kernel is precisely the arrays whose sum in every such class is zero. Neither the full quotient result nor the original pair obstruction asserts independent variation within the nonlinear RK-compatible weight arrays.
