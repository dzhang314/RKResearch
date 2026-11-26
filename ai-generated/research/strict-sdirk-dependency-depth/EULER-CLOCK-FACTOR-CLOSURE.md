# Closing the early fixed-clock Euler edit escape

Pure mathematics, over a real characteristic-zero coefficient field,
with a common nonzero diagonal gamma. The hypotheses below concern
a retained chronological Euler skeleton, with some altered physical
rows at the old fixed clocks. They do not bound unrestricted SDIRK,
and do not assume positive b. Exact supported vectors and paid
tree-context rank give the stage count; there is no parameter search.

## 1. The actual defect and its clock factors

Let A be a lower-triangular common-diagonal table, c=A1, M=diag(c).
Take s labelled old slots, in increasing chronological order, whose
clocks are c_i=gamma(i+1), i=0,...,s-1. An unedited slot has the
nominal strict Euler row: coefficient gamma on each earlier slot
and zero on any other stage. An edit can change those coefficients
but not that slot's clock. Output weights can all change.

Put
    D0=c^2-2Ac+gamma c,                                           (1)
where c^2 is pointwise. This is a tree-profile expression of grade
at most 3. Its exact output polynomial is gamma*x: the grade-three
profiles c^2 and Ac correspond to x^2 and x^2/2. On an unedited slot
it is exactly zero, even if earlier rows were edited, because c
on its predecessors was retained. Directly,
( Ac )_i=gamma^2[(i+1)+i(i+1)/2], so c_i^2-2(Ac)_i=-gamma c_i.

Let S be a predecessor-closed physical set containing the retained
slots. In the closed-prefix application take S to be exactly
those slots. With interleaving, take their predecessor closure.
Let Z be the **distinct** clocks of those rows in S where D0
is nonzero. It is also valid to take a larger known set of actual
clocks and annihilate it. Let epsilon be 1 if Z contains 0, and 0
otherwise. Let P(x)=product_{z in Z,z!=0}(x-z), with d=deg P,
and set u=1+epsilon, b0=3+epsilon, r=b0+d. The actual vector
    D = gamma^(-1) product_{z in Z}(M-z Id) D0                       (2)
is zero on S, has grade at most r, and has exact polynomial
x^u P(x). There is no extra sign penalty for its simple interior
roots, as shown next. In particular this multiplication uses the
*clock* of the edited slot, not a fitted root chosen from the RK
residual: it is an exact physical annihilator there.

## 2. Integrated remainders at distinct real roots

Write J f(x)=integral_0^x f(t)dt. For j=0,...,d-1, divide the
polynomial J(x^(u+j) P(x))/x^u by P, with quotient Q_j and
remainder R_j of degree <d. The division by x^u is literal:
the primitive is divisible by x^(u+1). The actual supported
carrier
    E_j=A M^j D-Q_j(M)D                                             (3)
has exact model x^u R_j and grade at most r+j+1, since
deg Q_j=j+1. Support is preserved by A and M on the coordinate
space of vectors zero on S, precisely because S is closed.

The d remainders are independent. In a relation let L be the
polynomial of degree <d with its coefficients on the E_j.
Evaluating the putative zero remainder at every nonzero root z
of P says
    integral_0^z t^u P(t)L(t)dt=0.
This primitive is also zero at 0. Sort all d roots together with
0. Subtract consecutive values. The integrals are now zero on
d disjoint open intervals between successive endpoints. The
weight t^u P(t) has nonzero fixed sign on each such interval,
because all its real roots are endpoints or beyond the interval.
A nonzero real L must consequently have a distinct root in
each interval, impossible at degree <d. This proves independence
for arbitrary signs and sizes of the roots, including roots
outside [0,1]; no Gaussian or special-root exceptions occur.
For d=0, there are no remainders and P=1.

Thus all polynomial residues of degree <d are represented by
supported carriers at grade <=r+d. Higher polynomial factors
are represented by division by P: for Q of degree m,
the quotient times D has grade at most r+m-d if it is present,
and the remainder has grade <=r+d. Its exact model is x^u Q.
Only field operations on actual clock values and rational
integrations are involved; no extension of the input coefficient
field is needed.

## 3. Paid staircase rank and the exact deficit count

For clarity, normalized stage tree profiles have exact model
    Phi_t -> |t| x^(|t|-1)/t!,
whose integral is the normalized RK order condition b^T Phi_t=1/t!.
M corresponds to multiplying by x (attach a leaf at the root),
and A to J (add a unary root). These rules are on formal profile
expressions, not on the quotient by actual stage-vector equalities.
Define Pi=M A-A M-A^2. Its exact model is zero (xJ-Jx=J^2),
and its diagonal is -gamma^2, hence it is invertible on the
supported coordinate subspace W of vectors zero on S.

At each level l take independent factors Q of degree <=2l
represented by supported expressions V_l(Q) of grade <=p-2l
and exact model x^u Q(x). Then all columns Pi^l V_l(Q) are
independent. In a relation let l0 be the first occupied block,
invert its common left Pi^l0 on the actual vectors, and apply
b^T Q_l0(M), where Q_l0 is the polynomial of that block. This
is paid: each term has grade at most
    (p-2l)+2(l-l0)+2l0 = p.
The higher-l terms all have zero target and the first contributes
integral_0^1 x^u Q_l0(x)^2 dx>0. This is impossible. No formula
for an inverse in the exact polynomial model has been used.

Now put n=p-b0 and assume p>=max(b0,4d+1+epsilon). At each
l=0,...,floor(n/2) write q=n-2l. The unpenalized dimensions
would be 1+min(2l,q).

* If q>=2d, all residues are available within p-2l, and so
  are all needed multiples of P. Thus use the entire factor
  space of degree <=min(2l,q).
* If 0<=q<d, use no block; the carrier itself is too costly.
* If d<=q<2d, use the q-d+1 multiples of P and the first q-d
  independent remainders in (3). Their degrees are all <=q.

In the last two cases 2l>=q because n>=4d-2 and q<=2d-1;
thus the left tests add no further restriction. The deficits
from full block dimension q+1, as q traverses 0,...,2d-1,
are
    1,2,...,d,d,...,2,1.
Only q of the parity of n are counted. Reflection
q -> 2d-1-q keeps the entries and switches parity, so the total
deficit is exactly d(d+1)/2 in either parity. Summing the unpenalized
counts gives
    F(n)=sum_{l=0}^floor(n/2) [1+min(2l,n-2l)]
        =floor(((n+2)^2+4)/8),
by splitting the two progressions at floor(n/4). Hence every
order-p table in this class satisfies
    # stages outside S >= F(p-3-epsilon)-d(d+1)/2.                 (4)
This is the exact dimension of the displayed construction in the
stated paid range, not a claim of an optimal universal rank or
of attainable RK order at the stage lower bound.

A blockwise lower formula is available without p>=4d+1+epsilon.
For each l with G=p-2l>=r, the multiples contribute
    max(0, 1+min(G-r, 2l-d)).
The independent available remainders number k=min(d,G-r).
Their intersection with degree <=2l has dimension at least
    max(0, k-max(0,d-1-2l)).
Add these two numbers over l and apply the same staircase argument.
They are disjoint because the second block is degree <d and the
first is divisible by P. This is useful when a low order budget
cannot afford the complete remainder space.

## 4. Consequences for early edits and few interleaved ancestors

For one fixed-clock edit of a predecessor-closed Euler prefix,
Z is empty or contains just the nonzero edited clock alpha.
In the second case (2) has grade 4 and model x(x-alpha).
In (3) at d=1, the remainder is -alpha^2/6, visibly nonzero.
Thus the simple clock factor followed by one integration provides
the weight-x seed of grade 5; it gains back most of the naive
projection loss from the unmultiplied D0. In either case, with
s>=p and p>=5,
    total stages >= s+F(p-3)-1.
For s=p this exceeds the last verified unrestricted upper at
every p=5,...,20; orders p=3,4 follow from s>=p and achieved
2,3 there. At p20 it is 64 with one actual defect clock, and
65 if no first clock moment changed. The former 56--58 window
concerned this retained edited base and is therefore closed.
The proof applies to arbitrary new late rows and signed reweighting,
not just a response-budget scheme.

For up to t altered fixed-clock rows in a closed prefix, use
d<=t and epsilon=0. At p20 and s=20, (4) gives 65, 64, 62,
59, 55 for t=0,1,2,3,4 respectively (bounds, not witnesses).
Thus a strict improvement over 59 needs at least four actual
distinct edited defect clocks in the closed-prefix architecture.
For t<=3, s>=p the same formula already rules out strict
improvement at each p=15,...,20. The improved one-edit
inequality holds across the entire range as above.

If other stages may appear before the edit, take S to be the old
slots plus all h external strict ancestors of that single edited
slot. This is predecessor-closed: the unedited old rows have no
external inputs, and the ancestors have their own predecessors
included. Then |S|=s+h and d+epsilon<=h+1. The bound (4) instead
counts the stages beyond this larger set. In particular at p20,
s>=20, one obtains
    h=0: >=64,
    h=1: >=63 if no zero defect clock, >=61 allowing zero,
    h=2: >=61 if no zero defect clock, >=60 allowing zero.
For d smaller than the maximal allowed number the bound only
improves; the displayed rooted-clock threshold is satisfied in
all these cases. At p19 the worst lower with h<=2 is 54, so
strict improvement is still excluded. With h=3 the estimate
can be 58 at p20; no claim is made for that escape, higher h,
different clocks on the old slots, or nonconstant increments.
In particular a putative strict improvement with one fixed-clock
edit and interleaving needs at least three external ancestors
of the edited slot. Bare interleaving of unrelated stages cannot
avoid the predecessor-closed argument.

## 5. Rooted-stem, sequential continuation consequence

These are also physical support carriers for the unary-root
demixing operator A-gamma Id on W. For any such carrier K of
grade k with exact polynomial f_K, the paid condition is
    b_W^T ((A-gamma Id)|_W)^l K
      = integral_0^1 (J-gamma id)^l f_K,   l+k<=p.
This is literal unary grafting and scalar subtraction. If the
integral is nonzero, there is a directed path of l strict edges
among stages outside S, not merely l abstract response levels.

In Section 2 choose the degree-zero factor 1 in the full
remainder space (or D itself for d=0). Its supported grade is at
most b0+2d and its exact polynomial is x^u. The right side is
    u! Q_(l,u+1)(gamma),
    Q_(l,a)(gamma)=sum_{j=0}^l binom(l,j)(-gamma)^(l-j)/(j+a)!.
For rational gamma with noninteger reciprocal this cannot
vanish: the reciprocal polynomial obtained by multiplying by
(l+a)!/(-gamma)^l is integral with leading coefficient +/-1.
Thus the highest paid l=p-(b0+2d) forces at least
p-b0-2d+1 sequential stages outside S, whenever this range
is nonnegative.

There is a stronger exact depth check when all d defect clocks
are nominal Euler clocks m_i gamma (m_i positive integers).
Use the original clock-factor carrier D, grade 3+d, rather
than its constant-factor remainder. Write
P(x)=sum_{k=0}^d (-gamma)^(d-k) e_(d-k)(m) x^k, with e elementary
symmetric polynomials. Its demixed integral is
    sum_k (-gamma)^(d-k) e_(d-k)(m) (k+1)! Q_(l,k+2)(gamma).
After setting X=1/gamma and clearing by
(l+d+2)!/(-gamma)^(l+d), this is an integer polynomial in X of
degree l+d and leading coefficient +/- (d+1)!; the k=d term
is unique in the top degree. It is nonzero when X is rational
with reduced denominator not dividing (d+1)!. It is also
strictly positive for negative gamma, since P(x) then has
positive coefficients on [0,1] and J-gamma id is positive
there. In these ranges the largest paid l=p-(3+d) forces
p-2-d sequential outside stages. For the one-edit case this is
p-3 stages, with paid coefficient explicitly
    2 Q_(l,3)(gamma)-alpha Q_(l,2)(gamma).
The width and path lower bounds concern the same continuation;
do not add them. The width bound (4) has no arithmetic
condition on gamma and is what closes the original stage gap.

The width counts require literal fixed old clocks and actual predecessor closure. Interleaved ancestors are counted once. The stronger nominal-clock depth result assumes all defect clocks are nominal and nonzero, and then combines with the width bound by taking their maximum, not their sum.
