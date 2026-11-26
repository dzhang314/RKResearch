# Free output reassignment is necessary for a uniform linear extension cost

Suppose the old stage equations *and their output weights* are fixed. New stages may read all the old rows and each other in any triangular pattern. Even then some old order-\((p-1)\) explicit methods need exponentially many added stages, as a function of \(p\), to reach order \(p\). Allowing a weight change at the first old explicit zero stage does not remove this obstruction.

Work over the real algebraic numbers. Let \(q\ge2\), put \(p\coloneqq3q+1\), and let \(d\) be the number of nonisomorphic rooted trees of size \(q\). The worst case requires at least
\[
                 \left\lceil \frac{(d+1)(d+2)}6\right\rceil
\tag{1}
\]
added stages. This lower bound is for keeping a specified old method fixed, not for the global minimum stage count of order \(p\).

## 1. Producing arbitrary cubic first errors on an actual old tableau

Begin with any ERK of order at least \(p\). For example, unroll the stages of a sufficiently accurate Gaussian collocation method as in the sharp-cost proof, with enough iterations to settle all its order-\(p\) tree columns. Append zero-output strictly explicit rows, without altering this method, so that the old columns \(\mathbf N_u\) for all \(|u|\le q\) are linearly independent. Here is a direct construction of that property. If the columns up to size \(k-1\) are independent, a row reading only the old prefix can prescribe arbitrary values of \(|u|\mathbf a\cdot\mathbf N_u\) for every size-\(\le k-1\) child. On this row a normalized tree up to size \(k\) evaluates as the monomial indexed by its root's child multiset. The monomials are distinct for distinct trees. As functions on an infinite field they are independent, so finitely many literal sample rows make the new matrix of columns independent. Start with the single normalized column \(\mathbf1\) and proceed up to \(q\). The zero output weights on these rows preserve the original order.

In particular the size-\(q\) columns form a basis of the increment of their numerical span modulo smaller tree sizes. Use the weighted polynomial quotient of the append-only first-error theorem on this tableau, with same-clock contrasts and weight \(m\) for an adapted variable of size \(m\). The pure cubic monomials in the size-\(q\) variables have exactly weight \(3q=p-1\). Prescribe an arbitrary linear functional on just this component and zero on every other weight-\((p-1)\) monomial. The finite mixed differences at paid integer points realize it by actual appended rows, altering no rooted test of smaller order. The unit factors \(q\) on each branch can be absorbed into the functional.

Consequently one can realize *any* symmetric cubic discrepancy on all order-\(p\) roots with exactly three size-\(q\) children, on an actual ERK that still pays order \(p-1\). Take a nonzero such discrepancy if exact failure of order \(p\) is wanted. This modified tableau, including these output weights, is the fixed old method for the lower bound.

## 2. Each added row contributes one cubic power

Index the \(d\) rooted trees of size \(q\) by \(u\). In a proposed upgrade, each new stage \(i\) supplies a vector of actual branch values
\[
        \lambda_{i,u}\coloneqq q(A\mathbf N_u)_i .
\]
Its contributions to the triple-child readouts, with repeated children allowed, are the entries of the symmetric cube of this vector multiplied by its output weight. This is true irrespective of the new-to-new coefficients: the coordinatewise rooted-product recurrence holds on every physical stage. None of the old contributions can change. In the ERK first stage all these branch values are zero, so changing just its weight has no effect here.

It follows that the negative of the chosen cubic discrepancy must be a sum of at most \(n\) rank-one symmetric cubic tensors if \(n\) stages are added. A nonzero branch vector in each term may be scaled so that one chosen nonzero coordinate equals one, absorbing the cube of the scale into its output weight. Thus that term has at most \(d\) free coordinates including its weight, with finitely many choices of which coordinate was normalized. Zero terms can be realized by a weight zero. For a given sequence of normalization choices the sum is a polynomial map from \(nd\) variables to
\[
                  D\coloneqq\binom{d+2}{3}
\]
cubic coordinates. If \(nd<D\), its image satisfies a nonzero polynomial relation. One way to see this is to compare the number of formal products of its \(D\) coordinate polynomials of degree at most \(M\) with the dimension of polynomials in \(nd\) variables of the resulting bounded degree, for large \(M\). A linear dependence gives a nonzero polynomial relation in the target coordinates. Multiplying such relations for the finitely many normalization choices gives a nonzero polynomial vanishing on all attainable sums. An infinite field has a cubic outside its zero set. Choosing this as the error in the preceding construction proves (1). The argument uses actual tree coordinates with symmetry, not the dimension of a larger space of arbitrary stage arrays.

For instance the \(20\) six-vertex trees give \(p=19\) and the lower count \(77\) additional stages for some fixed-output old base. There are exponentially many trees even by a direct construction: begin with a four-vertex trunk, and repeatedly adjoin a root with the previous trunk and one of the two distinct three-vertex rooted trees as children. Each step adds four vertices, and the previous trunk is always the unique child larger than three, so the binary choices are recoverable. Adding up to three additional unary roots handles intermediate sizes. The old bases here can themselves be large. The lower bound does not challenge the linear extension theorem, which expressly allows replacing the old output.
