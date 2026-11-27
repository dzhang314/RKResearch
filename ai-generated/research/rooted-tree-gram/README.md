# An integer Gram certificate for ordinary Runge–Kutta order

This provides an alternate exact verifier for the repository's **reviewed**
`FiniteRootedTree` and `HasOrder`. It neither lowers a stage minimum by
itself nor changes the coefficient class. It avoids enumerating trees in the
numeric checker, although its soundness proof expands the moment matrix
conceptually as a sum over every ordered tree presentation.

Write a rational tableau as $A=M/d$ and $\boldsymbol{b}=\boldsymbol{w}/e$.
For a rooted tree $t$ with $n$ vertices, write $F(t)$ for the product of
the factorials of the root's subtrees, so that $t!=nF(t)$. Set
$$
\boldsymbol{g}_t=\bigl(F(t)\boldsymbol{\Phi}_t(M),\,d^{n-1}\bigr),
\qquad
\boldsymbol{\ell}_n=(n\boldsymbol{w},-e).
$$
The scalar $\boldsymbol{\ell}_n^\top\boldsymbol{g}_t$ is the
denominator-cleared integer defect. When $u$ is attached as an additional
subtree at the root of $t$, the feature obeys
$$
\boldsymbol{g}_{t\triangleleft u}
  =\boldsymbol{g}_t\odot(B_{|u|}\boldsymbol{g}_u),
\qquad B_j=\operatorname{diag}(jM,d).
$$
Here $\odot$ denotes componentwise multiplication. The one-vertex
feature is $\boldsymbol{1}$. Define the Gram matrix
$C_n=\sum_{|t|=n}\boldsymbol{g}_t\boldsymbol{g}_t^\top$ on the
reviewed ordered tree presentations. The constructor splits each
presentation into two earlier trees. Bilinearity gives
$$
C_1=\boldsymbol{1}\boldsymbol{1}^\top,\qquad
C_n=\sum_{\substack{r+j=n\\ r,j\ge1}}
   C_r\odot(B_j C_j B_j^\top).
$$
Thus $\boldsymbol{\ell}_n^\top C_n\boldsymbol{\ell}_n$ is a sum of
squares of the individual cleared defects. It is zero exactly when
every size-$n$ defect is zero. The argument takes place over the
integers, before coefficient transport, and makes no sign assumption
on the weights of the RK method.

Since $B_j=J_j B_1$ for $J_j=\operatorname{diag}(jI,1)$, cache
$B_1 C_j B_1^\top$ once per grade and reweight its entries for each split.
Through order $p$ with $m=s+1$ augmented coordinates, the dense cost
is $O(pm^3+p^2m^2)$ integer operations and $O(pm^2)$ stored integers.
These are arithmetic-operation counts, not constant-bit runtime
guarantees. The implementation exploits symmetry and zeros in $B_1$.

## Lean and exact replay

`RKResearch.Certified.RootedTreeGram.Trace.paid` gives the reusable
integer soundness theorem. `Trace.hasOrder` and
`FactoredTrace.hasOrder` recover the repository's usual order
predicate over any commutative ring where the two integer tableau
scales map to units. The latter variant also permits substantial content
compression of the intermediate Gram matrices. For each compressed
covariance, it verifies the two matrix products, the multiplier
identities, the grade split and the diagonal quadratic energy. All
multipliers are eliminated by multiplication and distribution in the
proof, not by canceling nonzero factors. Its direct Lean 4.36.0 axiom
audit lists only `propext`, `Classical.choice`, and `Quot.sound`.

Run this standard-library replay from the repository root:

```sh
python3 ai-generated/research/rooted-tree-gram/check_gram.py \
  ai-generated/research/fixed-one-newton/tableau-9.json \
  ai-generated/research/fixed-one-newton/tableau-11.json
```

It independently obtains zero energies at orders 1–9 and 1–11 for the
18- and 26-stage strict SDIRK fixtures, respectively. The next-bush
failure and lower-triangular shape are checked by the other fixture's
`check.py`. The Gram script checks order at least the indicated order,
not exact order on its own.

To produce a standalone finite Lean arithmetic certificate, use:

```sh
python3 ai-generated/research/rooted-tree-gram/gen_lean.py \
  ai-generated/research/fixed-one-newton/tableau-9.json --graded > Certificate9.lean
```

After building `RKCert.ReviewedNative.RootedTreeGram` and its pinned
dependencies in the repository's normal project namespace, compile
the generated Lean file in that same environment. The Python script
provides only candidate integer tables and ordinary Lean source. It
does not provide an oracle, a native computation axiom, or a weakened
order predicate. The Lean theorem is a strict-SDIRK rational exact-order
existence statement with all ordinary rooted equations and the first
unpaid bush. The order-eleven source is generated the same way.
