# Six canonical opening rows, one singleton, and an actual rational size-six port

This packet gives two results. First, it supplies a rational seven-row ERK block whose last physical stage is locally pure through derivative size six. Second, it excludes a different, specified fourteen-stage ERK10 chart: **six canonical opening rows and eight strong-local-four high rows with one singleton interior Lobatto site**. The latter proof *forces* literal $D(1)$ where needed; it does not assume any co-order conditions. Neither result is an unrestricted stage lower bound or an improvement to the 14–15 interval.

## Hypotheses of the fourteen-stage exclusion

- Work in characteristic zero over the real algebraic field (or an extension with the same scalar data). $A$ is strictly lower triangular, with actual $\boldsymbol c=A\mathbf1$.
- The first six chronological clocks are $0,e,2p/3,p,q,r$, with $e,p,q,r\ne0$ and distinct $0,p,q,r$. Stage two uses the origin, and stage three is the usual exact affine-integral row on $0,e$. The three clean donor rows at $p,q,r$ have pure derivatives through size four; the first reads $0,2p/3$, the second may also read $p$, and the third may also read $q$. None of these reads stage two.
- The eight later rows are each locally pure through derivative size five. Their seven interior occurrences are three same-site Lobatto pairs and one singleton; the unique high clock 1 is last. Output is supported on the origin and high rows. Arbitrary real signed high splits are allowed, including zero individual shares.
- No $D(1)$, no full reverse co-order, no fixed high coefficients, and no prescribed pair chronology are assumed. Local size-five purity makes all high incoming columns at the two rough opening rows zero: test the actual pure quadratic difference at stage two and then its actual unary descendant at stage three. Thus their opening feed is on $0,p,q,r$.

The six scalar sites have uniquely determined, nonzero Lobatto masses if order ten holds, by exact clock moments. We use only this quadrature, not a Stepanov high tableau.

## 1. The independently useful rational local size-six port

Scale the desired seventh physical stage clock to 1. Choose rational $p,q$ with
$$
                   10pq-5p-5q+3=0
$$
and the third donor at $r=1$. Put $a=2p/3$. Its own stage-order-three row may feed its preceding donor $q$ with a single strict coefficient $f$. The affine dependence of the actual stage-three incoming coefficient at this row is
$$
 \ell_r=\ell_r^0+f\,q(q-p)/(a(p-a)),
 \qquad \ell_x^0=3x^2(3p-2x)/(4p^2).
$$
The next pure cubic primitive defect at that row is
$$
 q_{3,r}=q_{3,r}^0+f q(q-a)(q-p),\qquad
 q_{3,x}^0=-x^4/4+(p+a)x^3/3-pa x^2/2.
$$
These formulas are direct consequences of exactness on $1,X,X^2$ of the three donor rows.

Take the four-node interpolatory weights on $0,p,q,r$ for integration to 1. The next degree-four scalar condition is affine in $r$, giving
$$
 r=\frac{20pq-15p-15q+12}{5(6pq-4p-4q+3)}
$$
when its denominator is nonzero. Two actual pure size-five donor directions also have to vanish under the new row: the inherited stage-three pure direction read by $\ell$, and $q_3$. Eliminating the single $f$ from these two weighted equalities gives the exact compatibility factor
$$
 -\frac{3q(p-q)(10pq-5p-5q+3)}{40p^2}.
$$
The replay verifies the factor as a rational-function identity, together with the nonzero denominators in the stated example. On the simple displayed branch the affine scalar rule has $r=1$, and the first pure equality defines the literal $f$. The second follows exactly. There are no other size-five donor errors: at these clean stage-three rows a size-five non-unary root is already pure, and a unary root can inherit only the scalar cubic mismatch or the stage-three pure input. Thus all primitives through size five are paid. The seventh stage is an actual incoming row at that clock, not a virtual mean.

For example with $p=3/10,q=3/4,e=1/10$, the strict seventh row is
$$
                          (5/54,0,0,250/567,32/81,1/14).
$$
The literal first six rows are in the fixture. Their six-stage output has exact ordinary order five; the tall sixth value is $1/800$, not $1/720$. Appending that output as an evaluated stage gives all 37 exact derivative profiles through size six at clock 1. The next local grade fails. This is an early-stage ingredient, not a fourteen-stage order-ten method. Any nonzero clock rescales the entire seven-row block.

## 2. True early-null forward source and the possible exceptional covectors

The canonical six-row opening has pure rank four through derivative size five. The quadratic defect has nonzero support at stage two, its primitive descendant at stage three is independent, and on the clean donors the two size-five pure directions above are independent already on $p,q$, with determinant $-3pq^2(p-q)^2/16$ up to a nonzero multiplier. There can be no further pure donor direction at that grading by the actual root decomposition just used.

Let $\ell$ be the nonzero covector on the three clean donor values killing the two independent pure directions. View it as a linear functional on polynomials by evaluation at $p,q,r$. The actual early-null model space through size five is exactly
$$
              U=\{f\in X\mathcal P_3:\ell(f)=0\}.
$$
For proof, take the joint image of ordinary tree combinations in their physical six coordinates and their polynomial models. Projection to the five-dimensional polynomial space is onto by bushes and its kernel has dimension four by the actual pure rank. Thus the model image of the kernel of the physical map has dimension at least three. Its model has zero origin value and its values on $p,q,r$ are annihilated by $\ell$, giving the opposite bound. This is an image of actual **early-null combinations**, not merely the discrepancy of a chosen decoder.

Usually $U+XU$ is all of $X\mathcal P_4$. If it is proper, a nonzero functional $F$ on that five-dimensional space satisfies $F|_{X\mathcal P_3}=\alpha\ell$ and $F(X\cdot)|_{X\mathcal P_3}=\beta\ell$. With $l_j=\ell(X^j)$ this entails $\alpha l_{j+1}=\beta l_j$ for $j=1,2,3$. The possibilities with $\alpha=0$ or $\beta=0$ require either the first or last three $l_j$ to vanish, impossible for a nonzero combination of the three distinct nonzero evaluations. Otherwise the sequence is geometric, so $\ell$ is proportional to one nonzero point evaluation on $X\mathcal P_3$. Since $\ell(X(X-p)(X-q)(X-r))=0$, its point is one of $p,q,r$. Independence of the pure directions on $p,q$ rules out those two. Thus the only exception is $\ell=E_r$, namely the actual third donor is already pointwise pure through size five.

## 3. Ordinary order forces the shorter high co-order

Every early-null source from $U$ has actual high derivative vector $E f$ because those rows are pointwise pure through size five. Any outer unary or same-root leaf mark preserves its zero physical opening vector, since the opening is closed. A same-root mark costs one and gives the actual pure high vector $E(Xf)$. Hence ordinary order ten tests every actual high adjoint word of length at most four on both $U$ and $XU$. Scalar integration by parts gives its nominal density, and precision nine applies throughout the degree budget.

Consequently through length four the raw reverse site sums are exact if $U+XU=X\mathcal P_4$: evaluation on the five nonzero high sites is invertible. Even for $\ell=E_r$ with $r$ not an interior quadrature site they are exact. If $r$ is off mesh, the four-dimensional evaluation space of $X(X-r)\mathcal P_3$ has an annihilator line with nonzero coordinate at the endpoint 1; this follows from distinct sites and the invertible Vandermonde after multiplying by the nonzero node factors. But every actual and model word already agrees at the final endpoint: after a primitive the final physical column is zero, as is $J^*f(1)$, and further marks preserve zero. Thus the possible line error vanishes. If $r=1$, evaluate only at the four interiors and use exactness at the endpoint again.

In these cases the high restrictions of $\mathbf d_0,\ldots,\mathbf d_3$ have exact aggregate zero, for
$$
 \mathbf d_j=\mathbf b C^jA-\mathbf b(I-C^{j+1})/(j+1).
$$
Inside the high block $B$, the resulting paired row differences have highest-word constraints too: $\mathbf d_0 C^k B$ for $k=0,1,2$ and $\mathbf d_1 C^k B$ for $k=0,1$ have zero site sums. The remaining $\mathbf d_1 C^2 B$ and $\mathbf d_4$ annihilate $E U$ by testing length five on the unmarked size-five sources. To verify these in order, append a primitive to the known error word $\mathbf d_0 C^k$ or $\mathbf d_1 C^k$ and subtract the nominal coefficient contributions of the already paid $\mathbf d_j$. The length-five word with four initial clock marks is exactly the $\mathbf d_4$ test.

It follows that on $X\mathcal P_3$ the normalized required site means of $B$ have the form
$$
                          G_y(f)=(Jf)(y)+\omega_y L(f).
$$
Here $\omega_y=1/(W_y F'(y))$, with $W_y$ the nonzero site mass and $F$ the five-site high hull, up to a common normalization. Indeed the first four output-clock moments leave just this Vandermonde line; the fifth on $U$ makes $L|_U=0$, so $L$ is a scalar multiple of $\ell$. The endpoint/origin conventions cause no extra terms, because $f(0)=Jf(0)=0$.

## 4. Forced literal D(1), then the singleton contradiction

Let $I_t$ be the cardinal at interior $t$ of $X\mathcal P_3$ on the four interior nodes. The twelve ordered cross-diagonal gates
$$
 W_s F'(s)(J I_t)(s)-W_t F'(t)(J I_t)(t)\ne0
 \qquad(s\ne t)
$$
hold exactly. Their nonzero reductions mod 227 are checked in the independent replay. A **singleton** row at $s$ equals its mean $G_s$ on the polynomial inputs. If any earlier member at a different paired clock $t$ also equals its own full mean $G_t$, whichever of it and the singleton occurs first cannot read the other's value. The later of them cannot read its own clock, since it is a singleton or the first occurrence of its pair. Thus both rows have zero actual coefficient in the same column (the later clock's cardinal). This would violate the displayed ratio gate. This argument is independent of branch signs or whether a later share vanishes.

The high $\mathbf d_0$ is supported on at most the three opposite pair differences. The first three marked actions $\mathbf d_0 C^kB$ are exact on the full space $X\mathcal P_3$ as proved above. Vandermonde isolates every active pair difference, so any active earlier member would equal its mean; the singleton cycle makes this impossible. Thus the high $\mathbf d_0=0$ literally. The full opening part is supported at $0,p,q,r$ and killed by the four true bush moments, so **full literal $D(1)$ is forced**. In particular the last nonzero interior share before the endpoint yields $\mathbf d_1$ coefficient $b_i(1-c_i)^2/2\ne0$: any later zero shares do not enter either output. Therefore there is at least one active high $\mathbf d_1$ pair.

If at most two pairs are active for $\mathbf d_1$, its first two marked primitive actions isolate each active pair difference on all $X\mathcal P_3$. An active earlier member again equals its full mean, impossible with the singleton. If all three are active, the first three marked primitive actions isolate the differences on $U$. Every pair's earlier member, and the singleton, must then act as $J$ on $U$ because $L|_U=0$. Consider the first two **distinct** actual high clocks $x,y$. Before the first there is no high input, so $U=\ker(E_xJ)$ inside $X\mathcal P_3$. Before the first occurrence at $y$ the only high clock is $x$. The allowed input
$$
 f(X)=X(X-x)(X-x/2)
$$
vanishes at $x$ and belongs to $U$, but $(Jf)(y)=y^2(y-x)^2/4\ne0$. This contradiction treats all three active pairs even if some individual split is zero.

## 5. The remaining on-mesh exception

If $\ell=E_r$ and $r$ is a quadrature interior, the marked early-null test forces the shorter raw rows to be exact at the other four high sites. The opening row at $r$ is itself genuinely locally pure through size five. Reclassify it as the first high row (still with zero output weight), leaving the canonical five-opening block. The true clock moments of $\mathbf d_j$, $j=0,1,2,3$, combine its coefficient at $r$ with the only possibly nonzero old high site aggregate at that clock. Their remaining support lies at $0,p,q,r$; the first four actual bush reads force these aggregate coefficients to vanish. Every high aggregate is therefore now exact as in the [five-opening reordered proof](../erk10-stepanov-reordered-coorder/README.md).

If $r$ was at a paired clock, there is still a singleton among the four interiors and it cannot provide the resulting exact mean on $X\mathcal P_3$ with just its three possible other interior predecessors (the sixty support gates in that packet). If $r$ was the original singleton, there are now four pairs. In this reclassified case the literal $\mathbf d_0=0$ is again forced without an assumption: $\mathbf d_0 C^k A$ for $k=0,1,2,3$ annihilate all size-five trees by true order ten, so the two independent pure donor vectors and the bushes make their high restrictions annihilate $X\mathcal P_3$. The four clock marks isolate every active $\mathbf d_0$ pair, so its earlier row would equal its already exact full site mean; this is impossible by the support hull gate. The low $\mathbf d_0$ vanishes by interpolation. Now the previously proved pair-order-independent contradiction applies on the reclassified four pairs. This finishes the six-opening chart.

## Reproduction and native scope

    sha256sum -c sources.sha256
    python3 port.py /tmp/rational-local-port.json
    cmp port.json /tmp/rational-local-port.json
    python3 high_diag.py
    python3 solve_port.py

The rational replay and cross-diagonal arithmetic use only Python's standard library; the independent symbolic family check uses SymPy. The Core arithmetic module checks all twelve cross-diagonal residues on the four tested Lean releases. The native rational-port module proves the reviewed six-stage $HasOrder\,5$, the exact failed sixth tall, and every seventh-stage derivative through size six. The high chronological classification and characteristic-zero transfer are mathematical proofs, not native all-tableau theorems.

See the [typed native audit](../../lean/evidence/erk10-six-opening-port-20261127/README.md) for the closed rational port proofs and their axiom checks.
