# One genuinely dirty high row: exact failure of a late weighted partner

The real-algebraic ERK10 interval remains **14–15**. This conditional obstruction allows one extra dirty high row in the five-opening, four-Lobatto-pair chart. It is not a lower bound for unrestricted tableaux. It identifies a global chronological condition that the authentic Stepanov order of the two initially zero-weight high rows cannot satisfy. The independent differentiated rooted replay is a local diagnostic, not the argument for global exclusion.

## Hypotheses

The first five physical rows are the canonical two-clean-donor opening with clocks $0,e,2p/3,p,q$, as in the [exact order-nine control](../erk10-stepanov-five-opening/README.md); $e,p,q\ne0$, $p\ne q$. The nine high rows have four interior Lobatto pairs followed by the unique endpoint 1. All are locally pure through derivative size five except an individual designated high row $d$ at some interior clock $x_d$, which is pure through derivative size four and **genuinely not** through size five. Its actual high output weight is zero; output elsewhere is supported on the origin and high rows. The clock $x_d$ is distinct from $p,q$.

The dirty row may read the rough third opening stage (whose actual derivatives through size three are pure). Clean high rows must kill the actual pure quadratic and its unary descendant, hence cannot read rough stages two or three. The dirty row's local size-four purity also prohibits a tap on rough stage two. All high rows may have arbitrary causal taps on earlier high rows. No high co-order, literal $D(1)$, fixed high coefficients, or sign on individual weights is assumed. The scalar moments imply the usual nonzero aggregate Lobatto masses.

## Exact pointwise tests at the dirty row

For each true output order $n$ write
$$
 \mathbf d_j=\mathbf b C^j A-\mathbf b(I-C^{j+1})/(j+1).
$$
The actual rooted order implies $\mathbf d_j\boldsymbol\Phi_t=0$ whenever $|t|+j+1\le n$, by comparison of a unary parent with $j$ marks and its marked polynomial scalar form. Multiplying $\boldsymbol\Phi_t$ by an extra clock costs one leaf at that same root.

The actual rank-two pure size-five columns can be taken as
$$
 \mathbf q_3=A\mathbf c^3-\mathbf c^4/4,\qquad
 \mathbf v=A^2(A\mathbf c-\mathbf c^2/2).
$$
Subtract earlier pure columns supported at rough rows two and three so their remaining support is $p,q,d$; this does not change the values at those three coordinates. On the first two columns of that support the two pure tests are independent, with the actual donor determinant from the earlier packet. At $d$, one of the two tested components is nonzero if the row is genuinely dirty: $\mathbf q_3$ detects failure of its true cubic primitive and $\mathbf v$ detects a tap on the rough stage-three pure column. Every other possible size-five pure high failure at that row is a combination of the same two directions: its lower inputs are pure and its only possible erroneous child has size four, so its outer root is unary.

For $n\ge9$, it follows that $\mathbf d_1(d)=0$ if the row is genuinely dirty. Indeed attach $0,1,2$ leaves to both actual pure profiles; the separated clocks $p,q,x_d$ give a three-by-three Vandermonde, forcing $\mathbf d_1$ times the individual two pure responses to vanish at each coordinate. This is the exact local zero/nonzero gate. The published order-nine 14-row control has $\mathbf d_1(d)\ne0$ at either normally zero-weight early high row (nonzero residues at independent coefficient-field reductions). No sufficiently small perturbation in this architecture can make one of those rows genuinely dirty while retaining **exact** order nine: the nonzero row coefficient is continuous and stays nonzero near that control.

For $n=10$ the same argument applies also to $\mathbf d_0,\mathbf d_2$. For $\mathbf d_3$ only one extra mark is available, but the two pure tests already have a one-dimensional kernel on the three coordinates. A nonzero kernel vector has nonzero dirty component and at least one nonzero donor component: the first two vectors of donor values are independent and the dirty vector is nonzero. If one mark also brought it back into that kernel line, it would be a clock eigenvector with at least two distinct supported clocks, impossible. Thus exact order ten necessarily gives
$$
                            d_{j,d}=0,\qquad j=0,1,2,3.
$$

## Actual early-null source and the weighted partner

The actual early-null model through derivative size five on the first five rows is all of $X\mathcal P_3$. To see it, the first five actual coordinates have four independent pure directions: the quadratic and its unary descendant at rough rows two and three, and the two size-five donor directions on $p,q$. Their joint image with all five model coefficients therefore has dimension at least nine. The polynomial image of the physical kernel has dimension at least four and is restricted only by vanishing at the origin. This proves equality by dimension. The required hypothesis for the proof is the **literal** five-opening data, not a formal list of polynomial moment equations.

For such an actual early-null combination with model $H$, its high vector is a tilted evaluation
$$
                      E H+\mathbf e_d\psi(H).
$$
At clean high rows this is the nominal evaluation. The extra value at $d$ is well-defined as a linear functional $\psi$: the two old size-five pure donor values are fixed by $H(p),H(q)$ (the actual old vector is zero), and those two independent donor values determine the corresponding two error coefficients at the dirty row. Earlier pure directions at rough rows two and three do not change those two coefficients after subtracting them as above. Successive clocks and unary contexts preserve zero early physical data, so through such actual contexts the suffix acts strictly by its high block $B$.

For each $0\le j\le3$, take the context of a unary attachment with $j$ root leaves. It has length $j+1$ and fits with size five inside order ten. Its numerical read on the tilted source borrows no extra defect: the coefficient of the dirty coordinate is
$$
               \mathbf b_H C^j B\mathbf e_d=d_{j,d}=0
$$
because the individual dirty output weight is zero. The nominal clock relation and integration by parts thus show that the high $\mathbf d_j$ annihilates $E(X\mathcal P_3)$. Evaluating that four-dimensional space on five distinct nonzero high sites has an annihilator line with nonzero terminal coordinate. The terminal coordinate of every $\mathbf d_j$ is already zero, since the last column of $B$ is zero and its clock is 1. Therefore the aggregate $\mathbf d_j$ is zero at every high site, **derived from ordinary order rather than imposed**.

The dirty clock's only other occurrence is a **weighted** partner, since its aggregate Lobatto mass is nonzero. All its coefficients $d_{j,d'}$, $j=0,\ldots,3$, are therefore individually zero. Writing $a=x_d$, its strict column must supply quadrature of degree at least three for integration from $a$ to 1 using only **later nonzero-weight physical rows**. The terminal 1 is the only available endpoint. If the set of distinct later contributing sites consists of at most two, with the other at $y$, the polynomial
$$
                            (X-y)^2(1-X)
$$
vanishes on that support but has strictly positive integral on $[a,1]$. Algebraically, with $h=1-a>0$ and $s=(y-a)/h$, the integral is
$$
                     h^4\bigl(\tfrac12(s-\tfrac13)^2+\tfrac1{36}\bigr)>0.
$$
With only the terminal the same test works. Thus its later weighted partner needs **three distinct later contributing clocks** at a minimum. In the published original chronology, the first zero-weight clock $\theta_4$ has its weighted partner followed only by $\theta_5,1$, and the next zero-weight clock $\theta_5$ has its partner followed only by 1. Neither can be the genuinely dirty row of an exact order-ten tableau in this chart.

## Why the coefficient-zero condition is not literal disconnection

The moment conditions at the dirty column alone do not make its physical outgoing taps zero. If five distinct high sites are available *after* the dirty row and a second preceding high helper, one may send actual weighted tap totals proportional to $1/F'(y_i)$ over those five sites, where $F$ is their monic hull. This annihilates degrees 0–3 but has nonzero degree-four moment. Divide each required total by the nonzero actual receiver share to emit one physical tap per later site. A compensating tap from a different earlier high column, with coefficient ratio $-P(x_d)/P(x_{\rm helper})$ where $P=X(X-p)(X-q)$, preserves the clean rows' cubic condition, and their lower moments are repaired by their actual opening taps. This is a causal column possibility respecting the lower scalar moments, not a claimed ordinary order-ten solution. The weighted partner chronology is the reason the original arrangement fails, not an unsupported deletion argument.

## Local differentiated replay

The exact finite-field replay forms the actual order equations through nine and the clean cubic gates at the authenticated order-nine control. It differentiates only the fixed-clock high taps, the two actual donor clocks, the optional rough feed into each nominated dirty stage, and permitted pair mass splits. It is not unconstrained least squares. At both tested independent coefficient-field reductions it verifies that every prior equation is zero, and that no first-order perturbation preserving them can cancel all current size-ten errors in the fixed-split one-dirty chart. Specifically the full correction matrix has 39 variable columns and its augmented residue rank is 40. The nonzero determinant of a square augmented minor transfers to characteristic zero; this rules out that **affine linearized correction**, not a finite or distant nonlinear branch. The derivative-rank columns and their variants with two dirty rows or varying split are recorded as small-prime diagnostics; the exact no-genuine-dirty-nearby proof above does not rely on them.

    sha256sum -c sources.sha256
    OPENBLAS_NUM_THREADS=1 python3 check.py

The replay uses NumPy for exact bounded-integer modular matrix arithmetic, SymPy for finding good primes, and the authenticated public coefficient file from the neighboring packet. The order-nine control is unchanged. A differently reordered high pair with its weighted partner early enough, a mixed dirty support or cut, or another opening/mesh remains outside this proof.
