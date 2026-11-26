# A six-stage order-five criterion with coefficients in a ring

## Theorem

Let \(R\) be a nonzero commutative unital ring with \(5!\) invertible. An explicit Runge–Kutta tableau on at most six actual stages, satisfying the order conditions through five, exists with the following two restrictions if and only if \(-15\) is a square in \(R\):

1. Its quadratic stage defect is supported on at most one physical coordinate.
2. Every \(4\times4\) minor of a matrix of generators of its pure size-five defect module vanishes.

Such a tableau has six actual stages and has exact order five. Its one defective coordinate is the second. The determinantal restriction refers to the actual matrix over \(R\), not merely to ranks in its residue fields. No ordering, reducedness, domain hypothesis, or restriction to characteristic zero is used. This is a statement about the specified defect stratum, not an unrestricted ordinary stage lower bound.

Put \(\mathbf c\coloneqq A\mathbf1\), let \(C\) be multiplication by \(\mathbf c\), and use the vector \(\mathbf q\coloneqq \mathbf Q([\bullet])/2=A\mathbf c-\mathbf c^{\odot2}/2\) for the quadratic stage residual in the calculations. For each rooted tree \(t\), let \(\gamma_t\) be the product of the factorials of its root branches and put
\[
g_t(X)\coloneqq X^{|t|-1}/\gamma_t,\qquad
\Delta_t\coloneqq\boldsymbol\Phi_t(A)-g_t(\mathbf c).
\]
Define the pure module \(F_k\coloneqq\operatorname{span}_R\{\Delta_t:|t|\le k\}\). It is precisely the actual image of the formal combinations through size \(k\) with zero ideal polynomial: subtract the appropriate multiple of the bush of the same size. This description supplies a finite generating matrix and commutes with specialization. Consequently the minor condition is independent of the generating list, by multilinearity. Also \(AF_k,CF_k\subset F_{k+1}\), by extending a tree and attaching a leaf.

The proof uses the [field classification](ORDER-FIVE-MINIMAL-DEFECT-FIELD-THRESHOLD.md) and its [fifth-row calculation](SINGLE-SECOND-ROW-DEFECT-SIX-LOWER-BOUND.md).

## Necessity

### 1. The pivots are units in the ring

Pass first to any residue field at a maximal ideal of \(R\). Order two guarantees a nonzero clock. The first such clock has nonzero quadratic defect, so the unique possible defective coordinate remains nonzero. The minor hypothesis gives \(\dim F_5\le3\), and chronological no-plateau gives \(\dim F_5\ge3\). The field theorem applies. In every residue field six rows are needed, no row can be deleted, the defective index is two, and the third and fourth clocks are distinct and nonzero. In the normalization \(c_2=1\), let
\[
N\coloneqq c_3,\qquad T\coloneqq c_4,\qquad X\coloneqq c_5,\qquad
D\coloneqq3N-2T,\qquad \mathbf f\coloneqq A\mathbf e_2 .
\]
Indeed the original \(c_2\) is a unit: it is nonzero in every residue field, so the normalization takes place over \(R\). Rescaling \(A\) by a unit multiplies every size-\(k\) derivative column by that unit to the power \(k-1\); it preserves \(F_k\), its minors and the condition on \(\mathbf q\). The exact ordinary terminal scales with the same factor and the weights are unchanged.

In every residue field the field theorem says \(T=2N\), \(X=T\), \(f_5\ne f_4\), and \(c_6\notin\{0,N,T\}\). It also gives \(f_3=N^2/2\), \(f_4=-2N^2\) and \(f_6\ne0\). Thus the following elements are units in \(R\), even before imposing the exact equalities \(T=2N\) and \(X=T\) over the ring:
\[
N,\ T,\ T-N,\ D,\ X,\ X-N,\ f_3,\ f_4,\ f_5-f_4,\quad
c_6,\ c_6-N,\ c_6-T,\ f_6.
\]
Here \(c_6,f_6\) are in the \(c_2=1\) normalization. This use of residues establishes invertibility, not equality of ring elements.

### 2. The pure-column relations hold globally

In the current normalization \(\mathbf q=-\mathbf e_2/2\). The three columns \(\mathbf q,\mathbf f,C\mathbf f\) lie in \(F_5\). Their restriction to coordinates 2, 3 and 4 has unit determinant \(-f_3 f_4(T-N)/2\). Subtract their unique linear combination matching those coordinates from any \(\mathbf z\in F_5\). The result is zero on those three coordinates, and its entry on each other row is zero by the \(4\times4\) minor along that row and the three pivot rows. Hence \(F_5\) is exactly the free span of these three columns.

Set
\[
\mathbf u\coloneqq A\mathbf c^{\odot2}-\mathbf c^{\odot3}/3,
\qquad
\mathbf v\coloneqq A\mathbf c^{\odot3}-\mathbf c^{\odot4}/4 .
\]
Write \(\mathbf u=L\mathbf q+K\mathbf f+\lambda C\mathbf f\). Because \(C\mathbf u\) belongs to \(F_5\), so does \(\lambda(C-NI)(C-TI)\mathbf f\). It is zero on the three pivot coordinates and therefore zero everywhere. Its sixth entry is \(\lambda(c_6-N)(c_6-T)f_6\); all three factors multiplying \(\lambda\) are units. Thus \(\lambda=0\). Comparing rows two and three now gives the actual identities
\[
\mathbf u=\tfrac23\mathbf q+(1-2N/3)\mathbf f,
\qquad
f_4=T^2D/(2N),\qquad
A_{43}=T^2(T-N)/N^2 .
\]
The last two follow from the first two clock powers at the fourth row. Since \(A\mathbf f,\mathbf v\) both belong to the pivot span, their first four coordinates give
\[
A\mathbf f=\alpha(C-NI)\mathbf f,\qquad
\mathbf v=\tfrac12\mathbf q+
 [\,1-N^2/2+\theta(C-NI)\,]\mathbf f,\qquad
\alpha\coloneqq N/D,\quad\theta\coloneqq-\alpha(T-N)/2.
\]
For example the donor cube on the first three coordinates equals \((1+N)\mathbf c^{\odot2}-N\mathbf c\). This gives the cubic entries at rows three and four and hence the displayed coefficients. All denominators here are paid constants or the specified units.

### 3. The delayed equality fails by at most a square-zero element

On the first four donor coordinates the following identities hold by evaluation, even with repeated clock labels:
\[
\begin{aligned}
\mathbf c^{\odot3}
 &= (N+T)\mathbf c^{\odot2}-NT\mathbf c+(1-N)(1-T)\mathbf e_2,\\
\mathbf f
 &= T\mathbf c+U\mathbf c^{\odot2}-(T+U)\mathbf e_2,\qquad
U\coloneqq(N-2T)/(2N).
\end{aligned}
\]
Apply the fifth row to these identities and use its quadratic, cubic and \(\mathbf f\) relations above. With
\[
\begin{aligned}
B&\coloneqq N(2T-N)/6, &
G(Y)&\coloneqq Y^2/4-(N+T)Y/3+NT/2,\\
J(Y)&\coloneqq T/2+(N-2T)Y/(6N),&
L_1(Y)&\coloneqq B-\theta(Y-N),\\
L_2(Y)&\coloneqq\alpha(Y-N)+(N+T)/3 ,
\end{aligned}
\]
the resulting equations are \(L_1(X)f_5=X^2G(X)\), \(L_2(X)f_5=X^2J(X)\). The polynomial identity
\[
L_1(Y)J(Y)-L_2(Y)G(Y)=-\tfrac{\alpha}{4}(Y-N)(Y-T)^2
\]
holds by expansion. Eliminating \(f_5\) without dividing by it, and using the units \(\alpha,X,X-N\), shows
\[
Z^2=0,\qquad Z\coloneqq X-T .
\]
In \(R'\coloneqq R/(Z)\) the first fifth-row equation, now at \(X=T\), becomes
\[
\frac{NT(2N-T)}{6D}(f_5-f_4)=0 .
\]
Thus \(T=2N\) in \(R'\) since the other factors are units. The ideal \((Z)\) of \(R\) is square-zero; this is stronger than the earlier congruences in all residue fields.

### 4. The scalar obstruction and a Newton correction

In \(R'\) now scale \(T\) to one. Write \(a\) for the new second clock, \(x=c_6/T\) for the new sixth clock, and \(\tau\) for the new exact ordinary terminal. The old \(N\) becomes \(1/2\), both fourth and fifth clocks are one, and \(a\) is a unit. Here \(\tau\) is the inverse of the original physical fourth clock before either normalization. In each residue field \(\tau=x\) by the field theorem, and \(x,1-x,2x-1\) are nonzero. Consequently \(\tau,1-\tau,x,1-x,2x-1\) are units in \(R'\).

In these units the same cubic subtraction gives \(f_6=x^2(1-x)/a\), because \(x-1\) is a unit. The three rows of the annihilator of \(F_5\) are the origin, the mixed true endpoint combining rows four and five with weights of sum one that kill \(\mathbf f\), and
\[
\mathcal R\coloneqq E_6-\beta E_3-\gamma E_4,\qquad
\beta\coloneqq16x^2(1-x)^2,\qquad
\gamma\coloneqq2x^2(1-x)(1-2x).
\]
They are a basis over the ring: a linear read annihilating the three pivot columns is determined by its entries on coordinates 1, 5 and 6; these three reads give a unit triangular set on those entries, since the mixed endpoint coefficient at row five is \(-f_4/(f_5-f_4)\), a unit. Their scalar model is evaluation at 0, evaluation at 1, and \(P(x)-\beta P(1/2)-\gamma P(1)\). There is no need to infer these assertions from a field dimension.

Write \(v=2Y-1\), \(d=2x-1\) and take the two model polynomials
\[
H\coloneqq(1-v^2)(v^2-\tfrac45 dv-\tfrac15),\qquad
S\coloneqq\tfrac32(1-v^2)(1-dv).
\]
Both vanish under these three model reads, by evaluation. The ordinary output therefore annihilates them and agrees, on degree at most four, with \(\tau^{-1}\int_0^\tau\). The lower primitive of \(H\) at \(\tau\) is \((d-(2\tau-1))(1-(2\tau-1)^2)^2/10\). Since \(\tau,1-\tau\) are units, its vanishing implies \(\tau=x\) in \(R'\). The primitive of \(S\) at \(x\) is \((d+1)^3(3d^2-9d+8)/16\); because \(x\) is a unit, \(3d^2-9d+8=0\) in \(R'\). Thus \((6d-9)^2+15=0\) there.

Define \(\delta_0\in R\) by this same expression \(6(2c_6/T-1)-9\) before taking the quotient, and put \(e\coloneqq\delta_0^2+15\). Then \(e\in(Z)\), so \(e^2=0\). Also \(\delta_0\) is a unit because its square is the unit \(-15\) plus a square-zero element. The explicit correction
\[
\delta\coloneqq\delta_0-\frac{e}{2\delta_0}
\]
satisfies \(\delta^2+15=e-e+e^2/(4\delta_0^2)=0\) in \(R\). No completeness or division by a possibly nonunit discriminant was used.

## Sufficiency and exactness

Given a square root \(\delta\in R\) of \(-15\), put \(x=(15+\delta)/12\) and use the six literal rows and weights in the [explicit witness](EXPLICIT-FIELD-WITNESSES.md). These are unambiguous formulas from the paid base algebra \(\mathbb Z[1/5!,\delta]/(\delta^2+15)\). If \(\bar x=(15-\delta)/12\), the products \(x\bar x\), \((1-x)(1-\bar x)\), and \((2x-1)(2\bar x-1)\) are respectively \(5/3,1/6,8/3\); hence all divisions in the literal formulas and the terminal rescaling are by units. The fifth raw coordinate is itself the true endpoint because \(f_5=0\) in this witness.

For a direct rooted verification across rings, the witness has \(\mathbf q=-a^2\mathbf e_2/2\), \(\mathbf u=(2a/3)\mathbf q+(a^2-a/3)\mathbf f\), \(\mathbf v=(a^2/2)\mathbf q+[a^3+(a/4)(C-I)]\mathbf f\), and \(A\mathbf f=(I/2-C)\mathbf f\), where \(a=1/4\) in the pre-scaled rows. Its \(\mathbf q\) is supported on one coordinate. A unary root at size five contributes the fourth primitive defect \(\mathbf v\) and \(AF_4\). A multibranch root contributes \(CF_4\), multiples of \(\mathbf q\) or its coordinatewise square, or zero: the partition with two size-two children is \((\mathbf c^{\odot2}/2+\mathbf q)^{\odot2}\). The corresponding size-four contributions lie in \(\operatorname{span}(\mathbf q,\mathbf f)\). Thus every pure size-five defect is in \(\operatorname{span}(\mathbf q,\mathbf f,C\mathbf f)\), which has the same unit pivot on coordinates 2, 3 and 4. The required minors vanish.

The three exact normalized model reads have common kernel generated by \(H,S\) over the paid base: subtracting an \(H\) multiple removes the quartic term by its unit leading coefficient; an endpoint-zero cubic \((1-v^2)(b+c v)\) is killed by the mixed read exactly when \(c=-bd\), since \((1-d^2)d\) is a unit. The normalized integral \(x^{-1}I_x\) kills \(H,S\) by the displayed primitive formulas and \(\delta^2=-15\). The weights in the explicit witness reproduce it on the three remaining model reads. Thus they satisfy all rooted order-five equations after scaling the terminal to one. If order six held after a nonzero base change, it would hold in a residue field. The cross-order floor forces five independent pure directions through size six with one defective coordinate, filling the five non-origin entries in a six-row tableau. That would force output supported only at the origin and contradict order two. This proves exactness.

The extra determinantal assumption cannot be replaced in this proof by merely observing dimension three in each residue field: that observation alone does not make the three pivot columns generate the whole module over the ring. Even the square-root assertion need not descend from residue fields in general; for example the local ring \(\mathbb Q[t]_{(t^2+15)}\) has a residue root of \(-15\), but no such root in its fraction field \(\mathbb Q(t)\). The square-zero step above is what makes exact lifting possible for this tableau stratum.
