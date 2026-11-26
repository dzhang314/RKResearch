# Exact order seventeen in 56 explicit stages

There is an explicit Runge–Kutta tableau of exact order seventeen with at most **56** stages over \(\mathbb U_{17}\coloneqq\mathbb Z[1/17!]\), and after every base change to a nonzero commutative \(\mathbb U_{17}\)-algebra. The previous bound was 57. The reduction uses seven existing scalar receiver stages for a single weighted observation of the reverse error. None of their individual weights needs to be a unit. The paid coefficient of that observation is \(2560/(3^{11}11)\). A controlled late correction gives a next homogeneous defect of raw value one. The construction below specifies the [literal tableau](tableau-17.json) by interpolation. The [reconstruction](weighted_taps_17.py) and [verifier](verify.py) reproduce the tableau and next-order defect with exact rational arithmetic.

## Forward and reverse input rows

Use the **27-row** forward \(\Pi_F=\Pi_9\) through the end of the second bank in [the two consecutive primitive reads](TWO-PRIMITIVE-READS.md). It begins with the archived 16-row order-nine seed, its literal output endpoint and the new midpoint. Its next four centered clocks are \(-1/3,1/3,3/5,-5/3\); the next five are \(-8/3,-1/3,1/3,-2,2\), in that order within their bank. Each of these rows uses the preceding chart and integration up to its own clock as in that source. Do not append the seven grade-ten preparation rows. The whole integral of \(\Pi_F\) is the literal old order-nine output row. The old origin and endpoint pin both exact evaluations through size ten. The promoted read \(\ell_5\) is a linear combination of the last five existing stage coordinates, exact on tree derivative data through size ten. The chart \(\Pi_F\) pins their individual evaluation reads on arbitrary data, so it pins \(\ell_5\) as well.

Use the original **11-row** grade-six chart \(\Pi_R=\Pi_6\) of Section 2 of [the signed reverse construction](CONSTRUCTION.md). Its first seven rows and weights are listed there. Append the actual order-six endpoint, then the midpoint and the two later pure rows at reverse clocks \(2/3,5/6\), as specified there. Its distinct centered reverse clocks are \(-1,-1/3,0,1/3,2/3,1\). The old exact grade-seven observation from [the shorter grade-seven chart](SHORT-GRADE-SEVEN.md) is denoted \(\ell\). In the centered variable \(v=2y-1\) it is
\[
 \ell(f)\coloneqq \frac{81}{4}f(0)-\frac{2187}{64}f(1/3)
                              +\frac{2187}{100}f(2/3).
\]
The chart \(\Pi_R\) pins the individual point reads in \(\ell\), so on size-seven tree data it agrees with the exact \(\ell\) read even though it does not give the whole exact polynomial at that size. Both endpoint reads, supplied by the origin and old order-six endpoint, are exact through size seven.

Throughout, polynomial primitives \(I_y f\) use the original reverse clock \(y\) on \([0,1]\); when \(f\) is written in \(v\), this means \(I_y f=\int_0^y f(2z-1)\,dz\). For centered polynomials define \(\mu f\coloneqq\tfrac12\int_{-1}^1 f(v)\,dv\), and put \(H(v)\coloneqq1-v^2\). The physical primal clock of a reverse row is \(x=1-y\). The ordinary order proof uses forward grade \(m=9\), reverse word budget \(r=7\), and \(17=m+r+1\).

## A grid and a paid weighted read of the reverse error

Use the 17 scalar quadrature sites with centered coordinates
\[
 \mathcal G\coloneqq \{0,\pm1,\pm2,\pm3,\pm4,\pm5,\pm6,\pm7,\pm9\}/9.
\]
Let \(\lambda_a\) be the centered integral of the ordinary Lagrange cardinal polynomial for \(a\in\mathcal G\). They give scalar degree-16 precision; symmetry gives degree 17 as well. All site differences are units of \(\mathbb U_{17}\), since the nonzero absolute index differences are at most 18. No assertion is made that the individual \(\lambda_a\)'s are units.

The reverse scalar sites serve the following roles. The same physical clock can host one additional split probe at a distinct reverse label.

| Label type | Centered reverse coordinates |
|---|---|
| Three **additional**, unit-mass split probes | \(-3,3,6\) divided by 9 |
| Existing scalar sites used as **live unsplit** early probes | \(\mathcal E\coloneqq\{-6,-5,-4,-2,2,4,5\}/9\) |
| Existing pure sites used for late corrections | \(\mathcal L\coloneqq\{0,\pm1,\pm3,6,\pm7\}/9\) |
| Remaining scalar sites, pure and unmodified | \(\pm1\) |

All original reverse donor clocks belong to the ten pure sites. In particular no unsplit early live probe uses a former donor-clock site or either endpoint.

For a word \(W\) of length at most six in reverse extension and reverse clock multiplication, let \(d_W\) be its values on the eleven base donors and \(g_W\) its exact model polynomial. Words are applied to the all-ones vector; the exact operations are integration from zero and the corresponding clock multiplication. Multiplication by the physical clock \(1-y\) is allowed by linearity. The discrepancy
\[
 \sigma_W\coloneqq g_W-\Pi_Rd_W
\]
is zero for words of length at most five. For length six it has degree at most six and satisfies \(\sigma_W(\pm1)=0\) and \(\ell(\sigma_W)=0\), by the actual two endpoint reads and old contrast above. These properties also hold for any linear combination of shorter and length-six words.

An early live probe with literal reverse incoming row \(I_y\Pi_R\) gives the exact value \(g_W(a)\) at its centered site \(a\), for words through length six. Indeed every outer extension there applies the primitive to a word of donor length at most five; any outer clock letters are exact multiplications. Its discrepancy reading is therefore the **difference** between its own word value and \((\Pi_Rd_W)(a)\). This subtraction is a linear functional of the original donor columns and the one live probe column; it is zero for earlier words.

Three such reads at \(-1/3,1/3,2/3\) determine \(\sigma_W(0)\) using \(\ell(\sigma_W)=0\). Let \(\sigma_0\) be \(H\) times the degree-at-most-three interpolating polynomial at these four points, using values \(\sigma_W(a)/H(a)\). The pivots are paid. The difference has the form \(kq\), where
\[
 q(v)\coloneqq vH(v)(v^2-1/9)(v-2/3),\qquad
 P(v)\coloneqq(v^2-1/81)(v^2-49/81).
\]
Indeed both divided polynomials have the same four point reads and degree at most four. The product \(Pq\) vanishes at every site outside \(\mathcal E\). Consequently the last coefficient is given by
\[
 k\coloneqq
 \frac{\displaystyle\sum_{a\in\mathcal E}\lambda_a P(a)
           (\sigma_W(a)-\sigma_0(a))}{\mu(Pq)}.
\]
The equality follows from degree-16 quadrature since \(Pq\) has degree ten. This pivot is a paid unit. Setting \(t=v^2\), the three moments of \(v^2H(v)(v^2-1/9)\,t^j\) for \(j=0,1,2\) are \(8/189,8/315,104/6237\), respectively, by integrating consecutive even powers. Thus
\[
 \mu(Pq)=\frac8{3^{11}\cdot5\cdot7\cdot11}
     \bigl(142155-2673(1+49)+55\cdot49\bigr)
   =\frac{2560}{3^{11}\cdot11}.
\]
On arbitrary virtual word data, use exactly these linear formulas to define \(\mathcal D\coloneqq\sigma_0+kq\). It gives \(\sigma_W\) on every word of length at most six. Crucially the coefficient on the raw value of each unsplit early probe \(a\) is **explicitly** \(\lambda_a\) times a paid coefficient: it only enters the numerator of \(k\). This property is independent of whether \(\lambda_a\) vanishes after base change.

## Literal reverse rows, paid transpose, and the stage count

For \(a\in\mathcal L\), let \(B_a\) be the degree-at-most-seven Lagrange cardinal polynomial for the eight distinct points of \(\mathcal L\). Define
\[
   E_a(v)\coloneqq H(v)B_a(v)/H(a),\qquad
   U_a(f)\coloneqq\int_0^1 E_a(2y-1)\,I_y f\,dy,
   \qquad \gamma_a\coloneqq\ell_5\bigl(E_a(-u)\bigr),
\]
where the last read uses the centered **forward** variable \(u=2x-1\). These are paid: the point factors and differences are units, the product in the displayed integral has degree at most 16 for \(f\) of degree at most six, and \(\ell_5\)'s pivots are paid by the specified forward construction. Every degree-at-most-nine polynomial vanishing at both endpoints is its interpolation by the \(E_a\)'s, because the polynomial divided by \(H\) has degree at most seven. Let \([v^6]f\) denote the degree-six coefficient in the centered reverse variable. The correction functional at site \(a\) will be
\[
 U_a(f)+128\gamma_a[v^6]f .
\]

Here is an explicit virtual reverse chronology and mass assignment. On each group use the listed order or, where no order is specified, increasing site index. Write \(L\) for the matrix of reverse rows and \(\beta_i\) for their virtual masses.

1. List the eleven original reverse donor rows with masses \(+1\). Their only inputs from the virtual array are their original predecessor columns. List three split live probes in the order \(-1/3,1/3,2/3\), with incoming row \(I_y\Pi_R\) and mass \(+1\). List the seven early live probes at \(\mathcal E\), with incoming row \(I_y\Pi_R\) and mass \(\lambda_a\). All probe incoming rows in this step use just the eleven original columns.
2. List one negative copy of each of the eleven original rows and of each of the three split probes, with mass \(-1\), using exactly the same incoming row as its positive copy, padded with zeros. These negative copies have no outgoing reverse column taps.
3. At each of the ten scalar sites outside \(\mathcal E\), list one ordinary pure receiver with mass \(\lambda_a\) and incoming row \(I_y\Pi_R\).
4. At every \(a\in\mathcal L\) append two more reverse rows at that same site, with masses \(+1,-1\) respectively, and incoming rows
\[
 I_y\Pi_R+\bigl(U_a+128\gamma_a[v^6]\bigr)\mathcal D,
 \qquad I_y\Pi_R.
\]
The first correction is a linear functional of just the original donor coordinates and the early live probe coordinates from Step 1. No column from Steps 2–4 is ever a reverse input.

Every row has the indicated reverse clock as its sum because \(\mathcal D\) annihilates the constant word. For an original or split live column \(j\) the mass is 1. For an unsplit live column \(j\) of site \(a\), every tap on it has the explicit form \(L_{ij}=\lambda_a M_{ij}\) from the weighted read. In primal reversed chronology define
\[
 T_{ji}\coloneqq
 \begin{cases}
    \beta_i L_{ij},& j\text{ is an original or split live column},\\
    \beta_i M_{ij},& j\text{ is an unsplit live column},\\
    0,&\text{otherwise}.
 \end{cases}
\]
It is strict in primal chronology and satisfies \(\beta_jT_{ji}=\beta_iL_{ij}\) over the paid ring and after every base change. There is **no division by a scalar mass**. With \(E f=(f(x_i))_i\) and \(I f=(\int_0^{x_i}f(z)\,dz)_i\) in primal clocks, append the resulting suffix to the forward chart with cross block \((I-TE)\Pi_F\). Give it the masses \(\beta_i\) as output weights, and give the forward prefix zero output weights before merging.

Every reverse label without an outgoing column has the exact same literal primal row \(I_x\Pi_F\) at the same physical clock. Thus its complete row and all later taps can be merged, including the two signs of each late correction. At an unsplit live clock its single scalar site is already occupied by that one live row; no pure row is required there. All original and split negative copies occur at the ten designated pure sites. The pure primal origin is the actual forward origin, and the pure primal clock-one row is the actual old order-nine output endpoint, because \(I_1\Pi_F\) is exactly that literal row on arbitrary data. Both merges are paid literal identities, not just equal clocks. No merger of a live row with another live row is counted. The tally is
\[
 27+11+17+3-2=\mathbf{56}.
\]

## Every ordinary order condition through seventeen

The rooted-tree proof is the same single-error expansion as in the signed-reverse construction, with the late correction checked here. Give a forward child \(t\) its exact derivative polynomial \(g_t\) and residual \(\rho_t\coloneqq g_t-\Pi_F\boldsymbol{\Phi}_t\). It vanishes through size nine. A first primitive error needs a child of size at least ten, so two such errors cannot occur at one rooted product through size seventeen. The suffix source from an extension of \(t\) is \((TE-I)\rho_t\). After propagating it along a path, every further extension contributes \(T\) and each ideal sibling contributes its model clock power. Moving these operations to the reverse side gives a word \(W\) on ones of length \(d\le16-|t|\), followed by one action of \(L\) in the first term. Its weighted contribution is
\[
 \langle L W,E\rho_t\rangle_\beta-\langle W,I\rho_t\rangle_\beta,\qquad
 \langle a,b\rangle_\beta\coloneqq\sum_i\beta_i a_i b_i.
\]
All original and split donors still cancel against their identical negative copies on every reverse word, since they have equal incoming rows and equal clocks. On any regular or late receiver, words of length at most six have their exact model value: the correction consumes \(\mathcal D\) only on a shorter word, where it is zero. Thus \(\langle W,I\rho_t\rangle_\beta\) is the ordinary scalar quadrature of the corresponding model product. For the extra action \(L W\) its only possible missing model part is \(I_y\sigma_W\). All lower lengths \(d\le5\) have \(\sigma_W=0\). If \(d=6\) then \(|t|=10\), so \(\rho_t\) vanishes at the endpoints, has degree at most nine, and satisfies \(\ell_5(\rho_t)=0\). Interpolating its reverse-reflected polynomial by the \(E_a\)'s gives
\[
 \sum_{a\in\mathcal L}\rho_t(1-y_a) U_a(\sigma_W)
     =\int_0^1\rho_t(1-y)I_y\sigma_W\,dy,
 \qquad
 \sum_{a\in\mathcal L}\rho_t(1-y_a)\gamma_a=0.
\]
These are exactly the signed late corrections needed for the first term. The scalar products and primitives in both terms have degrees at most sixteen by the path-size count. The ideal first and second terms are equal by polynomial triangular integration, so every propagated error cancels. The remaining scalar derivative weights integrate to the required order values. This proves all rooted conditions, including branching trees.

## An exact next-order witness

Let \(C\) denote coordinatewise multiplication by the actual stage clock. Use the homogeneous size-seven formal-zero expression \(\mathcal V\) of [the short symmetric grids](SHORT-SYMMETRIC-GRIDS.md), taking its unsubtracted \(\mathbf V_O\) as required there. To specify it in the present tableau, set
\[
 \mathbf d\coloneqq\mathbf c^{\odot2}-2A\mathbf c,
 \quad \mathbf V_O\coloneqq-72A C^2 A\mathbf d,
 \quad \mathbf W_Z\coloneqq A\mathbf c^{\odot5}-\mathbf c^{\odot6}/6,
 \quad \mathcal V\coloneqq-2\cdot945\,\mathbf V_O+3\cdot(8\cdot8505)\mathbf W_Z.
\]
The old cubic clock-weighted mean of \(\mathcal V\) is one, from the two old moments \(-47/945\), \(-31/(8\cdot8505)\) proved in the cited source. On the forward bank set \(G\coloneqq\Pi_8(C^2\mathcal V)\), with \(\Pi_8\) the earlier forward chart. Its endpoints, mean, and four old point reads vanish; its first physical moment is one. Let \(P_0\coloneqq I_xG\) in the forward clock. It has double endpoint zeros, degree at most eight, and mean \(-1\) by integration by parts. On this space the first promoted read \(\ell_4\) gives the ordinary mean, so \(\ell_4(P_0)=-1\).

The last five forward rows read \(P_0\) on \(A C^2\mathcal V\), and read \(xP_0\) on the homogeneous size-eleven expression \(w\coloneqq C A C^2\mathcal V\). By the exact normalized rule defining the second promoted read,
\[
 \ell_5(w)=\ell_4((xP_0)')=-1/2,
\]
where the derivative is in the centered forward variable and the second term \(\ell_4(xP_0')\) vanishes by the four old point zeros of \(G\). This is the same literal five-row calculation as in [the reflected order-twenty construction](REFLECTED-ORDER-20.md). Both endpoints on \(w\) are zero, since \(A C^2\mathcal V\) is size ten and formal-zero, and the actual endpoint reads are exact through that size. On the full suffix, \(A C^2\mathcal V\) likewise has zero values: the grade-nine forward chart gives exact suffix derivatives through size ten before any weighted error cancellation is needed. Clock multiplication preserves these zeros. In particular \(\rho_w\coloneqq-\Pi_F w\) is a degree-at-most-eight endpoint-zero polynomial and \(\ell_5(\rho_w)=1/2\).

Now extend \(w\) and adjoin six root leaves. The resulting homogeneous formal-zero tree combination has size eighteen. Since \(w\) is zero on the full suffix, its only suffix derivative term is the source \((TE-I)\rho_w\) times the sixth power of the physical clock. The adjoint word is therefore the pure scalar word \(W=x^6\). For this test the \(U_a\) correction gives precisely the full paired primitive on \(\rho_w\), by endpoint-zero interpolation. These terms cancel by triangular integration. The only remaining part is the deliberately added term
\[
 128\,[v^6]\sigma_W\,\ell_5(\rho_w)
   =128\cdot 2^{-6}\cdot\tfrac12=1.
\]
Here \([v^6]\sigma_W=2^{-6}\) because \(g_W=(1-v)^6/2^6\) and \(\Pi_R d_W\) has degree at most five. This is the actual raw output of the homogeneous formal-zero size-eighteen combination, not a limit or model defect.

To pass to the order conditions, for each tree \(t\) of size eighteen the ratio \(t!/18\) is the product of the child factorials and is a paid unit. The same linear combination of the defects in the order conditions divided by those child-factorial products is therefore 18, since the exact-polynomial combination is zero. The size-eighteen bush has defect \(-1\) modulo 18. Their ideal is the unit ideal, giving exact order after every nonzero paid base change. In this particular case 18 itself is already a paid unit; the argument also explains why the late correction method may be used at a next unpaid prime.
