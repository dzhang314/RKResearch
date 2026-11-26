# Explicit methods of exact orders 18, 19 and 20 in 62, 70 and 75 stages

The weighted regular-probe construction in [the order-17 proof](WEIGHTED-REGULAR-PROBES.md) gives the following additional bounds over \(\mathbb U_p\coloneqq\mathbb Z[1/p!]\), valid after every base change to a nonzero commutative \(\mathbb U_p\)-algebra.

| Order | Forward rows | Reverse base rows | Scalar sites | Extra split live probes | Literal merges | Stages |
|---:|---:|---:|---:|---:|---:|---:|
| 18 | 22 | 22 | 17 | 3 | 2 | **62** |
| 19 | 27 | 22 | 19 | 4 | 2 | **70** |
| 20 | 27 | 27 | 19 | 4 | 2 | **75** |

The previous paid upper bounds were 63, 71 and 78. Order 18 uses weighted recovery of **two** missing directions; order 19 uses one, and order 20 uses four, separated into two pairs by parity. No individual power of a scalar quadrature mass is inverted. The constructions have a homogeneous next-order raw defect equal to one.

## 1. Common rows and order proof requirements

Let \(v\coloneqq 2y-1\) be the centered reverse clock, \(u\coloneqq2x-1\) the centered forward clock, and \(x=1-y\) on a reverse label in the primal tableau. Define
\[
 H(v)\coloneqq1-v^2,\qquad \omega(v)\coloneqq H(v)^2,
 \qquad \mu f\coloneqq\tfrac12\int_{-1}^1 f(v)\,dv.
\]
As in the order-17 proof, \(I_y f\) for a polynomial written in \(v\) is \(\int_0^y f(2z-1)\,dz\). Given a reverse word \(W\), its exact scalar polynomial is \(g_W\), its vector on the base reverse donor rows is \(d_W\), and its missing polynomial is \(\sigma_W\coloneqq g_W-\Pi_R d_W\). A live probe at its centered clock \(a\) has reverse row \(I_y\Pi_R\). It gives \(\sigma_W(a)\) as its own word value minus the modeled value \((\Pi_R d_W)(a)\) whenever the word length is at most \(r-1\), provided \(\Pi_R\) is exact through size \(r-1\). Words of length at most \(r-2\) have \(\sigma_W=0\). The symbolic linear reconstruction \(\mathcal D\) below gives \(\sigma_W\) through word length \(r-1\) and has a factor \(\lambda_a\) on every unsplit live input at site \(a\).

Use the following chronological list of virtual reverse rows in all three methods. Every grid row uses \(y=(1+a)/2\) for its displayed centered coordinate \(a\).

1. List the specified reverse base rows in their original order, with mass \(+1\). List the split live probes at their stated sites, with incoming rows \(I_y\Pi_R\) on the old base columns and mass \(+1\). List the live unsplit probes at their specified sites, in increasing order, with the same type of incoming row and mass \(\lambda_a\). Here \(\lambda_a\) is the centered integral of the ordinary Lagrange cardinal function of the chosen full scalar grid.
2. List a negative copy of every base row and every split probe, in the same order as Step 1, with identical zero-padded incoming coefficients and mass \(-1\). They are never used as reverse columns.
3. At every grid site not used as a live unsplit probe, add an ordinary row \(I_y\Pi_R\) with mass \(\lambda_a\). These are never used as reverse columns.
4. At each late site \(a\in\mathcal L\) add two more rows with masses \(+1,-1\), in increasing site order, with incoming rows
\[
 I_y\Pi_R+\bigl(U_a+\eta\gamma_a[v^{r-1}]\bigr)\mathcal D,
 \qquad I_y\Pi_R.
\]
Here \(\eta\) and \(\gamma_a\) are specified below, \([v^{r-1}]\) extracts the indicated coefficient, and \(\mathcal D\) uses only the base and live probes of Step 1. Neither row in Step 4 is ever used as a reverse column.

All corrections annihilate the constant word, so the reverse row sums give the stated clocks. Let \(L\) and \(\beta_i\) be the resulting reverse matrix and masses. The paid weighted transpose is exactly as in the order-17 source: in primal reversed order, for a unit-mass live reverse column \(j\) use \(T_{ji}=\beta_i L_{ij}\); for an unsplit live column with explicit factorization \(L_{ij}=\lambda_a M_{ij}\) use \(T_{ji}=\beta_i M_{ij}\); otherwise use zero. Its adjoint identity is intact even when a scalar mass becomes zero. The forward-to-suffix block is \((I-TE)\Pi_F\), in the notation of the order-17 source, and the output weights are the reversed masses with zeros on the initial forward prefix.

In all three cases the forward chart is exact through tree size \(m\), with two actual endpoint reads exact through size \(m+1\), and \(p=m+r+1\le2m+2\). The first forward residual at size \(m+1\) is in \(H\mathcal P_{m-2}\) on the centered interval, where \(\mathcal P_j\) denotes polynomials of degree at most \(j\). Thus a late set of \(m-1\) distinct nonendpoint sites suffices. If \(B_a\) is its ordinary cardinal polynomial, set
\[
 E_a(v)\coloneqq H(v)B_a(v)/H(a),\qquad
 U_a(f)\coloneqq\int_0^1 E_a(2y-1)I_yf\,dy.
\]
The degree here is at most \(m+r=p-1\), so every denominator is paid. The following \(\gamma_a\)'s represent a functional on all of \(H\mathcal P_{m-2}\) vanishing on ordinary size-\((m+1)\) residuals. With \(\mathcal D\) supplied below, the ordinary single-source tree proof of the order-17 source applies verbatim: pairs of identical old donor rows cancel, the late difference adds the exact paired primitive of the missing \(\sigma_W\), and the added null term vanishes. The degree-\((p-1)\) scalar quadrature pays all the model products. All clocks used by the negative copies are among the pure sites. The complete primal rows of Steps 2–4 coincide at each equal clock, since they have zero reverse columns and thus the same literal forward row \(I_x\Pi_F\). The original forward origin and its actual old order-nine output endpoint merge with the two pure endpoint rows. The forward chart always has \(I_1\Pi_F\) equal to that output on arbitrary data. All other live rows are counted without assuming accidental equality.

## 2. Order 18: two weighted directions

Here \(m=8,r=9\). Use the 22-row forward and 22-row (unmodified, before the mixed rows) reverse grade-eight charts used in [the projected order-18 proof](PROJECTED-ORDER-18.md). Both start from the archived 16-row order-nine seed, its actual output endpoint, and the grade-six midpoint. Their grade-seven primitive banks have centered values \((-1/3,1/3,1/5,-5)\) forward and \((-1/3,1/3,-1/5,5)\) reverse. This reverse bank is essential for payment at order 18. The order-19 bank below would use an unpaid factor 19 in one grade-eight pivot.

Use the reported 17-site grid
\[
 \{0,\pm1/5,\pm1/3,\pm1/2,\pm2/3,\pm1,\pm3/2,\pm2,\pm5\}.
\]
Its site differences are paid, as verified in the preceding source. Its monic nodal polynomial is odd, so the interpolatory rule has degree-17 precision. The original scalar sites of the order-nine seed are \(\{0,\pm1/3,\pm1/2,\pm1,\pm2\}\). The reverse base adds sites \(-1/5,5\). Split the three live probes at \(-1/3,1/3,-1/5\), in that order. The six live unsplit sites are \(\{1/5,-5,\pm2/3,\pm3/2\}\), exactly the donor-free sites. For late corrections use
\[
 \mathcal L\coloneqq\{0,\pm1/3,\pm1/2,\pm2\},\qquad
 \gamma_a\coloneqq\mu E_a,\qquad \eta\coloneqq -256.
\]
The true forward mean pin at size nine makes \(\sum_a\gamma_a\rho(1-y_a)=0\) for the ordinary first source.

Write
\[
 Q_4(v)\coloneqq(v^2-1/9)(v+1/5)(v-5),\quad
 F(v)\coloneqq(v^2-1)Q_4(v),\quad J_0\coloneqq16/945,\quad \kappa\coloneqq12.
\]
The old reverse mean and promoted \(\ell_4\) read are true through size nine, so \(\mu\sigma_W=\ell_4(\sigma_W)=0\) at length eight and the endpoints are zero. Derive \(\sigma_W(5)\) from \(\ell_4(\sigma_W)=0\). In the normalized rule defining \(\ell_4\), the coefficient of the omitted site is a unit: its unnormalized weighted-cardinal numerator is \(\mu(\omega Q_4/(v-5))=J_0/5\), and its denominator is \(\omega(5)Q_4'(5)\), a unit. Let \(f\) be \(H\) times the degree-at-most-three interpolant on the four \(Q_4\) sites, fitting \(\sigma_W/H\). Start the fit with
\[
 \sigma_0\coloneqq f-(\mu f/J_0)F.
\]
The fitting values remain unchanged and its mean is zero. Because \(\mu F=\mu(v^2F)=J_0\) and \(\mu(vF)=\kappa J_0\), the remaining error is
\[
 \sigma_W-\sigma_0=k_1F(v-\kappa)+k_2F(v^2-1).
\]

For the last two coefficients put
\[
 R(v)\coloneqq v(v^2-1/4)(v^2-4),\quad
 \mathcal H(v)\coloneqq v(v^2-1)(v^2-1/9)(v^2-1/4)(v^2-4),\quad
 s\coloneqq-24/5.
\]
Then \(FR=\mathcal H(v)(v^2-1+sv)\) and \(R(\sigma_W-\sigma_0)\) vanishes at every non-early grid site. Define three observed weighted values
\[
 M_j\coloneqq\sum_{a\text{ unsplit}}\lambda_a a^{2j}R(a)
                       (\sigma_W(a)-\sigma_0(a)),\qquad j=0,1,2.
\]
Quadrature identifies these with the integrals of the same polynomials: their degrees are at most 17. Since \(\mathcal H\) is odd, writing \(A_j\coloneqq\mu(v^{2j+1}\mathcal H)\) gives
\[
 M_j=A_j h_1+A_{j+1}h_2,
 \qquad h_2\coloneqq k_1+s k_2,
 \qquad h_1\coloneqq-s\kappa k_1-h_2.
\]
For a reproducible check of the four moments, the formula
\[
 \mu\bigl(v^2H(v)(v^2-1/9)(v^2)^j\bigr)
 =\frac{8(4j+5)}{9(2j+3)(2j+5)(2j+7)}
\]
and \((v^2-1/4)(v^2-4)=(v^2)^2-(17/4)v^2+1\) give
\[
 (A_0,A_1,A_2,A_3)=(19838,13674,9942,127778/17)/405405.
\]
Scale the measured vector \((M_0,M_1,M_2)\) by \(405405/2\); its coefficient matrix has adjacent pairs \((a_j,a_{j+1})\) with
\[
 (a_0,a_1,a_2,a_3)\coloneqq(9919,6837,4971,63889/17).
\]
Let \(B_0,B_1\) be its square submatrices on rows \((0,1)\), \((1,2)\), with determinants \(\Delta_0,\Delta_1\). Direct products give
\[
 \Delta_0=7260\cdot353,\qquad 17\Delta_1=47379\cdot353+9,
 \qquad (-7438507/7260)\Delta_0+2669\Delta_1=1.
\]
Apply the adjugate of \(B_0\) and of \(B_1\) to the respective pairs of scaled measurements and add them with coefficients \(-7438507/7260,2669\). This gives \((h_1,h_2)\). Set \(k_1=-(h_1+h_2)/(s\kappa)\), \(k_2=(h_2-k_1)/s\). This defines \(\mathcal D\) on arbitrary data by the same formulas; it is paid and has the required unsplit mass factors. In particular it does not invert 353 or 19.

## 3. Order 19: one weighted direction

Here \(m=9,r=9\). The forward 27 rows are exactly the double-promoted forward bank of the order-17 source, with the two additional banks at \((-1/3,1/3,3/5,-5/3)\) and \((-8/3,-1/3,1/3,-2,2)\). The reverse grade-eight chart has the same first 18 rows and takes the next four pure \(\Pi_7\) rows at \((-1/3,1/3,1/2,-2)\). This is the first 22 rows of the order-20 reflected construction in [the earlier reflected order-20 proof](REFLECTED-ORDER-20.md). Use
\[
 Q_4(v)\coloneqq(v^2-1/9)(v-1/2)(v+2),\quad F(v)\coloneqq(v^2-1)Q_4(v),\quad
 J_0\coloneqq16/945,\quad \kappa\coloneqq-15/4.
\]
The grade-eight pivots \(J_0(1\pm\kappa)\) are now paid because 19 is inverted. The old exact readings at size nine are again the two endpoints, mean, and \(\ell_4\). In that last read the old site \(-2\) has unit coefficient: its weighted-cardinal numerator is \(-J_0/2\) and its denominator is \(\omega(-2)Q_4'(-2)\).

Use the symmetric 19-site centered grid
\[
 \{0,\pm1,\pm2,\pm3,\pm4,\pm5,\pm6,\pm7,\pm8,\pm12\}/6.
\]
The only possibly unpaid prime difference in index units is 23; a sum of radii 23 would require the missing 11 and is impossible. The rule has precision at least 18. Split four live probes at \((-1/3,1/3,1/2,0)\). The reverse donor sites are exactly the old nine centered scalar sites of Section 2. Reserve \(1/6\) as a pure site and make every other donor-free site live unsplit. The eight late sites are the seven original donor interior sites and \(1/6\). Use
\[
 \gamma_a\coloneqq\ell_5(E_a(-u)),\qquad \eta\coloneqq512,
\]
where the promoted \(\ell_5\) is the forward one, exact through size ten. The true forward read gives a null functional on the ordinary size-ten source.

Derive the reverse reading at \(-2\) from \(\ell_4(\sigma_W)=0\). Let \(f\) be \(H\) times the degree-at-most-four interpolant of \(\sigma_W/H\) at \(-1/3,1/3,1/2,-2,0\), and put
\[
 \sigma_0\coloneqq f-\frac{\mu f}{\mu(vF)}vF,\qquad
 q(v)\coloneqq v(v+4/15)F(v),\qquad R(v)\coloneqq(v+1/2)(v-2)(v-1/6).
\]
The mean pivot is \(\mu(vF)=-60/945\), paid. The remaining line is \(\sigma_W-\sigma_0=kq\), by the five vanishing values after division by \(H\) and the remaining mean condition. In fact \(\mu q=J_0+ (4/15)\kappa J_0=0\). The product \(qR\) vanishes outside the live unsplit set. With \(\mathcal H\) defined as in Section 2,
\[
 qR=\mathcal H(v)(v+4/15)(v-1/6),\qquad
 \mu(qR)=109/22275,\qquad
 \mu(qR(v+4/9))=13674/405405.
\]
The identities follow from odd parity of \(\mathcal H\) and the moments \(A_0,A_1\) above; adding \(4/9\) in the last expression cancels the \(A_0\) term. Define
\[
 P(v)\coloneqq R(v)\bigl(2509\cdot22275-20\cdot405405(v+4/9)\bigr).
\]
Then \(\mu(Pq)=2509\cdot109-20\cdot13674=1\). The actual reconstruction of \(k\) is therefore
\[
 k\coloneqq\sum_{a\text{ unsplit}}\lambda_a P(a)(\sigma_W(a)-\sigma_0(a)).
\]
All factors are paid, and no mass is inverted. These expressions define \(\mathcal D\coloneqq\sigma_0+kq\).

## 4. Order 20: four weighted directions in two pairs

Here \(m=9,r=10\). Use the same 27-row forward chart as at order nineteen. The 27 reverse rows start with the same grade-eight chart as at order nineteen. The next five pure rows have centered clocks \(0,\pm1/3,\pm1/2\), and the grade-nine read uses those values, the endpoints, the old mean, and the first weighted primitive read. The chart replay verifies its paid determinant and every required tree read. The only first-excess conditions needed here are the two exact endpoint values on size-ten trees.

Use the same 19-site symmetric grid as at order nineteen, now of precision 19. Reserve both \(-1/6\) and \(1/6\) as pure sites. Make all other donor-free sites unsplit live probes. Split four live probes at \(\pm1/3,\pm1/2\). The late sites consist of the old seven interior donor clocks and \(1/6\). Use \(\gamma_a=\ell_5(E_a(-u))\) and \(\eta=-1024\).

Let \(\sigma_0\) be \(H\) times the cubic interpolant of \(\sigma_W/H\) at the four split clocks. Since \(\sigma_W\) has degree at most nine and vanishes at both endpoints, the remaining polynomial is
\[
\sigma_W(v)-\sigma_0(v)=q(v)(k_0+k_1v+k_2v^2+k_3v^3),
\quad q(v)\coloneqq(v^2-1)(v^2-1/9)(v^2-1/4).
\]
Define
\[
R(v)\coloneqq v(v^2-4)(v^2-1/36),
\qquad B_j\coloneqq \frac{36\cdot405405}{2}\,\mu(v^{2j+1}qR).
\]
The product \(qR\) is odd and vanishes at every site not used as an unsplit live probe. Thus the six measurements
\[
\frac{36\cdot405405}{2}\sum_{a\;\mathrm{unsplit}}
 \lambda_a a^j R(a)(\sigma_W(a)-\sigma_0(a)),\qquad 0\le j\le5,
\]
split into two sets of three. The even indices recover \((k_1,k_3)\); the odd indices recover \((k_0,k_2)\). Both use the same matrix with rows \((B_0,B_1),(B_1,B_2),(B_2,B_3)\). The tested products have degree at most 19, so quadrature equals the scalar integral, and the integrals of odd polynomials vanish.

The four entries are
\[
(B_0,B_1,B_2,B_3)=(236213,172119,2215497/17,32885489/323).
\]
For the two adjacent determinants \(\Delta_0,\Delta_1\),
\[
17\Delta_0=19705040124=924\cdot21325801,\qquad
17^2\cdot19\Delta_1=2963584997076.
\]
The second integer is congruent to \(2409509\) modulo \(21325801\), and these two integers are relatively prime. All the other factors used in rescaling are units. Therefore a Bézout combination of the two adjugates gives a left inverse with coefficients in \(\mathbb U_{20}\). It recovers both coefficient pairs and every unsplit column retains its factor \(\lambda_a\). This gives \(27+27+19+4-2=75\) physical stages.

## 5. Exactness at the next size

In the order-18 method use the homogeneous size-ten forward child \(w\coloneqq C^3\mathcal V\) of the previous order-17 source. Its derivative values on the full suffix are zero: \(C^2\mathcal V\) has size nine and zero ideal polynomial, and the grade-eight forward chart ensures that all suffix tree derivatives are exact through size nine before any weighted cancellation is needed. Clock multiplication preserves the zero coordinates. The forward endpoint observations of \(w\) are also zero, and its old forward mean is one. Thus \(\rho_w=-\Pi_F w\) is endpoint-zero and its mean is \(-1\).

In the order-19 and order-20 methods use the order-17 child \(w=C A C^2\mathcal V\) of size eleven. Again its full suffix and both forward endpoint readings vanish, and \(\ell_5(\rho_w)=1/2\) for \(\rho_w=-\Pi_F w\). These conclusions use only the stated preceding 27 forward rows and were checked explicitly in the order-17 source. The expression \(\mathcal V\) is homogeneous or extends to any new tableau by its word definition, with no assumption about higher exactness of individual suffix rows.

In each case extend \(w\) once and adjoin \(r-1\) leaves at the root. Its size is \(m+2+1+r-1=p+1\), and the expression is homogeneous formal-zero. As \(w\) vanishes on the full suffix, the only suffix term is \((TE-I)\rho_w\) tested against the pure scalar reverse word \(W=x^{r-1}\); other products of source errors do not occur in this test. The \(U_a\) part of the late correction pays the exact triangular pairing even on this new child, since \(\rho_w\) still has endpoint zeros and belongs to \(H\mathcal P_{m-2}\). All products tested in this calculation have degrees at most \(m+r=p-1\), using \(\deg\rho_w\le m-1\). The remaining raw output is exactly
\[
 \eta\, [v^{r-1}]\sigma_W\ \sum_{a\in\mathcal L}\gamma_a\rho_w(1-y_a),
 \qquad [v^{r-1}]\sigma_W=(-1)^{r-1}2^{-(r-1)}.
\]
The three choices give respectively \((-256)2^{-8}(-1)=1\), \(512\cdot2^{-8}\cdot(1/2)=1\), and \((-1024)(-2^{-9})(1/2)=1\).

Finally for each size-\((p+1)\) tree \(t\), the child-factorial product \(t!/(p+1)\) is a paid unit. The indicated linear combination of the defects in the order conditions divided by these products is \(p+1\) times the raw output, since the ideal-polynomial combination is zero. The size-\((p+1)\) bush has defect \(-1\) modulo \(p+1\). The two facts give the unit ideal after any nonzero paid base change and complete the exact next-order claim.

## Reproduction

The literal tableaux are available for [order 18](tableau-18-weighted.json), [order 19](tableau-19-weighted.json), and [order 20](tableau-20-weighted.json). For each order, substitute its number in the commands:

~~~sh
python construct.py p --verify-reads
python verify.py p
~~~

The first command rebuilds the literal tableau, checks the paid chart determinants, and verifies every chart read and every additional pin used in the proof. The second samples ordinary full-tableau conditions and checks both the individual next-order defects and the four-tree combination above. The all-tree argument in Section 1 proves ordinary order; the full-tableau samples are a separate consistency check. These are exact constructions, not Lean certificates.
