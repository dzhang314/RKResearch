# Six scalar sites and three paid terminals are impossible in the SDIRK9 twin-port bridge

This excludes the grouped $(N,t,s_r)=(6,3,6)$ chart at thirteen stages. Here $N$ is the number of scalar quadrature sites, $t$ is the number of old reverse terminal means, and $s_r$ is the number of old reverse rows. The exclusion covers every regular two-port branch of the original four-row arithmetic-progression forward family, including the certified six-row stem whose two ports are approximately $2.29199572,5.63237267$. The unrestricted order-nine interval does not change.

## Actual terminal primitives supply two additional equations

The six forward rows have a dense return through rooted size four. Their genuine size-five error span is the three-dimensional space of polynomials of degree at most four vanishing at two actual size-five pure ports $v,w$. Both shifted decoder rows agree literally with the corresponding old strict rows. The reverse return pays words through length two. Its three old terminal means, at distinct scalar sites disjoint from the protected sites, are exact through length three. The remaining sites each get a fresh representative, two of which merge into the forward ports. The physical count is $6+6+3-2=13$.

Use the normalized physical reflected variable $Y$ on $[0,1]$. If the diagonal is $\gamma\ne0$, the two protected sites are $a=1-\gamma v$, $b=1-\gamma w$, and the first reverse clock is $\gamma$. Let $c$ be the third nonterminal site and $G(Y)=(Y-a)(Y-b)(Y-c)$. The old top reverse residual is a line: it vanishes at the three terminal sites, and the length-three clock word has a nonzero cubic leading coefficient outside the degree-two return. Let $K$ be the monic cubic whose roots are those terminals.

Write $E_y$ for site evaluation, and $J$ for integration from zero in the unit-diagonal coordinate $y=Y/\gamma$ for the next identity. The literal grouped row equation is
$$
 ML=E_y JD_r+S(M-E_yD_r),
$$
where $L$ is the actual reverse primitive matrix, $M$ the actual means and $D_r$ the old return. Each terminal row of $S$ is its unit coordinate row. At word length three the next primitive discrepancy is $(SE_y-E_yJ)K$, with the polynomial written in the appropriate coordinate. At **each old terminal** this is $-E_yJK$, not zero just because the length-three evaluation is exact. Both $G$ and $YG$ vanish at all nonterminal sites, so these two allowed forward tests see only the old terminal primitive discrepancies.

Why the pairing is necessary: attach a unary root to an actual size-five generator of the forward residual, then append any three unary or same-root leaf marks. Only the first source has all three exterior letters; lower sources cancel by the dense reverse return, the grouped identity and quadrature. Reflection changes clock multiplication by an affine substitution whose lower-word terms are already paid. Two imperfect children cannot meet through order nine because each would have size at least five.

Now take $Jf(Y)=\int_0^Y f(Z)\,dZ$ and $\mathcal I f=\int_0^1 f(Y)\,dY$. Conversion from the unit coordinate only multiplies the terminal primitive term by a nonzero scalar. The mixed tests and precision eight give
$$
 \mathcal I(GJK)=\mathcal I(YGJK)=0 .
$$
Quadrature separately gives
$$
 \mathcal I(Y^jGK)=0,\qquad j=0,1,2,
$$
because $GK$ is the full node hull. These five conditions are linear in the coefficients of $K$. They do not require positive output shares, interior abscissae, or assumptions about sign.

If a cubic-dense reverse decoder is proposed to make the top residual zero, the literal old terminal primitive rows in the grouped identity make all three old means exact through length four. The invertible word commutator packet of degrees $4,2,0$ then requires $3+3+1=7$ old rows: three independent distinct-site length-four targets, plus the dense lower quadratic and constant blocks. Fitting three evaluation means with just six old rows cannot buy this extra primitive grade.

## Four possibilities for the first reverse clock

The chronological first reverse clock is $\gamma$, so it is one of the six actual sites.

1. **First site is $a$.** Set $\gamma=1/(1+v)$ and leave $c$ variable. With the four monomial columns of $K$, the $5\times4$ matrix of the five equations has rank at most three. Its maximal minors have degree at most four in $c$.
2. **First site is $b$.** Interchange $v,w$.
3. **First site is $c$.** Set $c=\gamma$ and use the same rank test. Its minors have degree at most eleven, not twelve: the degree-three coefficient of $G$ in $\gamma$ is constant as a polynomial in $Y$. For constant $G$ the primitive rows are linear combinations of the first three moment rows, by $\mathcal I(Jf)=\mathcal I((1-Y)f)$ and $\mathcal I(YJf)=\mathcal I((1-Y^2)f)/2$.
4. **First site is a terminal.** Write $K=(Y-\gamma)Q$ with $Q$ quadratic, and $G=(Y-c)G_0$. The five equations have the form $B\mathbf q-cA\mathbf q=0$, with $B$ using $YG_0$, $A$ using $G_0$, and $\mathbf q$ the three monomial coefficients of $Q$. Thus $[B,A]$ has a kernel vector with its last three entries $-c$ times its first three. If the matrix has rank five, its signed maximal cofactors span the kernel, so the corresponding $2\times2$ minors of its two blocks vanish. If the rank is smaller, all the maximal cofactors vanish anyway. The entries in the $5\times6$ matrix have degree at most three in $\gamma$, making the final polynomials degree at most thirty.

## Exact reduction covers every regular port conjugate

The branch field is specified by the monic seed cubic $s^3-9s^2+18s-6$, the monic first-port quartic
$$
 v^4-(8s/3+8)v^3+(2s^2+16s+12)v^2-(8s^2+16s)v+4s^2,
$$
and the monic polynomial four times
$$
 \frac{(J-I)((X-s)(X-v)(X-z))}{X-v},
 \qquad z=\frac{v(2s-v)}{2(3s-v)} .
$$
Here $J$ uses the unit-diagonal variable $X$; the last polynomial defines $w$.

The seed cubic is irreducible over the rationals. At $p=31$, its simple root $s=11$ lifts into $\mathbb Q_{31}$ and the monic quartic has irreducible reduction. At $p=17$, the simple roots $s=16,v=1$ lift into $\mathbb Q_{17}$, where the last monic cubic has irreducible reduction. A monic factor of an integral monic polynomial over a local field has integral coefficients, since its roots are integral. Thus both tested reductions rule out characteristic-zero factors in their respective tower levels. This is a number field, not a product from which the modular replay might accidentally select another component.

At $p=37$ the simple roots $s=8,v=3,w=19$ provide a good reduction of this tower. All denominators used by the formulae are units. In each of the four cases the two selected polynomials retain the full stated degrees $4,4,11,30$ and satisfy a Bézout identity equal to one modulo $37$. Their full-degree characteristic-zero Sylvester determinant is therefore nonzero. This does **not** require the unknown real clock to reduce modulo $37$: it excludes common roots over an algebraic closure. Any regular real choice of the ports is a conjugate embedding of this tower.

## Reproduction and scope

    sha256sum -c sources.sha256
    python3 check.py

The exact replay verifies irreducibility by the Frobenius criterion, reconstructs the physical primitive-moment matrices and signed cofactor tests, and verifies the degree-preserving Bézout coefficients. It uses no floating arithmetic. The matching [Lean audit](../../lean/evidence/sdirk9-six-site-three-terminal-20261127/README.md) independently kernel-checks the emitted coefficient identities on Lean 4.36.0. The characteristic-zero transfer and actual rooted proof are mathematical.

The complementary [seven-site exclusion](../real-sdirk9-seven-site-three-terminal/README.md) removes $(7,3,5)$. The three other grouped counts $(6,1,4),(6,2,5),(7,2,4)$ are not resolved by these two arguments.
