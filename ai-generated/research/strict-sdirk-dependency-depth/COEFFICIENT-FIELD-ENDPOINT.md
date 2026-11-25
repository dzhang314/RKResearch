# The coefficient field at simultaneous depth and quadrature endpoints

Let $p=2q\ge4$. A **contributing clock** of a tableau $(A,b)$
is an abscissa $c$ of its physical clock column $A\mathbf1$
at which the sum of the output weights of all rows with that clock
is nonzero. Thus clock repetitions are aggregated, and hidden rows
or cancellations do not add quadrature sites.

**Theorem.** Fix a nonzero common diagonal $\gamma$ for which the
sharp off-diagonal dependency depth is $p-2$. Let $E_q$ be the
splitting field over $\mathbb Q$ of the degree-$q$ Legendre polynomial
and let $K_\gamma=\mathbb Q(\gamma)$. A strict SDIRK tableau of order
$p$, depth $p-2$, and exactly $q$ contributing clocks has coefficient
field containing $E_qK_\gamma$. Moreover
$$
 [E_qK_\gamma:\mathbb Q]=(2q-1)[E_q:\mathbb Q].
$$
For each such $\gamma$ this field is attained by a tableau of exact
order $p$ of the stated depth and contributing support. In particular,
for $p=20$ the smallest possible degree of a finite coefficient field
at these two simultaneous endpoints is
$$
 \boxed{72{,}960=19\cdot 3{,}840}.
$$
The displayed degree is a **field** minimum, not a minimum number of
physical stages. The attainment uses the published 153-stage upper
construction at order 20.

Here a finite coefficient field is a finite extension of $\mathbb Q$
containing every entry of $A$ and $b$. We may compare these fields
inside a common algebraic closure. For a larger characteristic-zero
field the necessary containment means that it contains the corresponding
copy of the compositum as a subfield.

## 1. What the two endpoints force

The bush order conditions give a quadrature exact through degree
$2q-1$ for uniform integration on $[0,1]$, using the aggregate weights.
There must be at least $q$ contributing clocks: the $q$ by $q$ moment
matrix with entries $1/(i+j+1)$ for $0\le i,j<q$ has rank $q$,
by positive definiteness over $\mathbb R$ and hence nonzero rational
determinant. The discrete moment matrix is a sum of one rank-one
matrix per contributing clock.

If there are exactly $q$ such clocks, their monic nodal polynomial $h$
of degree $q$ satisfies
$$
 \int_0^1 h(x)u(x)\,dx=0\qquad(\deg u\le q-1).
$$
Indeed the product is paid and vanishes at every contributing clock.
The same invertible moment matrix determines the lower coefficients
of $h$ uniquely over $\mathbb Q$. Thus $h$ is the monic shifted
Legendre polynomial. Its splitting field equals $E_q$ because the
change of coordinate from $[-1,1]$ to $[0,1]$ is rational affine.
The clocks are actual row sums of $A$, so they force $E_q$ in any
coefficient field. The uniquely determined Gaussian aggregate weights
lie in $E_q$ by the Vandermonde solve. No positivity is needed in the
necessity argument.

The [sharp-depth theorem](PROOF.md) forces
$L_{2q-1}^{(1)}(1/\gamma)=0$ at depth $p-2$. As $\gamma$ is an entry
of $A$, the coefficient field must also contain $K_\gamma$.
The rest of the proof pays the degree of these **two** requirements
together, not just their separate lower bounds.

## 2. Even-order disjointness using one local Eisenstein factor

Set $n=2q-1$ and let $F_n$ be the monic normalization of
$L_n^{(1)}$. Its coefficients are
$$
 [X^j]F_n=(-1)^{n+j}\frac{n!}{j!}\binom{n+1}{j+1}
 \qquad(0\le j\le n).
$$
The [classical theorem of Schur](https://doi.org/10.1515/crll.1931.165.52)
gives irreducibility of this parameter-1 Laguerre polynomial over
$\mathbb Q$; see also the attribution in
[Hajir](https://ftp5.gwdg.de/pub/EMIS/journals/JTNB/2005-2/article6.pdf#page=2).
Only irreducibility, not Schur's more detailed group description,
is used here.

Choose a prime $\ell$ with $q<\ell<2q$ by Bertrand's postulate.
Then $\ell\le n$ and $n+1<2\ell$. The following is the complete
coefficient valuation ledger needed at $\ell$:

* The constant coefficient is $(-1)^n(n+1)!$, of valuation one.
* If $j<\ell$, the factor $n!/j!$ is divisible by $\ell$, and the
  binomial coefficient is integral.
* At $j=\ell$, the factor $n!/\ell!$ is an $\ell$-adic unit.
  In $\binom{n+1}{\ell+1}$, numerator and first denominator factorial
  have valuation one, and the remaining factorial $(n-\ell)!$
  has valuation zero. Thus this coefficient is a unit.

Consequently $F_n$ reduces to $X^\ell U(X)$ in $\mathbb F_\ell[X]$,
where $U(0)\ne0$. Hensel factorization over $\mathbb Z_\ell$ separates
a monic factor of degree $\ell$ reducing to $X^\ell$, with a second
factor whose constant term is a unit (if $\ell=n$, the second factor
is simply 1). The first factor has constant valuation one, so is
Eisenstein over $\mathbb Q_\ell$.

Let $L$ be the splitting field of $F_n$ over $\mathbb Q$, with
Galois group $G$. A completion of $L$ at a place over $\ell$ contains
a root of that Eisenstein factor, an extension of local degree
$\ell$. The completion degree is the order of a decomposition
subgroup of $G$, so $\ell$ divides $|G|$. Cauchy's theorem supplies
an element of order $\ell$. Since $G$ acts faithfully on the $n$
roots and $\ell>n/2$, this element acts as one $\ell$-cycle.

Both $E_q$ and $L$ are Galois. The subgroup
$$
 N=\operatorname{Gal}(L/(L\cap E_q))
$$
is normal in $G$, with index dividing $[E_q:\mathbb Q]$, which
divides $q!$. Hence the $\ell$-cycle belongs to $N$.
The transitive action of $G$ on the roots permutes the $N$-orbits
transitively, so their sizes are equal. One orbit contains the
entire $\ell$-cycle, and $\ell>n/2$ forces that orbit to be all the
roots. Finally the image of $\operatorname{Gal}(LE_q/E_q)$ on $L$
is exactly $N$: the elements of $L$ fixed by that image are
precisely $L\cap E_q$. This proves that $F_n$ stays irreducible
over $E_q$. As $1/\gamma$ is one of its roots, the degree of
$E_qK_\gamma$ over $E_q$ is $n$ as claimed. This proves linear
disjointness of the diagonal **root field** and the Gaussian
splitting field; it does not need a claim about the two full
splitting fields being disjoint.

## 3. The degree of the order-20 Gaussian field

Using the [Legendre coefficients](https://dlmf.nist.gov/18.5), write
$$
 256P_{10}(X)=H(X^2),\qquad
 H(Y)=46189Y^5-109395Y^4+90090Y^3-30030Y^2+3465Y-63.
$$
For example the exact coefficients of $H$ follow by dividing
each coefficient $(-1)^j\binom{10}{j}\binom{20-2j}{10}$ by 4,
for $0\le j\le5$ in decreasing degree. We show
$\operatorname{Gal}(P_{10}/\mathbb Q)=C_2^5\rtimes S_5$.

**Quintic quotient.** The reciprocal $R(Z)=Z^5H(1/Z)$ is
Eisenstein at 11: its coefficient valuations in increasing degree
are $(1,1,1,1,1,0)$. Thus $H$ is irreducible over $\mathbb Q$.
The squarefree reduction at 41 is
$$
 H(Y)\equiv23(Y+20)(Y+30)(Y+31)(Y^2+31Y+10)
     \pmod{41}.
$$
The three linear roots are distinct, and the quadratic discriminant
is $19\bmod41$, a nonsquare since $19^{20}\equiv40\bmod41$.
The leading coefficient is a unit at 41, so Hensel lifting over an
unramified extension and its residue Frobenius give a transposition
in the quintic Galois group. Explicitly, Frobenius fixes the lifts
of the three linear roots and exchanges the two lifts of the
quadratic roots. It restricts to an automorphism of the global
splitting field embedded in a local algebraic closure.

The group on the five roots is transitive by irreducibility.
Make a graph of all transpositions conjugate to the one just found.
The group acts transitively on the vertices and permutes its
connected components. They have equal sizes dividing five, and
at least one edge is present, so the graph is connected.
Transpositions along a connected graph generate $S_5$.
This proves the quotient on the five squared roots is $S_5$.

**One independent sign change.** At 19, the reduction in the
original variable loses its leading term and is
$$
 H(Y)\equiv(Y+14)C(Y),\qquad
 C(Y)=7Y^3+8Y^2+11Y+5 \pmod{19}.
$$
It is squarefree and has nonzero constant: $C(5)=14$, while
$C'(Y)=2(Y+3)(Y+5)$ and $C(-3)=7$, $C(-5)=16$ in
$\mathbb F_{19}$. Thus the reciprocal has one simple zero root
and four simple nonzero roots over the residue algebraic closure.
The constant coefficient of $R$ has valuation one because
$46189=11\cdot13\cdot17\cdot19$; its linear coefficient
$-109395$ is a unit at 19.

Lift the reciprocal roots in a finite unramified extension of
$\mathbb Q_{19}$ whose residue field contains them. The unique
root $z$ lifting zero has valuation exactly one: if it had
valuation greater than one, the constant term of $R(z)$ would
be the unique term of least valuation. The other four reciprocal
roots are units. Therefore, of the five original squared roots
$Y_i$, one has valuation $-1$ and the other four are units.
After a further unramified extension the four units have square
roots, by lifting their nonzero residue square roots (19 is odd).
The remaining square root must generate a ramified quadratic
extension, since its valuation is $-1/2$. Its nonidentity
inertia element fixes the four unit square-root pairs and changes
the sign of just the remaining pair. It fixes $\mathbb Q$,
permutes the ten roots, and so restricts to a single sign change
in the embedded global splitting field.

Every global permutation respects the pairs $\{\pm\sqrt{Y_i}\}$.
It acts on the pairs through the full $S_5$ quotient above, since
the splitting field of $H$ is a Galois subfield. Conjugating the
single sign change by lifts of these permutations supplies all
five coordinate flips. Thus the full sign kernel is $C_2^5$ and
$$
 [E_{10}:\mathbb Q]=2^5\cdot5!=3840.
$$
As an optional smaller check, the product of one root from each
pair has square $63/46189$, so $E_{10}$ contains
$\mathbb Q(\sqrt{323323})$.

For $n=19$, the general valuation ledger with $\ell=19$
already makes the full monic Laguerre polynomial Eisenstein at
19. So $[K_\gamma:\mathbb Q]=19$ independently of Schur's theorem
in this case. Its degree is coprime to 3840; either coprime-degree
composition or Section 2 gives the exact degree 72,960.

## 4. Attainment and scope

Use the $q$ Gaussian nodes and their uniquely determined weights
in $E_q$. The [published quadratic stage construction](QUADRATIC-STAGE-BOUND.md),
Sections 3 and 4, uses only field operations: each strict row is
built from cardinal polynomials on a submesh, evaluated formal
integrals, and terms linear in $\gamma$. The resulting tableau has
all coefficients in $E_qK_\gamma$. Its last layer has the original
Gaussian clocks and weights and all earlier layers have zero
output weights. The Gaussian weights are positive at the real
embedding (each is the integral of the square of its cardinal
polynomial), so precisely the $q$ Gaussian clocks contribute.

On the shallow branch that construction has depth $p-2$ and
exact order $p$, by the first failing next tall tree. At order
20 its stage count is at most $10\cdot20-\binom{10}{2}-2=153$.
As the tableau contains $\gamma$ and all ten contributing clocks
in its actual coefficients and row sums, its generated
coefficient field is exactly the compositum, not merely a
subfield of it. Any other finite coefficient field satisfying
both endpoints has degree a multiple of 72,960. The result
makes no stage minimum, stability, or claim under a different
notion of clock support.
