# Quadratic elimination for a rational sixteen-stage ERK10 chart

The chart uses an eight-stage dense-order-five prefix and nine reverse rows,
with the common endpoint row merged. A special reverse row at clock zero
takes the zero-clock mass, and one other reverse donor has zero weight. This
gives a new rational construction criterion. It does not give a
sixteen-stage rational tableau.

**Exact exclusion.** In the regular rank-three late-helper chart below,
there is no rational choice of the other clocks, the dense endpoint
horizon, or the free taps when the late clocks \(d,e,\xi\) are integral at
29 and reduce to \(18,19,22\) respectively, up to exchanging \(d\) and \(e\).
For example the triple \((-1/8,8/5,1/4)\) is excluded. The calculation
allows arbitrary rational poles at 29 in the remaining donor and the
horizon. This is an exclusion within the stated reverse-moment construction,
not a lower bound on unrestricted ERK10.

## The distinct clock-zero and zero-weight donors

Use the raw reverse chronology
\[
 \boldsymbol x=(1,0,a,b,h,z,d,e,\xi)^\top .
\]
All clocks are distinct, and the weight at \(h\) is zero. The other eight
clocks carry the signed cardinal-integral weights of a scalar quadrature
through degree nine. For the constructive solves the weights at the first
1 and at \(a,b,z\) must be nonzero. Any nonzero portion of the scalar zero-clock mass may
be placed at raw clock zero, with the rest on the old prefix origin.
Set \(y_i=1-x_i\) and \(M_{j,i}=w_i y_i^j\). The strictly lower triangular
raw matrix \(K\) is required to pay
\[
 K\boldsymbol w=\boldsymbol M_1,\quad
 K\boldsymbol M_1=\boldsymbol M_2/2+\boldsymbol U,\quad
 K\boldsymbol M_2=\boldsymbol M_3/3+\boldsymbol G,\quad
 K\boldsymbol U=\boldsymbol H.
\]
The seven distinct nonzero sites other than the initial 1 have a
one-dimensional cofactor annihilator of \(X,\ldots,X^6\). Its vector
\(\boldsymbol V\) has there the entries
\[
 V_x=\frac{1}{x\prod_{u\ne x}(x-u)}
\]
where the product runs over the other six sites in that set. Set its two
entries at the initial 1 and raw 0 to zero. The seven tests through
\(X^7\) force \(\boldsymbol U\) to live only at raw zero, where
\(U_1=-w_1/2\). The forward construction uses
\(\boldsymbol G=(2/3)\boldsymbol U+g\boldsymbol V\) and
\(\boldsymbol H=j\boldsymbol V\). At the first weighted off site \(a\), set
\(p=1-a\), \(q=1-b\). The actual first reads give
\[
 G_a=w_a p^2/2-w_a p^3/3,\qquad H_a=-w_a p^2/4 .
\]
At the next weighted site \(b\), the four reads are compatible exactly when
\[
 \mu_b(b-h)q(3p-2q)=\mu_a(a-h)p^2,\qquad
 \mu_x=\int_0^1\prod_{u\in\{0,1,a,b,z,d,e,\xi\}\setminus\{x\}}(X-u)\,dX .
\]
This is linear in the helper clock \(h\).

The zero-weight helper cannot precede the first two weighted off sites
in this cofactor architecture. Before the first, its received
second-defect action is zero, which forces \(j=0\) and contradicts
\(H_a\ne0\). Immediately after the first, its three possible effective
donors force \(G_h+2(1-p)H_h=0\); but the first weighted site gives
\(G_a+2(1-p)H_a=w_a p^3/6\ne0\). Since both profiles have the same
nonzero cofactor values at \(a,h\), this is contradictory.
The [kernel scalar receipts](../../lean/RKCert/ReviewedNative/ERK10LateHelperGate.lean)
include both the last forced relation and its conflict with the first
weighted donor.

## The only terminal test that constrains the late triple

In the doubled-clock dense-prefix chart the size-six defects are the
kernel of a functional \(\ell\) on \(X(X-\xi)\mathbb Q[X]_{\le3}\).
For a regular dense endpoint \(\theta\ne0,2\), put
\[
 v=\frac{\theta(12\theta^2-45\theta+40)}{15(\theta-2)^2},
 \qquad
 \ell(f)=f(\xi v/\theta)-
      \frac{v^3(3v^2-15v+20)}{16} f(2\xi/\theta).
\]
As usual, this rank-three chart excludes \(v=0,2\); the quadratic
\(3\theta^2-15\theta+20\) has no rational root. The
[rank-three prefix packet](../erk10-canonical-dense-rank3/README.md)
gives the literal paid \(\theta=5/2\) ingredient. Here the horizon is not
fixed. The scalar pressure proof uses the displayed functional, not a
claim that every dense prefix or literal order-ten tableau has this form.

Let \(\boldsymbol k=K\boldsymbol M_3-\boldsymbol M_4/4\). On the four
fixed donors \(1,0,a,b\) one has the pointwise identity
\[
 \boldsymbol M_3=(p+q)\boldsymbol M_2-pq\boldsymbol M_1
                  -2(1-p)(1-q)\boldsymbol U.
\]
A base row using those donors therefore pays its \(\boldsymbol k\)
test by the polynomial
\[
 L(Y)=(p+q)Y^3/3-pqY^2/2-Y^4/4.
\]
Indeed, the difference from \(\boldsymbol w\odot L(\boldsymbol y)\)
is a linear combination of \(\boldsymbol U,\boldsymbol G,\boldsymbol H\)
and disappears against tests of degree at most five vanishing at zero.
The same cubic identity holds for the extra helper donor, since every
\(\boldsymbol M_i\) and \(\boldsymbol U\) vanishes at it. Consequently
every raw matrix paying the four reads has identical tests on
\[
 f_4=X(X-\xi)(X-d)(X-e),\qquad f_5=Xf_4:
 \qquad \boldsymbol k\cdot f_j(\boldsymbol x)
         =\kappa(f_j):=\int_0^1 f_j(X)L(1-X)\,dX.
\]
The only rows which can change their cubic read are \(d,e,\xi\),
and the two tests vanish there. All used scalar integrands have degree
at most nine.

Terminal payment of \(\boldsymbol k\) means that it annihilates
\(\ker\ell\). It requires
\(\kappa(f_4)\ell(f_5)-\kappa(f_5)\ell(f_4)=0\).
Conversely, when the two \(\ell\) values do not both vanish, this
identity is sufficient for the \(\boldsymbol k\) payment: either
late row \(d,e\) may independently use a compensated tap to \(z\),
whose unmatched cubic read is
\(w_z(1-z)((1-z)-p)((1-z)-q)\ne0\).
Separately the helper column can change \(K\boldsymbol V\) at
\(z,d,e\) without changing any of those reads. This pays the three
remaining cofactor tests whenever the evaluation on \(z,d,e\)
is invertible on \(\ker\ell\), equivalently
\(\ell(X(X-\xi)(X-z)(X-d)(X-e))\ne0\).
These are precise conditions for reusing the late-helper chart, not
assumed in the exclusion proof. For sufficiency through order ten, use
the same [marked-source attachment and physical merge](../erk10-sixteen-17-power-lift/README.md)
with the high forward block given by reversing the transpose of \(K\).
The prefix is exact through size five. Through order ten a rooted product
contains at most one source of size six or higher. Its exterior reverse
word has length at most three. Through length two the only new errors are
\(\boldsymbol U,\boldsymbol G,\boldsymbol H\), all paid by the stated
monomial moments. At length three, multiplication by \(1-X\) leaves
\(\boldsymbol U\) unchanged, and the new actions
\(K\boldsymbol G,K\boldsymbol H\) lie in the span of
\(\boldsymbol H,K\boldsymbol V\). Thus the two terminal payments suffice
for these marked words. A concrete solution would still need a separate
order-eleven failure certificate to claim exact order ten.

## Exact quadratic and modular exclusion

Write \(S=a+b,\ P=ab\) and
\[
 U(X)=X(X-1)(X-d)(X-e)(X-\xi),\qquad
 m_i(z)=\int_0^1 X^i U(X)(X-z)\,dX .
\]
The precision-nine scalar rule implies
\(m_2-Sm_1+Pm_0=m_3-Sm_2+Pm_1=0\).
Without dividing by any determinant, these give
\[
 \Delta S=N_S,\quad\Delta P=N_P,\qquad
 \Delta=m_0m_2-m_1^2,\quad
 N_S=m_0m_3-m_1m_2,\quad N_P=m_1m_3-m_2^2 .
\]
All three are quadratic in \(z\). The terminal pressure is affine in
\(S,P\) since \(p+q=2-S\) and \(pq=1-S+P\).
Thus any solution satisfies \(C_0\Delta+C_1N_S+C_2N_P=0\),
where the \(C_i\) are the corresponding normalized terminal coefficients.
This remains necessary even at \(\Delta=0\).
For constructive search when \(\Delta\ne0\), solve this quadratic in
\(z\), then check whether \(S^2-4P\) is a rational square.

The [exact replay](replay.py) cancels common factors from \(\ell\) on
\(X(X-\xi)\mathbb Q[X]_{\le3}\) before using projective coordinates.
If \(T\) denotes the horizon, put \(N=12T^2-45T+40\),
\(D=15(T-2)^2\), \(B=3T^2-15T+20\), \(E=TN-2D\), and
\(W=3T^2N^2-15TND+20D^2\). On a basis element
\(X^{j+1}(X-\xi)\), the normalized functional has value
\[
 \xi^{j+2}
 \frac{-8T^2D^{3-j}N^{j+1}-2^jT^{3-j}(2-T)N^3W/B}{NE},
 \quad j=0,1,2,3 .
\]
Polynomial division is exact and only divides by constants prime to
29. This is the original functional multiplied by
\(8T^2D^5/(BNE)\), which is nonzero in this regular rational chart.
No clock-dependent content is removed. The integrations likewise
only divide by \(1,\ldots,10\).

For \((d,e,\xi)\equiv(18,19,22)\pmod {29}\), the resulting pressure
polynomial of bidegree at most \((9,2)\) reduces to
\[
 A(T)(z^2+23z+21),\qquad
 (A_i)_{i=0}^9=(4,7,20,1,24,10,20,12,20,20).
\]
The projective homogeneous form of \(A\) is nonzero at all 30 points
of \(\mathbb P^1(\mathbb F_{29})\), and so is that of the quadratic.
Primitive rational numerator-denominator pairs for \(T,z\) each
reduce to a nonzero projective pair, including when a denominator
is divisible by 29. The product is therefore nonzero, ruling out
every rational solution in the stated late residue class. The
same local obstruction holds for a valued field with residue
\(\mathbb F_{29}\) and the same regular chart.

## Replay and formal scope

    python3 -B replay.py
    sha256sum -c sha256.txt

The rational profile-to-polynomial proof and exact coefficient extraction
are separate from the small Lean algebraic receipts. The
[projective kernel check](../../lean/RKCert/ReviewedNative/ERK10LateHelperMod29.lean)
proves that neither homogeneous factor has a zero in the relevant finite
charts, including infinity. The column move, cubic-read identity, and
cleared pair elimination theorems in the sibling module are over arbitrary
commutative rings. They do not assert that an arbitrary literal HasOrder
tableau must come from this construction.
