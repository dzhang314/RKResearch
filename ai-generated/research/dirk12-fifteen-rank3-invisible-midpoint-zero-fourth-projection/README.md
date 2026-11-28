# DIRK12/15: the midpoint first-root branch has a degree-36 coefficient field

In the two actual early reverse charts of the real ordinary fifteen-stage order-twelve \(C(2),f_5=3\) invisible four-dirty-ghost frame, set the first nonzero ordinary live clock to \(a=1/2\). This is a first Legendre root. The [fourth-diagonal exclusion](../dirk12-fifteen-rank3-invisible-nonzero-fourth-exclusion/README.md) requires the fourth live nonzero diagonal to be zero. The [terminal repeat exclusion](../dirk12-fifteen-rank3-invisible-nine-site-fourth-terminal-exclusion/README.md) and the actual ten-site early-zero chronology make every first-five ordinary live nonzero clock different from 1.

Under these hypotheses all possible second ratios \(x=b/a\) belong to one verified irreducible degree-36 polynomial. The third and fourth ratios \(y=c/a,t=e/a\) are unique rational elements of its coefficient field, and the fifth physical clock satisfies a monic cubic over that field. A further orientation quadratic suffices for the unique unordered reverse support; the maximum rank of the remaining scalar candidate algebra is \(36\cdot3\cdot2=216\). This finite coefficient projection does not assert existence or exclude the degree-36 factor. It does not address other first Legendre roots or first nonroots. The overall real DIRK12 interval remains **15–16**.

## Paid quadratic and cubic from the zero fourth diagonal

In normalized ordinary units \(T=X/a\), let \(P_0=T(T-1)(T-x)(T-y)\) and write the true first-root live-only operator \(\mathcal A(F)=JF-r\,\mathcal I(F)-k[\mathcal I(TF)-\epsilon[T^5]F]\) as in the [geometry-free first-root proof](../dirk12-fifteen-rank3-invisible-all-ordinary-prefixes/README.md). Put \(I_i=\mathcal I(T^iP_0)\), \(K_1=I_2-\epsilon\) and \(\Delta=I_0K_1-I_1^2=-(5x^2-5x+1)D/10800\), where \(D=2xy-x-3y^2+2y\). The diagonal-zero condition gives literal \(\mathcal A(P_0)(t)=\mathcal A(TP_0)(t)=0\). Solving for the two mode values produces
\[
 k_0(s)=\frac{I_0J(TP_0)(s)-I_1JP_0(s)}{\Delta},\qquad
 r_0(s)=\frac{K_1JP_0(s)-I_1J(TP_0)(s)}{\Delta}.
\]
The actual \(k(s)\) is its fixed \(L_6'\) scalar multiple. The actual \(r(s)\) is the unique combination of \(sL_5'(as),sL_6'(as),sL_7'(as)\) matching the known reads on \(1,x,y\), with the third read \(r_0(y)\). The three-mode determinant is nonzero by the [actual rank proof](../dirk12-fifteen-rank3-invisible-fifth-ordinary-live/README.md), even when one true \(k\)-read vanishes.

Both \(k-k_0,r-r_0\) are divisible by \(P_0\) on actual prefixes, by the values at \(0,1,x,y\). After clearing only the guarded denominators and removing nonzero factors in the quotient, the retained two equations have formal maximum degrees \(2,3\) in \(t\). In the second quotient the removed scalar factors are exactly the already prohibited \(x,x-1,y,y-1,x-y\). For this coefficient calculation ordinary monic Euclidean quotients can be evaluated at arbitrary \(x,y\); actual \(x,y\) make the corresponding remainders zero.

Their resultant in \(t\) is a rational constant times a single polynomial of bidegree \((27,22)\) in \(x,y\). Its resultant in \(y\) against the actual third-clock gate with the factors \(y-1,y-x\) stripped has \(x\)-degree 256. Remove powers of \(x,x-1,5x^2-5x+1\), and \(33x^4-132x^3+168x^2-72x+8\) (the last is the stripped nonzero part of \(L_6'(x/2)/(x-1)\) and the actual rank-two tap pivot excludes its zeros). The retained factors have degrees 36 and 20, with multiplicities one and two respectively.

## Exact exclusion of all four degree-20 residue fibres

Modulo 17 the degree-20 factor has degrees \(2,2,8,8\). The checked third polynomial keeps degree five and its common divisor with the bivariate resultant is linear in all four fields. The corrected degree-2/3 fourth equations have a unit leading coefficient in at least one, and their common divisor has degree two. In each base field that quadratic is irreducible; the four resulting residue field degrees are \(4,4,16,16\).

In all four fields the literal fourth commutator gate from the genuine grade-four mask \(\mathbf Q\) fails: compare the first-three interpolation of \(\bar R(\bar A\mathbf Q)\in F_7\) against its literal read at the zero-diagonal fourth row. Use the complete first-root two-source calculation, which keeps the contributions at \(b\), the direct \(c\) contribution, and the indirect \(b\to c\) tap; no assumption of a zero second diagonal is made. All stage clock, scalar and three-mode pivots are units.

The monic winning input in each fibre guarantees integrality of the corresponding coordinate of any putative characteristic-zero candidate. Thus the nonzero physical commutator residue excludes the full degree-20 branch. No coincident root or a drop of all leading coefficients is discarded by reduction.

## Remaining field and reproduction

The degree-36 factor is primitive and irreducible modulo 137 with degree retained; hence it is irreducible over \(\mathbb Q\). The exact characteristic-zero \(y\)-gcd and \(t\)-gcd over this field are both linear, giving the literal rational field elements in the data. The paid fifth equation has degree three and remains cubic after both universal split-free reverse scale tests: its gcd with the two scale-only filters is the same monic cubic in the characteristic-zero field. It does not follow that each root is real or satisfies all higher gates. The unordered reverse fit and its two possible orientations are already described by the [split-free construction](../dirk12-fifteen-rank3-invisible-split-free-grid/README.md).

    python3 -B rebuild.py          # SymPy + python-flint, exact two projection resultants
    python3 -B verify.py           # standard-library field checks on degree20, irreducibility of degree36
    python3 -B recover-field.py    # python-flint; exact y,t,f degrees and literal coordinates

The degree-20 exclusion is an exact mathematical result and independent field replay, not a full Lean stage proof. All actual higher mixed checks retain the unpaid next scalar discrepancies; none is silently set to zero.
