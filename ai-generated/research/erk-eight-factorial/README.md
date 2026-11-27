# Twelve explicit stages suffice for exact order eight over every factorial-admissible ring

A [later eleven-stage rational construction](../erk-eight-rank3-four/README.md) succeeds outside the restricted architecture studied here.

Let \(R\) be a nonzero commutative unital ring. The order-eight equations force \(8!\) to be a unit by the tall tree. Conversely, if \(8!\) is a unit, the twelve-stage tableau below has exact order eight over \(R\). It improves the [general-ring thirteen-stage upper](../erk-eight-ring-witness/README.md) by one and supersedes the scope-specific [positive-characteristic and field cover](../erk-eight-finite-characteristic/README.md) at twelve stages. It is not a new lower bound and does not improve the real-algebraic upper of eleven.

## Tableau and exactness

The row entries are in chronological predecessor order.

| Stage | Strict predecessor coefficients |
|--:|:--|
| 1 | none |
| 2 | \(2/27\) |
| 3 | \(1/36,\ 1/12\) |
| 4 | \(1/24,\ 0,\ 1/8\) |
| 5 | \(296/1029,\ 0,\ -352/343,\ 384/343\) |
| 6 | \(11/196,\ 0,\ 0,\ 32/147,\ 1/84\) |
| 7 | \(19/512,\ 0,\ 0,\ 41/120,\ 539/1536,\ -147/640\) |
| 8 | \(-1157/32,\ 0,\ 0,\ 1858/15,\ 5243/96,\ -5733/40,\ 0\) |
| 9 | \(-607/4,\ 0,\ 0,\ 7456/15,\ -1715/12,\ -15778/45,\ 448/3,\ 8/9\) |
| 10 | \(25939/76832,\ 0,\ 0,\ -398/735,\ 53/672,\ 1291/2520,\ 2368/7203,\ -58/21609,\ 9/9604\) |
| 11 | \(10387/76832,\ 0,\ 0,\ -398/735,\ 53/672,\ 3091/2520,\ -3392/7203,\ 32/21609,\ -11/9604,\ 2/7\) |
| 12 | \(-325/672,\ 0,\ 0,\ 122/63,\ -91/288,\ -329/324,\ 32/189,\ 1/378,\ 11/13608,\ 0,\ 343/486\) |

\[
b=\left(\frac7{80},0,0,0,0,\frac{16807}{38880},-\frac{16}{405},
        -\frac1{38880},-\frac1{38880},\frac{16807}{77760},
        \frac{16807}{77760},\frac7{80}\right).
\]
The clock vector \(A\mathbf1\) is \( (0,2/27,1/9,1/6,8/21,2/7,1/2,-1,2,5/7,5/7,1)\). Two nodes are outside the unit interval. This result concerns order and physical width, not stability or positivity.

The common denominator \(1493614080=2^9 3^5 5\cdot7^4\) divides \((8!)^4\). All order-eight identities therefore specialize along the canonical map \(\mathbb Z[1/210]\to R\). For a tree \(t\), write \(e_t=t!\,b^\top\Phi_t(A)-1\). In the tableau the ninth-order bush and tall tree have residuals
\[
    e_{\rm bush}=-263/27440,\qquad e_{\rm tall}=362/735.
\]
Neither residual individually has to be nonzero in all admissible coefficient rings. Instead, the integer Bézout identity
\[
       -117\cdot27440\, e_{\rm bush}-85\cdot735\, e_{\rm tall}=1
\]
shows they cannot both vanish after any specialization into a nonzero ring. This proves exactness without cancelling a possible zero divisor.

## Construction: a fourth reverse read separates two physical rows at the same clock

The construction retains the simplifying pattern of the [classical Shanks tableau](https://doi.org/10.1090/S0025-5718-1966-0187406-1) but redesigns its clocks and coefficients. Denote the clock diagonal by \(C\), and let \(r_j=Ac^{j-1}-c^j/j\) denote the primitive residual at degree \(j\). Here powers of a vector are coordinatewise. Impose \(b_2=\cdots=b_5=0\), column 2 empty below stage 3, column 3 empty below stage 5, \(r_2,r_3\) supported only on stage 2, and \(r_4\) supported on stages \(2,3,4,5\). In particular all rows with nonzero weight are exact primitives through degree four.

On the seven distinct active sites \(0,a,1/2,d,1-d,f,1\), \(f=1-a\), symmetry makes the seven interpolated quadrature moments through degree six imply degree seven. Split the weight at \(f\) between stages 10 and 11. The desired reverse reads are
\[
 B=b^\top A=b^\top(I-C),\qquad D=b^\top C A,\qquad E=b^\top C^2 A,\qquad F=DA .
\]
They are supported on the active clocks. The first three integrate polynomials through degrees \(6,5,4\) against the respective densities \(\mu_0=1-x,\ \mu_1=(1-x^2)/2,\ \mu_2=(1-x^3)/3\). The fourth integrates through degree four against \(\int_x^1\mu_1(y)\,dy=(2-3x+x^3)/6\).

For donors 9, 10, and 11 the only later receiver clocks are \(f,1\), so
\[
  E_j=(1+f)D_j-f B_j .
\]
Choose \(D\) by interpolation on the six active donor sites excluding 1, splitting its component at \(f\) so \(D_{11}=B_{11}\). Prescribe \(E\) by its five moment equations and the displayed relation at slots 10 and 11. To enforce the relation also at slot 9, require
\[
  \int_0^1 [\mu_2-(1+f)\mu_1+f\mu_0]\,x(x-a)(x-1/2)(x-d)\,dx=0 .
\]
With \(f=1-a\) this gives exactly \(d=a/(21a^2-14a+2)\). The last two components of \(F\) vanish. Chronology fixes \(F_{10}\) from \(D_{11}A_{11,10}\); the other five active components follow from its moments.

The head clocks \(x=c_4,\ y=c_5\) must allow the first active row to integrate through degree four using only the three predecessors with clocks \(0,x,y\). This means \(\int_0^a t(t-x)(t-y)\,dt=0\), so \(y=a(4x-3a)/(2(3x-2a))\). The next two prefix rows use four donors \(0,x,y,a\), with the optional tap \(A_{8,7}\) set to zero. In the four remaining receiver rows, the three reads \(B,D,E\) cannot distinguish the two equal clocks \(f\), but \(D_{10}/b_{10}\ne D_{11}/b_{11}\) lets the additional read \(F\) distinguish them. Thus four linear equations per donor determine the remaining strict entries, with the displayed compatibility for the shorter last columns. The choice \(a=2/7,\ x=1/6,\ d=-1\), and equal output-weight splitting at \(f=5/7\), pays all divisions using only \(2,3,5,7\). Here \(D_{10}/b_{10}=10/49\) and \(D_{11}/b_{11}=14/49\), so the equal-clock separation itself is by a unit.

### Why these reverse reads pay the rooted conditions

For a tree \(t\) of size \(n\), its stage defect is its elementary weight vector minus \((n/t!)c^{n-1}\). Unary graft transforms a defect by \(A\) plus the corresponding primitive residual \(r_n\) times \(n/t!\). Root merge multiplies stage weights coordinatewise, so it adds two clock-shifted terms and one product of defects.

Defects through sizes 3, 4, and 5 lie respectively in the spans of \(\{e_2\}\), \(\{e_2,e_3\}\), and \(H=\operatorname{span}\{e_2,e_3,e_4,e_5\}\), where the \(e_i\) here are stage coordinate vectors. Let \(W=\operatorname{span}\{Ae_4,Ae_5,r_5\}\). The sixth-order defects lie in \(H+W\). At order seven only \(A W,C W,r_6\) need be added; at order eight the further vectors are in \(A^2W, ACW,CAW,C^2W,\operatorname{span}\{Ar_6,Cr_6,r_7\}\). Products of two defects up to order eight have at least one factor of order at most four and so stay in \(H\). The stipulated taps annihilate these spaces under \(b^\top\). In particular
\[
 b^\top CW=b^\top C^2W=0,\qquad b^\top CAW=DW=0
\]
by the moments of \(D,E,F\) and their head silence; the leading \(A\)'s then drop by \(b^\top A=b^\top(I-C)\). The conditions on \(r_6,r_7\) follow from the scalar moments of \(b,B,D\). Thus outputting the exact polynomial part gives every tree order condition. The literal certificate below does not require the symbolic derivation.

## Verification

Run **python3 check.py** in this directory. The standard-library replay independently checks all 200 rooted conditions on unlabeled non-plane trees, both ninth-order residuals and their Bézout identity.

The [Lean proof](../../lean/RKCert/ReviewedNative/ERK8FactorialTwelve.lean) checks all 626 reviewed constructor trees through order eight using integer-pair arithmetic and connects the result to the reviewed **HasOrder** and **ERK** predicates. Its theorem **RKResearch.Certified.ERK8FactorialTwelve.exact_order_eight_iff** is for arbitrary nontrivial commutative rings. In the configured Lean project:

    lake build RKCert.ReviewedNative.ERK8FactorialTwelve

The proof was kernel checked with Lean/Mathlib 4.36.0; only the standard axioms propext, Classical.choice and Quot.sound were reported.


## Eleven-stage rational restriction

The [four-tap obstruction](FOUR-TAP-ELEVEN-OBSTRUCTION.md) excludes the
specified head-silent eleven-stage architecture over the rationals. The
[symmetric chart calculation](SYMMETRIC-ELEVEN-OBSTRUCTION.md) isolates
the irrational clock condition in that subcase. Neither result excludes
unrestricted eleven-stage rational ERK tableaux.
