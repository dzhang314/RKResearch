# Three-coefficient form of the external fourth and fifth reads

This is an equivalent reduced implementation of the necessary read gates in the [external-root note](README.md#2-exact-fourth-and-fifth-read-conditions), not a nonexistence proof. Keep the same \(D\), external root \(\rho\), ordinary mean \(I_D\), and Cauchy functional \(\Lambda_\rho\). In a live star one may use the degree-six effective mask \(R\) in \(\Lambda_\rho\) instead of \(P_8\), by the gap cancellation in the note. Let \(P\) denote \(P_8\) in a finite-gap phase or this effective \(R\) in the star, so
\[
 \Lambda_\rho(F)=P(\rho){\cal C}_F(\rho)-{\cal C}_P(\rho)F(\rho),\qquad
 P(\rho)\ne0 .
\]

The two cases are:

| Read being tested | Actual supported input \(\eta\) | Previous zero clocks | Test clock \(x\) |
|---|---|---|---|
| fourth | \(\sigma=(T-a)(T-b)(T-c)\) | \(a,b,c\) | \(d\) |
| fifth | \((T-d)\sigma(T)\) | \(a,b,c,d\) | \(e\) |

The preceding physical inputs vanish (as do the two off-row inputs). Put \(W=(C'-\rho I)(A'\boldsymbol\eta-(J\eta)(\mathbf x))|_U\), representing its trace by a polynomial of degree at most \(\deg\eta+2\). Then the actual image \((C'-\rho I)A'\boldsymbol\eta|_U\) has trace \(W(T)+(T-\rho)J\eta(T)\). This polynomial vanishes at all the preceding labels. Their monic polynomial is exactly \(\eta\); hence the trace is \(\eta(T)Q(T)\) for a quadratic \(Q=q_0+q_1T+q_2T^2\), possibly of lower degree. The actual tested diagonal requires \(Q(x)=x-\rho\), since \(\eta(x)\ne0\).

Therefore the following are linear equations in \(q_0,q_1,q_2\):
\[
 \begin{aligned}
 I_D(T^j\eta Q)&=I_D(T^j(T-\rho)J\eta)
     &&(0\le j\le 5-\deg\eta),\\
 \Lambda_\rho(\eta Q)&=P(\rho)I_D(J\eta),\\
 Q(x)&=x-\rho .
 \end{aligned}
\]
The Cauchy equation uses \(\Lambda_\rho((T-\rho)J\eta)=P(\rho)I_D(J\eta)\), with no division by a clock difference other than the exact divided polynomial. For implementation, the primitive means on the right are reducible to elementary moments by the monomial identity
\[
 I_D(T^k J\eta)=
    [D^{k+1}I_D(\eta)-I_D(T^{k+1}\eta)]/(k+1).
\]
All formal means in the tests stay within the ordinary degree-seven range.

Before the final diagonal row, the coefficient matrix has rank three in an actual tableau: a homogeneous \(Q\) would give a pure trace \(\eta Q\) in the corresponding Cauchy kernel, vanishing at the previous literal reads, contradicting their detection of \(F_4|_U\) or \(F_5|_U\) unless \(Q=0\). In particular the fifth test can use one four-by-four augmented determinant, rather than the five-mode interpolation fit. The fourth test can use the four-by-four minors of its five augmented rows. The nonzero-rank justification is chronological, not just a check at a sample node or coefficient specialization.
