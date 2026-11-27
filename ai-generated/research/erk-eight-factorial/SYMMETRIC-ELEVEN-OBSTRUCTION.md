# Why simply deleting the duplicated clock cannot give a rational eleven-stage chart of this type

This is an architecture-specific obstruction, not an eleven-stage ERK lower bound. Use the same active sites \(0,a,\tfrac12,d,1-d,f,1\), with \(f=1-a\), as in [the twelve-stage construction](README.md). Assume the sites are pairwise distinct, now with only one physical slot at \(f\), and retain the same output and reverse-read requirements.

A single stage at \(f\) has only one later receiver, at 1, so \(D_f=B_f\). Set \(P_f=x(x-a)(x-\tfrac12)(x-d)(x-1+d)\); this degree-five polynomial vanishes at all nonterminal active donor sites other than \(f\). The last column of each of \(B,D\) is zero. Their paid moments and the equality \(D_f=B_f\) therefore imply
\[
  0=\int_0^1 [\mu_1-\mu_0]P_f(x)\,dx
    =-\frac12\int_0^1 (1-x)^2 P_f(x)\,dx
    =\frac{a(7d^2-7d+1)}{1680},
\]
where \(\mu_1=(1-x^2)/2,\ \mu_0=1-x\). Distinctness gives \(a\ne0\). The resulting quadratic in \(d\) has discriminant 21, so it has no rational root. Consequently this symmetric chart cannot simply lose its duplicate physical clock over \(\mathbb Q\) or \(\mathbb Z[1/210]\).

The [stronger four-tap obstruction](FOUR-TAP-ELEVEN-OBSTRUCTION.md) also handles nonsymmetric and repeated clocks under the stated hypotheses. Neither result excludes other simplifying assumptions or the unrestricted rational eleven-stage problem.
