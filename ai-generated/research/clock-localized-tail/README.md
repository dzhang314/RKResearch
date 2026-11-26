# A localized stage vector forces one extra row in an explicit method

The linear chain bounds the number of rows after the first nonzero coordinate of a stage vector. Two families of mixed order conditions improve that bound by one when the vector is supported at a single stage abscissa and has nonzero output. The argument works over fields of positive characteristic as well as characteristic zero, provided the factorials in the statement are invertible. The [prefix consequences](WEIGHTED-PREFIX.md) explain how this additional row can improve a stage bound. The [delayed-closure theorem](DELAYED-CLOCK-CLOSURE.md) treats cases in which the tree space itself need not be invariant under multiplication by the clock. The [common-diagonal extension](COMMON-DIAGONAL.md) treats singly diagonally implicit methods with nonzero common diagonal and constant-diagonal intervals of diagonally implicit methods.

Let \(K\) be a field. Let \(A\) be strictly lower triangular in the physical stage order and \(C\) be the actual diagonal clock matrix. Let \(\beta\) be an output row, and let a stage vector \(\boldsymbol{\eta}\) be supported at a single clock \(\theta\ne1\), with \(\beta\boldsymbol{\eta}\ne0\). Fix an integer shift \(m\ge0\) and a paid word budget \(L\ge5\), with \((m+L)!\ne0\).

Assume the actual normalized scalar reverse tests through this budget are those of the weight \((1-X)^m/m!\). Precisely, replace \(A\) by \(A/(1-\theta)\), \(C\) by \((C-\theta I)/(1-\theta)\), and \(\beta\) by \(\beta/(\beta\boldsymbol{\eta})\). In these normalized coordinates the following are the only tests needed:
\[
 C\boldsymbol{\eta}=0,\quad
 \beta A^i\boldsymbol{\eta}=\mu_i,\quad
 \beta A^k C^r A^i\boldsymbol{\eta}=i^{\overline r}\mu_{i+k+r},
 \qquad
 \mu_j=\frac{m!}{(m+j)!},
 \tag{1}
\]
where the pure taps are for \(0\le i\le L\), and the mixed tests are for \(i\ge1,\ r=1,2,\ k\ge0,\ i+k+r\le L\). Here \(i^{\overline 1}=i\) and \(i^{\overline 2}=i(i+1)\). There is no assumption of vanishing first reverse residual or that the last physical clock is 1.

Let \(t\) be the actual last nonzero position of \(\beta\) and \(\ell\) the first nonzero entry of \(\boldsymbol{\eta}\). Then
\[
                              t-\ell\ge L+1 .
 \tag{2}
\]
All calculations can be done in the actual prefix ending at \(t\), since the adjoint words never read beyond it. The bare chain only gives \(t-\ell\ge L\). We exclude equality as follows.

## Further results

- [Common-diagonal resonance and prefix rank](COMMON-DIAGONAL-RESONANCE.md): a nonendpoint direction still forces the extra row even when the longest shifted moment is zero. The [prefix theorem](COMMON-DIAGONAL-PREFIX-RANK.md) and [formation argument](FORMATION-AND-CARDINAL-RANK.md) give the consequences for actual invariant subspaces.
- [The odd SDIRK endpoint is different](ODD-SDIRK-ENDPOINT-SHARP.md): an exact real-algebraic construction at every odd order attains the endpoint exception. On the shorter prefix all positive weighted outputs are available but no weights give ordinary order of the same size.
- [Late unary directions](DELAYED-CLOCK-UNARY-RANK.md): failure of early output factorization can force several independent new columns, not just one.
- [The penultimate late test](PENULTIMATE-PAID-TAP.md) does not require localization at a single clock. In a hypothetical \(3d+1\)-stage method of order \(2d+1\), it forces [maximal clock delay](MAXIMAL-ODD-CLOCK-DELAY.md) and yields [reverse clock charts](REVERSE-CLOCK-CHARTS.md). In the full-closure branch, [a further support bound](MAXIMAL-DETECTOR-PHYSICAL-SUPPORT.md) leaves a specific singleton-clock case. These restrictions do not exclude every equality case.

## The saturated suffix and its two diagonalizable quotients

If \(t=\ell+L\), the nonzero \(L\)-th tap forces all \(L\) adjacent physical edges in the suffix to be nonzero. The vectors \(\boldsymbol{\eta}_i=A^i\boldsymbol{\eta}\), \(0\le i\le L\), then form a basis of that suffix, with first physical positions \(\ell+i\). In this basis \(A\) is the nilpotent shift, and \(C\) preserves the successive suffix flags, with actual clock diagonal entries \(x_i\). In particular \(x_0=0\). The restriction of \(C\) to any invariant subspace, and its action on the corresponding quotient, remain split diagonalizable.

Let \(\mathbf u_i\) be the suffix vector whose first nonzero coefficient is one at \(\boldsymbol{\eta}_i\) and \(\beta A^k \mathbf u_i=0\) for \(0\le k<L-i\). These equations successively give a unique vector by the nonzero last moment \(\mu_L\); they also imply \(\mathbf u_i=A^i \mathbf u_0\). Write \(\mathbf u_0=\sum_j U_j\boldsymbol{\eta}_j\), with \(U_0=1\). Put \(M=m+L\). Multiplying the equations by \(1/\mu_L\) shows that \((U_j)\) is the truncated reciprocal to \(\sum_{j=0}^L (M)_j z^j\), where \((M)_j\) is the falling factorial. We need only
\[
                     U_1=-M,\qquad U_2=M,\qquad U_3=M(M-2).
 \tag{3}
\]
The last two are nonzero because the characteristic of the field is zero or greater than \(M\).

The one-clock-factor tests give, for \(i<L\),
\[
                    C\boldsymbol{\eta}_i=i\boldsymbol{\eta}_{i+1}+x_i \mathbf u_i .
 \tag{4}
\]
This includes \(i=0\) by \(C\boldsymbol{\eta}_0=0\). At \(i=L\) the same formula holds with \(\boldsymbol{\eta}_{L+1}=0,\ \mathbf u_L=\boldsymbol{\eta}_L\) by the triangular flag, with no restriction yet on \(x_L\).

For \(i\ge1,\ i+k+2\le L\), expanding \(C^2\boldsymbol{\eta}_i\) in (4) and using the two-clock-factor test leaves \(x_i\beta A^k C \mathbf u_i=0\). To calculate that remaining response, expand \(\mathbf u_i=\sum_j U_j\boldsymbol{\eta}_{i+j}\). Among the \(\mathbf u_{i+j}\) terms of (4), only \(i+j+k=L\) has nonzero response, giving \(x_{L-k}U_{L-i-k}\mu_L\). For the other terms, use
\[
       (i+j)\mu_{i+j+k+1}
          =\mu_{i+j+k}-(m+k+1)\mu_{i+j+k+1}.
\]
Both full sums vanish by the defining responses of \(\mathbf u_0\); the first sum misses its terminal entry \(U_{L-i-k}\mu_L\). Thus
\[
                 x_i(x_{i+r}-1)U_r=0,
                 \qquad 2\le r\le L-i,
 \tag{5}
\]
on writing \(r=L-i-k\). In particular any nonzero clock \(x_i\) forces \(x_{i+2}=1\) and \(x_{i+3}=1\) whenever those indices exist. Every integer distance at least two is a sum of jumps of lengths two and three, so a nonzero \(x_i\) forces \(x_j=1\) at any position \(j\ge i+2\).

If \(x_L\ne1\), this implication forces \(x_1=x_2=0\). The first three-dimensional quotient by the suffix beginning at \(\boldsymbol{\eta}_3\) then has all diagonal entries zero, but \(C\boldsymbol{\eta}_1=\boldsymbol{\eta}_2\) in the quotient by (4). A diagonalizable operator with only the eigenvalue zero is the zero operator, a contradiction. Hence \(x_L=1\).

Now \(x_{L-1}\) cannot be 1: the last two-dimensional block would have
\[
           C\boldsymbol{\eta}_{L-1}=\boldsymbol{\eta}_{L-1}-(m+1)\boldsymbol{\eta}_L,
           \qquad C\boldsymbol{\eta}_L=\boldsymbol{\eta}_L,
\]
using \(U_1=-M\). The coefficient \(m+1\) is nonzero in the paid field, so this again contradicts diagonalizability. Apply (5) with destination \(L-1\), whose distances from both 1 and 2 are at least two because \(L\ge5\). It again forces \(x_1=x_2=0\), impossible in the first quotient. This proves (2) uniformly, without any high reciprocal coefficient assumptions.

## Why the hypotheses come from actual ERK order

Use tree degree \(d=|t|-1\); \(E_d\) is the actual rooted span through tree size \(d+1\), and \(F_d\) the span of differences between normalized Butcher weight vectors of the same degree. In an ordinary order-\(p\) explicit tableau, take \(\beta=bA^m\) and any \(\boldsymbol{\eta}\in E_d\). If \(L=p-1-d-m\ge5\), every needed adjoint word is paid. On formal polynomials the adjoint of unary extension for the Beta weight is
\[
 {\cal J}_m^* P(x)
       =(1-x)^{-m}\int_x^1 (1-u)^m P(u)\,du .
\]
This expression is a polynomial, as seen by expressing \(P\) in powers of \(1-x\); it increases degree by at most one. For each word, the exact scalar operators are multiplication by the clock and integration from zero. Under the weighted integral the adjoint of multiplication is itself, and the adjoint of integration is the operator above. Exactness through order \(p\) annihilates the difference between the numerical word and this polynomial calculation. Thus the word equals its scalar adjoint polynomial evaluated on the original numerical vector \(\boldsymbol{\eta}\). Its one-clock support gives that polynomial at \(\theta\) times \(\beta\boldsymbol{\eta}\). After affine normalization, the pure responses are \(\mu_i\); for a mixed response, the \(i\)-fold upper primitive at zero reduces to the weighted integral with factor \(X^{i-1}/(i-1)!\). In particular its value on \(X^r(1-X)^k m!/(m+k)!\) is \(i^{\overline r}\mu_{i+k+r}\), exactly (1). All factorials used are paid by \(p!\). No separation of \(E_d\) is necessary.

If \(b\boldsymbol{\eta}\ne0\) and \(\theta\ne1\), then every such \(\beta\boldsymbol{\eta}=(1-\theta)^m b\boldsymbol{\eta}/m!\) is nonzero. Since the actual last support of \(bA^m\) is at most \(s-m\), (2) gives
\[
                              s\ge p+\ell-d .
\]
This is one stage beyond appealing only to the nonzero linear path. It applies to actual clock-localized output-visible directions, not to a formal defect class or to an index that has not been shown to support the vector. At clock 1 the scalar responses of words containing a primitive vanish and this causal conclusion is not available. The argument is over paid coefficient fields, with residue-wise use over a ring only when the direction, its output and \(1-\theta\) survive the chosen specialization.

[Principal cohort deletion](PRINCIPAL-COHORT-DELETION.md) gives the exact finite conditions for preserving retained stage profiles and output reads, including a rational strict SDIRK example where equal clocks and linear invisibility are insufficient. [Causal rooted cohort reduction](CAUSAL-ROOTED-COHORT-REDUCTION.md) gives a closed-prefix test, identifies when full rooted profiles can be coalesced without changing the diagonal, and constructs rational DIRK examples showing that the size thresholds for output and outgoing transfer are sharp. These results do not change the unconditional stage bounds.

[Paired layers](PAIRED-LAYER-COMPRESSION.md) replace separate dense layers using earlier stages and exact weighted tests. The [stage counts and single-mode criterion](COUNTS-AND-ACTUAL-SPAN-SHAVING.md) state the extra hypotheses required for optional reductions. The [simultaneous criterion](SUMMED-SPINE-CRITERION.md) instead matches each complete rooted response, allowing cancellation across correction depths. [Its constructions](QUOTIENT-AND-PACKED-CONSTRUCTIONS.md) give exact orders 19 and 20 at any prescribed nonzero real-algebraic diagonal with at most 70 and 77 stages. With exterior reflected sites the second count is 76. These counts do not improve the unrestricted SDIRK table.
