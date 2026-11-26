# The paid neighboring-window cubic and a low-degree valuation separator

**Result.** For genuine common-diagonal SDIRK in characteristic zero, full rooted order \(5\le p\le20\) needs \(s\ge p\). A single paid mixed cubic, combined with the scalar repeated-pole polynomial, gives a uniform argument. It also works beyond \(20\) whenever \(p=tq\) or \(p=tq+1\), with a prime \(q\ge5\) and \(p<q^2\), or when \(p\) is a power of a prime \(q\ge5\). This is not a scalar-only bound: all paid tall and bush moments alone can coexist at \(s=p-1\); see the separate paid Hankel/Padé proof.

## 1. Mixed payment reduces the exceptional scalar degree to three

Let \(A=\gamma I+B\), \(\gamma\ne0\), \(B\) strict, \(\mathbf c=A\mathbf1\) and \(\lambda_n=\mathbf b\cdot B^n\mathbf1\). For \(n<p\), tall order gives
\[
\lambda_n=\ell_n(\gamma)
=\sum_{j=0}^n\binom n j\frac{(-\gamma)^{n-j}}{(j+1)!},
\qquad
(n+1)\ell_n=(1-2n\gamma)\ell_{n-1}-(n-1)\gamma^2\ell_{n-2}.
\]
The recurrence follows by formally differentiating
\(\exp(u/(1+\gamma u))=1+\sum_{n\ge0}\ell_nu^{n+1}\);
omit the last term for \(n=1\). No two consecutive \(\ell_n\) vanish, by descending to \(\ell_0=1\). Hence the only candidate below \(p\) is \(s=p-1\), with \(\lambda_s=0\) and \(L=\lambda_{s-1}\ne0\). The first condition reads \(f_s(\gamma^{-1})=0\), where the monic integer polynomial is
\[
f_s(x)=(-1)^s s!L_s^{(1)}(x)
=\sum_{j=0}^s (-1)^{s+j}\binom{s}{j}\frac{(s+1)!}{(j+1)!}x^j.
\tag{1}
\]
Here the identity follows by collecting the coefficients of \(\ell_s\), so no Laguerre irreducibility result is assumed.

For the mixed payment let \(C=\operatorname{diag}(\mathbf c)\) and \(C_X=C-\gamma I\). For \(u,v\ge0\) with \(u+v+2\le p\), the tree with a leaf attached at the root of a tall tree of size \(v+1\), then \(u\) unary ancestors, gives
\[
\mathbf b\cdot A^u C A^v\mathbf1=\frac{v+1}{(u+v+2)!}.
\]
The factorial here is the product of the root and ancestor sizes \(v+2,\ldots,v+2+u\) times \(v!\). Subtract the two placements of \(C\) around one adjacent \(A\). This pays, for \(u+v+3\le p\),
\[
\mathbf b\cdot A^u(CA-AC)A^v\mathbf1
=\mathbf b\cdot A^{u+v+2}\mathbf1.
\]
Since \(CA-AC=C_X B-B C_X\), binomial expansion of the outer powers gives the corresponding \(\mathbf b\cdot B^u(C_X B-B C_X)B^v\mathbf1=\mathbf b\cdot B^{u+v}A^2\mathbf1\).

At the candidate \(s=p-1\), the actual singleton read
\[
W_i=\mathbf b\cdot B^{s-i}C_X B^{i-1}\mathbf1=L(c_i-\gamma),
\qquad 1\le i\le s,
\]
has a unique strict path, through all \(s\) stages. Its full weight \(L\) is nonzero, so in particular the first subdiagonal \(B_{21}=c_2-\gamma\) is nonzero. Every consecutive difference \(W_{i+1}-W_i\) uses the paid commutator with \(u+v=s-2\); since \(c_1=\gamma\), it follows that
\[
c_i-\gamma=(i-1)\delta,\qquad
\delta=2\gamma+\gamma^2\lambda_{s-2}/L=(1-2\gamma)/(s-1),
\tag{2}
\]
where the final expression follows from the tall recurrence at \(n=s\).

Now use a paid three-donor polynomial window (not a square Hankel window): the first three donor rows of
\(E(F)=\mathbf b\cdot B^{s-3}F(\mathbf c-\gamma\mathbf1)\).
Strict support and (2) give \(E(X(X-\delta)(X-2\delta))=0\) for the polynomial variable \(X\). For \(k\le3\), a \(k\)-leaf bush lifted by \(j\) unary ancestors pays \(k!/(j+k+1)!\) when \(j+k+1\le p\). Hence these \(E(X^k)\) values are the same as replacing \(X^k\) by the corresponding linear combination of \(h! A^h\mathbf1\), from expansion of \((c-\gamma)^k\). With \(M=\lambda_{s-2}\) and \(V=\lambda_{s-3}\), this gives
\[
E(X)=M,\qquad E(X^2)=2L+2\gamma M+\gamma^2 V,\qquad
E(X^3)=12\gamma L+9\gamma^2M+2\gamma^3V;
\]
the last equality uses \(6\lambda_s=0\). The maximum tree order here is \(1+(s-3)+3=s+1=p\).

Put \(t=\delta/\gamma=(\gamma^{-1}-2)/(s-1)\), \(m_1=\gamma M/L\), \(m_2=\gamma^2V/L\). The scalar recurrence at \(s,s-1\) gives
\[
m_1=t-2,\qquad
(s-2)m_2=((s-1)t-2(s-2))(t-2)-s.
\]
The paid vanishing cubic, divided by \(\gamma L\), is
\(12+9m_1+2m_2-3t(2+2m_1+m_2)+2t^2m_1=0\).
Substituting and multiplying by \(s-2\) yields
\[
(s+1)t^3-4s t^2+2(s-3)t+4=0.
\tag{3}
\]
Thus the scalar root \(\gamma^{-1}\) has degree at most three over \(\mathbb Q\). This is the paid mixed test, not a consequence of two scalar Hankel ranks. For comparison, at \(s=3\), \(f_3(2+2t)=8(t^3-3t^2+1)\) and (3) is proportional, so the separation used here is not valid at order four.

## 2. Valuations exclude low-degree factors

Use a prime-adic valuation \(v_q\) on an algebraic closure, normalized by \(v_q(q)=1\). Every root of a monic integer polynomial has \(v_q\ge0\), since otherwise the leading term is the unique least-valuation term. A sum can vanish only if its least valuation occurs twice. For a monic rational factor, the sum of valuations of its roots is the integer valuation of its nonzero constant term. The following elementary line rule will be used: if a monic degree-\(s\) polynomial has \(v_q(a_j)\ge(s-j)\theta\) with equality at \(j=0,s\), then every root has valuation \(\theta\). For a root of lower valuation the leading term would be uniquely least, and for one of higher valuation the constant term would be uniquely least.

**Family A: \(p=tq<q^2\), \(q\ge5\) prime.** Now \(s=tq-1\) and no \(\binom{s}{j}\) is divisible by \(q\). Indeed
\((1+X)^{tq-1}=(1+X)^{q-1}(1+X^q)^{t-1}\) modulo \(q\), and all coefficients of both small binomial factors are nonzero. Thus (1) gives \(v_q(a_j)=t-\lfloor(j+1)/q\rfloor\). A root of valuation zero is impossible because the top coefficient is the only unit. For a root of valuation \(w>0\), the only candidate least indices are \(0,q-1,2q-1,\ldots,tq-1\), the first of each constant-coefficient-valuation block. The latter indices have value \(t-w+k(qw-1)\) for \(k=1,\ldots,t\), and the constant term has value \(t\). If \(w<1/q\), the last index is uniquely least (the tie with the constant would need \(w=t/(tq-1)>1/q\)). If \(w>1/q\) the least among the latter indices is uniquely the first, and the tie with the constant requires \(w=1/(q-1)\). Hence all roots have valuations in \(\{1/q,1/(q-1)\}\). Any factor of positive degree at most three would have constant valuation strictly between zero and one, impossible.

**Family B: \(p=tq+1<q^2\), \(q\ge5\) prime.** Here \(s=tq\) and \(\binom{s}{j}\) is divisible by \(q\) if \(j\) is not a multiple of \(q\), as seen from \((1+X)^s=(1+X^q)^t\bmod q\). Write \(j=kq+r\), \(0\le r<q\). If \(r\le q-2\), the factorial part of (1) already has valuation \(t-k\); if \(r=q-1\), the binomial factor supplies at least one to recover \(t-k\). Therefore \(v_q(a_j)\ge(s-j)/q\), with equality at both endpoints. The line rule gives \(v_q=1/q\) for every root, again excluding low-degree factors.

For the additional prime-power family \(p=q^h\), \(q\ge5\), all \(\binom{p-1}{j}\) are units modulo \(q\) by the base-\(q\) binomial digits, or by repeated multiplication by \((1+X^{q^i})^{q-1}\). The factorial digit-sum identity gives
\(v_q(a_j)=(p-1-((j+1)-s_q(j+1)))/(q-1)\ge (s-j)/(q-1)\) with equality at the endpoints. Here \(s_q\) is base-\(q\) digit sum. The line rule again excludes every degree at most three.

**The one remaining order \(p=9\).** At \(q=3\) the same prime-power line argument gives \(v_3=1/2\) for every root, so any rational factor has even degree. At \(q=7\), the coefficients below degree \(7\) are divisible by \(7\) (for \(j\le5\) the factorial ratio contains \(7\); for \(j=6\), use \(\binom86=28\)). The constant has valuation \(1\), while \(a_7=\pm72\) and \(a_8=1\) are units. A root of positive valuation \(w\) thus needs a tie between the constant and index \(7\), so \(w=1/7\); the remaining roots have valuation zero. Any rational factor of degree at most three can have only valuation-zero roots, since the sum of at most three positive \(1/7\) contributions would be nonintegral. Monic rational factors are integral by Gauss's lemma. The reduction of such a factor has nonzero constant and divides \(x^7(x+\overline{a_7})\) modulo \(7\), hence has degree at most one. This contradicts the even-degree requirement.

Through \(20\), primes \(p\ge5\) enter Family A with \(t=1\); orders one more than a prime \(\ge5\) enter Family B with \(t=1\). Of the remaining orders only \(9,10,15,16\) occur; \(10,15\) enter Family A at \(q=5\), and \(16\) enters Family B at \(q=5\). Thus (1) has no rational factor of positive degree at most three for the stated range. It cannot have the root required by (3). This uses characteristic zero and does not extend the bound to arbitrary paid-characteristic rings.
