# Several actual late unary directions from failed early clock factorization

This strengthens the [delayed-closure theorem](DELAYED-CLOCK-CLOSURE.md) by counting how many independent late vectors are supplied by powers of \(A\). Use an ordinary order-\(p\) explicit tableau, \(E_d\) of tree degree \(d\) (size \(d+1\)), \(L=p-1-d\), and physical cutoff \(k=s-p+d\). The field is paid through \(p!\). Let \(W\) be the actual clock closure of \(E_d\), and assume \(W\subset E_{d+\delta}\), \(L-\delta\ge5\), \(\delta\ge1\). Suppose a vector \(v\in E_d\) vanishing through row \(k\) has nonendpoint output at precisely \(q>0\) distinct clocks, with \(q\le\delta\) by the universal local tail theorem. Let \(\alpha_\theta\ne0\) denote those charges and \(\lambda_\theta=1-\theta\ne0\). A further contribution at the endpoint is allowed.

For any integer \(J\ge1\) with
\[
                         (q+1)J\le L-\delta+1 ,
\]
the actual \(J\) vectors
\[
                      A^\delta v,\ldots,A^{\delta+J-1}v
\]
are linearly independent modulo \(W\). Consequently they give a real forward rank floor
\[
                      \dim E_{d+\delta+J-1}\ge \dim W+J.
\]
All these directions are zero through row \(k+\delta\).

To prove independence, put \(M=\delta+J-1\). If \(\sum_{j=\delta}^M a_j A^jv\in W\), its support starts after row \(k+\delta\). Every vector of \(W\) with that support has zero response under \(bY^r\) for every \(r\ge1\): its nonendpoint local blocks have exhausted their actual visibility cutoff, and the endpoint factor vanishes. On the other hand the word tests on the original \(v\in E_d\) give
\[
 bY^r A^jv=\frac{r!}{(r+j)!}\sum_\theta\alpha_\theta\lambda_\theta^{r+j}
 \qquad (r\ge1,\ r+j\le L).
\]
Here \(Y=I-C\), and the \(j\)-fold upper primitive of \(Y^r\) is \(r!Y^{r+j}/(r+j)!\) on the model. Thus we may use all rows \(r=1,\ldots,qJ\). Multiplication by \((r+M)!/r!\) gives a sequence of the form
\[
 \sum_\theta\lambda_\theta^r P_\theta(r)=0,\qquad
 P_\theta(r)=\alpha_\theta\sum_{j=\delta}^M
        a_j\lambda_\theta^j\prod_{u=j+1}^M(r+u)
\]
on those \(qJ\) samples. Each \(P_\theta\) has degree at most \(J-1\), and if some \(a_j\ne0\), each such polynomial is nonzero by the leading term from its first nonzero coefficient.

To see that these consecutive samples force every \(P_\theta=0\), let \(T\) be the forward shift of the sequence index. Each sequence \(\lambda_\theta^r P_\theta(r)\) is annihilated by \((T-\lambda_\theta)^J\), by finite differences. Their sum satisfies the monic recurrence that is the product of these \(q\) factors, of order \(qJ\). If the first \(qJ\) values vanish, the formal sequence is zero at every later positive integer. To isolate a term, apply the product of the factors for the other clocks. On this term those distinct shifts preserve degree and multiply its leading coefficient by nonzero factors. A sequence \(\lambda_\theta^r\) times a nonzero polynomial of degree at most \(J-1\) cannot vanish at \(J\) distinct paid integers. Contradiction. This proves the independence.

## The one-step, stage-tight odd survivor

In the tight odd case \(p=2d+1\), \(d\ge6\), \(s=p+d\), assume explicitly that clock closure occurs in one step. The delayed rank/rent theorem then leaves only \(W=E_d+CE_d\) clock-invariant with \(\dim W=\dim E_d+1\), \(\dim F_d=d\), and zero first reverse residual. A late output failure then has exactly one nonendpoint charged clock. Set \(\delta=q=1\). For \(1\le j\le\lfloor d/2\rfloor\), the new rank rent gives \(\dim E_{d+j}\ge p+j+1\); the paid reverse rank at that level has length \(d-j-1\), giving the matching upper bound. Thus
\[
             E_{d+j}=W+\operatorname{span}\{Av,\ldots,A^jv\},
             \qquad \dim E_{d+j}=p+j+1 .
\]
No actual plateau of \(E_{d+j}\) can occur inside this range. Each listed extra direction is a measured late unary vector.

If the literal constant lies in the invariant core of \(E_d\), for example in a one-head description of height \(h\le d\), the degree-\((d+1)\) alias is also forced. Otherwise the actual rank \(p+2\) in degree \(d+1\) would give \(\dim F_{d+1}=d+1\), with no polynomial alias. Its intersection with \(W\) would have rank \(d\): all nominal polys are in \(W\), and the new \(Av\) can have its nominal polynomial subtracted there, leaving a pure vector still outside \(W\). Hence \(F_{d+1}\cap W=F_d\), since \(F_d\subset W\). Then \(CF_d\subset F_d\). All literal polynomial-clock vectors already lie in the invariant core of \(E_d\), so this would make \(E_d\) itself clock-invariant, a contradiction. Thus the degree-\((d+1)\) companion alias exists. The paid companion-alias theorem gives alias dimension \(2j-1\) at degree \(d+j\), and the exact ranks above give
\[
                       \dim F_{d+j}=d+2j
                       \qquad(1\le j\le\lfloor d/2\rfloor).
\]

These are cross-order necessary rank profiles and an actual obstruction to suppressing all late unary growth. They make no claim that the last surviving profile is realizable, nor any unconditional new stage entry or Lean certificate.
