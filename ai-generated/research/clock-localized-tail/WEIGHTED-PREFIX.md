# Weighted order conditions on an earlier stage prefix

Use the degree convention \(d=|t|-1\). Thus \(E_d\) is the actual numerical span of all rooted derivative columns through tree size \(d+1\), and \(F_d\) is its numerical pure difference span. Let \(A,b\) be an ordinary order-\(p\) explicit tableau with \(s\) stages over a field in which \(p!\ne0\). Write \(C\) for its clock diagonal. Set \(L=p-1-d\), and assume \(L\ge5\). The [localized tail theorem](README.md) gives the support bound used below. The global prefix results require an invariant space; the local factorization does not.

## Local output factors through earlier physical reads

For a clock \(\theta\ne1\), let \(E_d(\theta)\) be the numerical subspace of \(E_d\) consisting of actual vectors supported on that clock. On this subspace the original output factors through physical rows at clock \(\theta\) of index at most
\[
                             k=s-L-1=s-p+d.
 \tag{1}
\]
Indeed if such a vector vanishes there but has nonzero output, its first nonzero index is at least \(k+1\). The universal paid tail then requires at least \(L+1\) rows after that index, incompatible with \(s\). Thus the kernel of the earlier evaluation map is contained in the output kernel; elementary finite-dimensional factorization gives a linear combination of those existing early reads. One may replace \(s\) in (1) by the last nonzero physical index of \(b\) for a stronger cutoff. No clock-invariance assumption is needed for this local statement.

Now suppose \(CE_d\subset E_d\), for example from an actual plateau \(E_d=E_{d+1}\). Spectral projections in \(C\) split \(E_d\) into its true clock-local subspaces. Choose a row \(b'\) supported on the prefix of length \(k\), using only nonendpoint clocks, that realizes the factorizations for all \(\theta\ne1\). Consequently, on the whole actual \(E_d\),
\[
 b'(I-C)^m/m!=b(I-C)^m/m!=b A^m
 \qquad(1\le m\le L).
 \tag{2}
\]
The first equality uses the block factorization and the vanishing endpoint factor; the second is the paid formal upper primitive on each input column. It is not asserted that \(b'\) itself agrees with \(b\) on the clock-1 component. Nor is \(b'(I-C)^m/m!\) asserted to equal a literal tap of \(b'\) on all possible stage vectors.

Strict truncation to that prefix preserves the actual rooted columns through the stated size. Thus the prefix has a single collection of actual weights \(b'\) for which all the weighted outputs in (2) are exact through tree size \(d+1\) simultaneously. An output with shift \(m\) has the moment functional
\[
                   P\longmapsto\frac1{m!}\int_0^1 (1-X)^m P(X)\,dX .
\]
If \(N_m(d+1)\) is any paid lower bound for that actual Beta-weighted problem, this yields the numerical conditional floor
\[
                         s\ge p-d+N_m(d+1)
              \qquad (1\le m\le L).
\]
The prefix therefore consists of genuine exact numerical weights on a strict physical tableau, not a synthetic model-only integration rule.

The simultaneous weights give a lower bound on the dimension of the tree space on the prefix. Let \(F_d^{\rm pre}\) be the actual pure span on this same prefix. If \(P(\mathbf c^{\rm pre})\in F_d^{\rm pre}\) with \(\deg P\le d\), then \(P(0)=0\) at the literal origin. Equation (2) gives \(\int P(X)(1-X)^m\,dX=0\) for every \(1\le m\le L\). Their independent rank on \(P/X\) is at least \(\min(d,L)\), by the paid Gram for weight \(X(1-X)\) on the lower powers. Consequently
\[
    k\ \ge\ \dim E_d^{\rm pre}
        \ \ge\ \dim F_d^{\rm pre}+1+\min(d,L).
 \tag{3}
\]
A separately verified pure-rank floor on the weighted prefix may be inserted here. When \(L\ge d\), one gets full model separation in degree \(d\) on this strict prefix, despite each single weighted output being exact only through size \(d+1\). All Gram use is within \(p!\), since \(2\min(d,L)+1\le p\).

## An independently forced invariant odd midpoint

There is a sharper ordinary consequence if \(p\ge2d+1\) and \(CE_d\subset E_d\). At that range the actual degree-\(d\) model is separated by the usual paid weight-\(X\) Gram. Moreover \(F_d\) is now \(C\)-invariant. Indeed write \(C f=P(\mathbf c)+f'\) for \(f\in F_d,f'\in F_d,\deg P\le d\). The polynomial has \(P(0)=0\), and the \(d\) scalar tests \(b C^k C f=0\), \(0\le k\le d-1\), imply \(\int X^kP=0\). The square Gram on \(P/X\) forces \(P=0\).

On each clock block the polynomial part supplies at most the one constant-vector line modulo \(F_d\). There are exactly \(d+1\) clock labels where it supplies one, by the separated model dimension. These are the clean labels, with an exact normalized clock read killing \(F_d\). One is the literal origin. The output restricted to the model is an ordinary scalar quadrature on these labels. All \(d+1\) aggregate weights are nonzero: otherwise the nonsingular ordinary Gram on polynomials through degree \(d\) would be represented by only \(d\) evaluations.

If \(p\ge2d+2\), this is impossible: the monic hull \(X\) times the polynomial through the \(d\) nonzero clean labels, multiplied by tests through degree \(d\), would annihilate a nonsingular weight-\(X\) Gram while exact order pays through degree \(2d+1\). Thus such an early clock-invariant \(E_d\) cannot occur at all. If \(p=2d+1\), none of the clean labels can be \(1\): with both endpoints the same hull argument uses weight \(X(1-X)\) and tests through degree \(d-1\), within degree \(2d\).

For \(p=2d+1\) and \(d\ge5\), all these exact clean reads are therefore already complete on the actual prefix of length \(k=s-p+d\). Indeed on a clean clock block the local output is its nonzero aggregate weight times the one normalized model read; (1) puts that read on the early prefix. Those reads preserve separated degree \(d\) even after truncation: they independently measure the degree-\(d\) model on its \(d+1\) labels. Both the restricted \(E_d\) and \(F_d\) remain \(C\)-invariant.

Let \(D_d\) be any independently established pure-rank floor for \(\dim F_{d-1}\) on actual ordinary order-\(d\) ERK providers. The [Hermite argument for first providers](../erk-first-provider/README.md) applies to this prefix. Its pure rank in degree \(d\) is at least \(D_d+\lfloor d/2\rfloor\): the exact clock reads give actual order-\(d\) providers by literal prefix integration, and their first \(\lfloor d/2\rfloor\) completions supply the preceding independent Hermite rows. Since the prefix has length \(k=s-p+d\) and its tree space has dimension \(d+1+\dim F_d^{
m pre}\),
\[
                   s\ \ge\ p+1+D_d+\lfloor d/2\rfloor .
\]
For \(d\ge6\), the ordinary size-six pure rank floor and strict pure growth give \(D_d\ge d-1\), so the displayed conditional bound is \(p+d+\lfloor d/2\rfloor\). For example it is 25 at \(p=15,d=7\) *if the actual midpoint \(E_7\) is clock-invariant*. Outside a branch where that hypothesis is forced, the bound is not an unconditional table entry.

The arguments are over paid coefficient fields, with no signs or completeness. Ring transfer is residue-wise where the actual rooted hypotheses and any numerical rank data used descend. No positivity or completeness of the coefficient field is used. These are mathematical proofs, not Lean certificates.
