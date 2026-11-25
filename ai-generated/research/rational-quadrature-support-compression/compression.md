# Exact compression by prescribed support exchange

Let \(L\) be a rational linear functional on polynomials. A rule *pays \(p\) moments* if it agrees with \(L\) on degrees \(0,\ldots,p-1\). For a distinct support with monic nodal polynomial \(N\) of degree \(n\le p\), its interpolatory weights are
\[
 w_x=L(N/(X-x))/N'(x).
\]
These weights pay \(p\) if and only if \(L(X^jN)=0\) for \(0\le j<p-n\): divide by \(N\) and integrate the remainder by interpolation. In particular the weights are forced over any characteristic-zero extension if the nodes and \(L\) are rational. Every site called active below has a nonzero aggregate weight. No positivity or interval assumption is needed.

## Exchange theorem in every order and every compression size

Fix an active \(n\)-site rule paying \(p\ge n\). Seek \(m<n\) active sites paying the same \(p\). Keep a prescribed set of \(n-k\) old sites with nodal polynomial \(H\), remove the other \(k\) distinct sites \(u_1,\ldots,u_k\), put \(D=\prod_i(X-u_i)\), \(N=HD\), and write \(C_x=L(N/(X-x))=w_xN'(x)\). Let \(d=m-(n-k)\ge0\), \(s=p-m\). A candidate nodal polynomial is \(HG\), where \(G\) is monic of degree \(d<k\).

* If \(k\le s\), there is no such exchange with disjoint new sites.
* If \(k>s\), let \(T\) range over polynomials of degree at most \(k-s-1\). Form the *one* interpolation
  \[
    U_T(X)=\sum_{i=1}^{k}
       \frac{T(u_i)}{C_{u_i}}\frac{D(X)}{(X-u_i)D'(u_i)}.
  \]
  All monic paid candidates are exactly \(G=U_T\) having degree \(d\) and leading coefficient 1. These constraints on \(T\) are linear. Retain only polynomials with \(d\) distinct rational roots, disjoint from both the retained and removed sites (the latter fixes the exact overlap). To test activity, for a new root \(z\) and an old retained site \(x\), respectively,
  \[
    L(HG/(X-z))=-T(z)/D(z),\qquad
    L(HG/(X-x))=(C_xG(x)-T(x))/D(x).
  \]
  Divide these cofactors by \((HG)'\) at the corresponding site for the actual weight. An exactly-order-\(p\) rule additionally requires \(L(X^sHG)\ne0\). For a rule paying *at least* \(p\), omit this last test.

**Proof.** For \(0\le j<s\), \(X^jHG\) has degree at most \(p-1\), so the old rule gives
\[
 L(X^j HG)=\sum_{i=1}^k u_i^j C_{u_i}G(u_i)/D'(u_i).
\]
If \(s\ge k\), the first \(k\) rows are invertible Vandermonde equations; \(G\) would vanish at all \(k\) sites despite its smaller degree. For \(s<k\), the \(s\) rows have rank \(s\). Leading-coefficient comparison in Lagrange interpolation gives \(\sum_i R(u_i)/D'(u_i)=0\) for \(\deg R<k-1\). Thus each vector \(C_{u_i}G(u_i)=T(u_i)\), \(\deg T\le k-s-1\), satisfies all \(s\) equations. The evaluation map on this space is injective, and its dimension \(k-s\) is the full nullity. This proves necessity, sufficiency and the stated interpolation because \(\deg G<k\). For either cofactor the polynomial being evaluated has degree \(m-1<p\). At a new root \(z\) the old rule gives \(\sum_i T(u_i)/((u_i-z)D'(u_i))=-T(z)/D(z)\), by partial fractions. At a retained \(x\) add the old site contribution \(w_xH'(x)G(x)=C_xG(x)/D(x)\). This establishes both formulas.

**Overlap tradeoff.** If two unequal rules of sizes \(n,m\) pay \(p\), let \(t\) be their shared sites and \(e\) the shared sites carrying identical weights. Their difference vanishes on the first \(p\) powers, yet has \(n+m-t-e\) nonzero atoms. Vandermonde invertibility requires at least \(p+1\) such atoms. Hence \(t+e\le n+m-p-1\). In particular \(18\longrightarrow17\) at \(p=20\) permits at most 14 shared sites, and at maximal overlap none of the shared weights can stay unchanged.

**One fewer site.** For \(m=n-1,\ r=p-n\), one must drop at least \(r+2\) old sites. At the minimum \(k=r+2\), \(T\) is constant and the unique possible residual is \(U_1/J\), where \(J=\sum_i1/(C_{u_i}D'(u_i))\). If \(J=0\), no monic residual of degree \(k-1\) exists. Otherwise every genuinely new root automatically contributes (the numerator in its weight is a nonzero constant). The rational splitting, collision and retained-weight tests remain.

The first flexible case \(k=r+3\) has \(T\) linear. Writing \(U=U_1,\ V=U_X\), one has \(V=XU-JD\), with \(J\) the leading degree-\((k-1)\) coefficient of \(U\). If \(J\ne0\), the degree-\((k-1)\) rational map \(V/U\) is reduced (since \(U(u_i)\ne0\)) and fixes all \(k\) removed sites. Its fibers, including infinity, give the polynomials \(U_T\) up to normalization. Every genuinely new root contributes: for finite fiber parameter \(b\), \(T\) is proportional to \(X-b\); a root at \(X=b\) would require \(D(b)=0\), so would already be an old site. Infinity has constant \(T\). If \(J=0\), then \(V=XU\); either \(U\) has degree \(k-2\) and is a fixed factor of every monic candidate, or no candidate of degree \(k-1\) exists. This is a general low-dimensional reduction, not an existence claim.

## Canonical interval order-20 prefix

Use the published order-18 rule of 16 sites from interval-component-continuation. From it remove \(u=7b,\ v=6a\) to obtain the fixed fourteen-site prefix \(H\). In interval-targeted-p19 the next two prescribed points are \([168]D\) and \([-42]D_{\rm new}\); the final order-20 rule has 18 sites and its four nonprefix sites are \(9c,10a,10b,10c\). All calculations below use only these published straight-line source data. A sufficient independent check of the rigid obstruction stops already at the order-18 ancestor.

Write \(P=H(X-u)(X-v)=HB\), \(h=L(X^2P)\ne0,\ k_1=L(X^3P)\), \(C_u=L(P/(X-u)),\ C_v=L(P/(X-v)),\ \ell=v-u\). The ancestor pays \(L(P)=L(XP)=0\). Its full monic cubic pencil with \(L(HG)=L(XHG)=0\) is
\[
 G_\tau=(X-\tau)B+R_u(X-v)+R_v(X-u),\quad
 R_u=\frac{h}{\ell C_u},\quad R_v=-\frac{h}{\ell C_v}.
\]
Indeed, the two unknown pole residues are uniquely determined by the two equations
\(\sum_i R_i C_i=0,\ \sum_i iR_iC_i=-h\), with \(i\in\{u,v\}\). Necessity follows by polynomial division by \(B\) for *every* monic cubic, and the equations use \(L(XP/(X-i))=i C_i\). Since \(L(X^2P/(X-i))=i^2C_i\), the third row is
\[
     L(X^2H G_\tau)=k_1-h(\tau+u+v).
\]
Thus \(G=G_{\tau_0}\), \(\tau_0=k_1/h-u-v\), is the only rational-coefficient cubic whose 17-site nodal candidate pays 20. This is necessary before one asks whether its roots are rational. The same \(G\) is forced for any continuation that retains exactly this ancestor prefix, independently of the chosen elliptic points.

In the latest two-shift pencil, \(w=9c\) is the third root left from the first elliptic point while the other two roots are dropped. Its nodal polynomial is \(H(X-w)G_{\rm last}\). Vanishing of the retained \(w\)-cofactor is exactly \(L(HG_{\rm last})=0\); combining this with the two guaranteed rows for \(H(X-w)G_{\rm last}\) gives \(L(XHG_{\rm last})=L(X^2HG_{\rm last})=0\), and conversely these three rows imply all three required equations. Thus its unique cofactor-zero fiber is precisely the same \(G\) (the slope of the cofactor in the last pencil is the negative nonzero old \(w\)-cofactor).

### One exact certificate in two coordinate systems

For \(q=2147483647\), the modular trace gives \(u,v=(1522663033,1352699488)\), \(C_u,C_v=(1986267913,541705821)\), \(h,k_1=(844394583,1378218029)\), \(\tau_0=259688100\). The six prefix moments \(L(X^jH)\), \(0\le j\le5\), are
\[
 (1590445951,1841160740,1580991869,927171731,1273401878,784409315).
\]
Their first \(3\times3\) Hankel determinant is \(1619569496\ne0\bmod q\), a second proof of uniqueness over \(\mathbb Q\). In physical \(X\), the ascending monic cubic coefficients are \((630645229,2011688757,1159916673,1)\). In \(Z=(X-u)/\ell\), the monic normalized cubic \(g(Z)=G(u+\ell Z)/\ell^3\) instead has coefficients
\[
       (273581351,1877309364,165315245,1).
\]
Repeated squaring and Euclidean reduction give, in ascending coefficients,
\[
 Z^q\bmod g=(181645769,1645707219,616261286),\qquad
 \gcd(g,Z^q-Z)=1 .
\]
The cubic is irreducible modulo \(q\), not merely nonsplit. Every straight-line division in the trace has a unit denominator, so the rational cubic is monic over \(\mathbb Z_{(q)}\). A rational root would be \(q\)-integral (otherwise its cubic power has strictly smaller valuation than every lower term) and would reduce to a root. This proves irreducibility over \(\mathbb Q\). No 17-site rational rule paying order 20 can contain all these fourteen nodes, even with signed weights or with rational sites outside the integration interval. This says nothing about other fourteen-site prefixes or a general 17-site bound.

Independently, on the published final 18 sites the forced four-drop calculation gives \(J=628061087\); normalizing its reciprocal interpolant gives exactly the same physical cubic. The fixed polynomial \(HG\) has all fourteen retained cofactors nonzero modulo \(q\); their product is \(727220578\). This last fact, not a computation on fourteen alternative solutions, supplies the coprimality hypothesis of the one-site-release theorem. The exact rational zero rows above are proved symbolically, not inferred from zero residues. The independent standard-library script in this packet operates at the single specified prime, using named source steps only, and does not search any alternative drop set.
