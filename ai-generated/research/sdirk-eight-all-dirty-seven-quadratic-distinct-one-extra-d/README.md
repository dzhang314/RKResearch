# Distinct doubled endpoints cannot each use one additional doubled label in their opening triples

Assume all-dirty strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field, with exactly seven distinct physical clock labels and a genuinely quadratic singleton residual graph. Let D denote a doubled clock label and S a singleton. If the two physical endpoints are distinct D labels, the two actual opening triples **cannot both have exactly one later D**. This is a necessary chronology restriction, not a global lower bound. No ordering, real embedding, uniform positivity, or finite-characteristic argument is used.

This packet and the [mutual-reuse exclusion](../sdirk-eight-all-dirty-seven-quadratic-distinct-mutual-reuse/README.md) exhaust the chart. Together with [no D,D,D at either boundary](../sdirk-eight-all-dirty-seven-quadratic-midpoint-vs-arithmetic/README.md) and the [shared-label endpoint exclusion](../sdirk-eight-all-dirty-seven-quadratic-no-shared-end/README.md), **whenever both endpoints are D, at least one actual prefix has type D,S,S**. Thus at most three physical D rows are in the first and last triples combined. The remaining both-D possibilities are:
- both D,S,S in actual arithmetic/arithmetic (any star in this shape was [excluded](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md));
- one D,S,S and the other with exactly one later D.

The genuinely quadratic graphs with one or two singleton endpoints, and the all-dirty branches with more than seven clocks, are not resolved by these packets. The general 10–11 stage interval is unchanged.

## Common geometry and actual pair data

Normalize the common diagonal to one, let \(\ell=1/\gamma=2m\), \(h=m-1\ne0\), and use \(t=x-m\). The distinct endpoint D labels are \(-h,h\), and the third D label is \(d\). The [odd projection from opposite D labels](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md) gives \(Q/B=L_3-\mu tL_4\), \(\mu\ne0\); put \(R=rW\), where \(W\) is monic quadratic. The exact root cases are:
- even: \(d=0,\ W=t^2-S\), \(S=(21m^2h^2-15m^4)/(35h^2-21m^2)\);
- split: \(d\ne0,\ W=t(t+d)\), \(d\ne\pm h\), and
\[
           \Theta(h,d)=35h^2d^2-21m^2(h^2+d^2)+15m^4=0 .
\]
The even case includes \(S=0\) (Hermite), and \(S=h^2\) is not excluded by definition. The denominator \(35h^2-21m^2\) is nonzero because \(\mu=(h^2-3m^2/5)/L_4(h)\ne0\).

An extra D clock with normalized offset \(y=x_{\rm D}-1\) in its own orientation pays exactly the following literal pairs after the first normalized residue \(1/2\):

| Phase | Extra D residue | S offset from first clock | S residue |
|---|---|---|---|
| A2, arithmetic D is second | \(\kappa(y)/2\) | \(2y\) | \(q(y)/2\) |
| A3, arithmetic D is third | \(q(y/2)/2\) | \(y/2\) | \(\kappa(y/2)/2\) |
| S, either genuine star order | \(\kappa(y)/2\) | \(2-y\) | \(\kappa(y)/2\) |

Here \(\kappa(u)=1+2u-u^2\), \(q(u)=q_{\rm num}(u)/D(u)\) with \(D=-2+u+4u^2-u^3\) and \(q_{\rm num}=(1+4u-4u^2)D+4u^2(3u-2)\). The table uses the actual nonzero arithmetic tap condition \(3u-2\ne0\); it does **not** rule out arithmetic \(u=2\) just because it was impossible at a shared endpoint. The star order uses \(\kappa(2-y)=\kappa(y)\) and the same unordered set of actual pairs, without permuting a tableau. A singleton clock must not be any D label, any other already consumed singleton, or a graph root.

The forward extra D label is either \(h\) or \(d\), and the reverse original extra D label is either \(-h\) or \(d\). This is the entire place census: either both reuse the opposite endpoints (the separate packet), each uses \(d\), or exactly one uses the opposite endpoint. In the last case orient by genuine weighted reflection so the forward uses \(h\). Thus the latter two configurations use all three D labels in their actual boundary triples. Let \(g_{\rm f,D},g_{\rm r,D}\) be the extra D residues from the table, \(s_{\rm f},s_{\rm r}\) the two actual singleton labels in original centered clocks, and \(g_f,g_r\) their normalized values in their own orientations.

The two observed singleton residues define \(r=g_f/W(s_{\rm f})\) and \(\lambda=rW(s_{\rm r})/g_r\), with literal nonzero divisors. Here \(\lambda\ne0\) converts reverse to original residue. The one actual shared D label gives \(\beta_0=B\lambda\) by Vieta. Put \(C=A_2+B R\), and take the three D values of \(\lambda C\). Each is obtained from the corresponding value of \(\lambda A_2\) below by adding \(\beta_0 rW\); no \(W\) division is used at a D label.

## Matching the third D label

The actual shared label is \(d\), the normalized D offsets \(h+d\) and \(h-d\) forward and reverse. Vieta gives \(\beta_0=-L_4(d)/(g_{\rm f,D}g_{\rm r,D})\). The two actual residues at \(d\) must differ after conversion, so \(g_{\rm f,D}-\lambda g_{\rm r,D}\ne0\). The observed D reads give
\[
 \begin{split}
 \lambda A_2(-h)&=2\lambda L_4(h)-\beta_0/2,\\
 \lambda A_2(h)&=2L_4(h)-\beta_0\lambda/2,\\
 \lambda A_2(d)&=-\beta_0(g_{\rm f,D}+\lambda g_{\rm r,D}).
 \end{split}
\]
The first two follow from the one known physical D residual at each endpoint and \(U=0\); the last from the actual two residuals at \(d\). The two actual singleton equations are
\[
      \lambda L_4(s_{\rm f})-g_f(\lambda C)(s_{\rm f})=0,\qquad
      L_4(s_{\rm r})-g_r(\lambda C)(s_{\rm r})=0,
\]
where \(\lambda C\) is interpolated on the three known distinct D labels. All interpolation denominators are genuine distinct gaps. The two phases can be considered unordered by the true mirror (changing \(d\) to \(-d\) when necessary).

If the graph is even, a choice A2 would put a supposed singleton at the opposite endpoint D. Equal pair-data phases otherwise give \(\lambda=1\) by evenness of \(W\) and duplicate the same extra D pair. The remaining even A3/S has unit exact gcd of the two singleton equations modulo their declared nonzero guards; this does not discard Hermite cases. If the graph is split, take exact resultants with \(\Theta\) in \(d\), separately for the two equations. The mixed phases have unit guarded gcd. The same-phase projections give only a single irreducible \(h\)-factor each: degrees 58 for A2/A2 and A3/A3, and 32 for S/S. A common projected root does not by itself ensure the *same* \(d\) satisfies both equations. Reconstruct the exact \(h\) field and reduce **both** integer numerators modulo \(d^2-S\), the scalar normalized \(\Theta\). The results are \(a_0+a_1 d,\ b_0+b_1 d\) with \(a_0b_1-a_1b_0\ne0\) in all three fields. Thus no \(d\) in any extension works, including a potential singular or repeated fibre. No \(p\)-adic reduction or trace shortcut is used.

## One opposite-endpoint reuse

Orient the extra forward D at \(h\) and reverse extra D at original \(d\). Their actual normalized offsets are \(2h\) and \(h-d\), respectively. At the shared label \(h\), \(\beta_0=-2L_4(h)/g_{\rm f,D}\), and \(g_{\rm f,D}\ne\lambda/2\) ensures different physical pairs. The paid values now are
\[
 \begin{split}
 \lambda A_2(-h)&=2\lambda L_4(h)-\beta_0/2,\\
 \lambda A_2(h)&=-\beta_0(g_{\rm f,D}+\lambda/2),\\
 \lambda A_2(d)&=L_4(d)/g_{\rm r,D}-\beta_0\lambda g_{\rm r,D}.
 \end{split}
\]
Use the same interpolation and two actual singleton equations. Check all nine independent forward/reverse phase pairs in each graph shape. Some are forbidden by literal label/residual guards (e.g. split forward A3 puts the singleton at \(t=0\), a graph zero). Every remaining even polynomial gcd or split projected gcd in \(h\) is a unit after stripping only the actual nonzero guards. Thus both nonmutual overlap patterns are impossible.

## Reproduction and scope

Run `python check_exact_simultaneous.py` with SymPy 1.14 and python-flint 0.8; it imports the sibling two sources. It computes every necessary exact phase polynomial, verifies that each denominator factor cleared is among the literal guards, and checks each high-degree \(h\) field before the simultaneous \(d\) fit. The split resultants eliminate from integer polynomials before specializing, so projected leading coefficient loss is not swept away. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticDistinctOneExtraD.lean) stages the scalar simultaneous-fit determinant identity, not a stock or end-to-end native proof. No ordering or real-field structure is used in this theorem.
