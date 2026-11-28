# Seven zero labels with a repeat at one of the first three early rows

Let \(A,\mathbf b\) be a ten-stage strict SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with common nonzero diagonal \(\gamma\). Let \(\mathbf c=A\mathbf1\) and \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Assume exactly eight physical zeros of \(\mathbf g\), at exactly seven distinct labels. The [low-label reduction](../sdirk-eight-eight-zero-low-labels/README.md) makes rows 1 and 2 the two off rows, at distinct clocks and with individually zero output weights. The [zero-ratio exclusion](../sdirk-eight-eight-zero-zero-ratio/README.md) lets us assume the reflected second ratio \(\kappa_R\ne0\).

**Result.** The only repeated label cannot connect one of physical rows 3, 4, 5 to:

* any of physical rows 8, 9, 10 in the silent-eighth or live-arithmetic branch;
* the terminal row 10 in the live-star branch, with no restriction on the free star gap.

These are 21 characteristic-zero chronology cases, not a positive-characteristic claim, and not an exclusion of all seven-label configurations. In particular an early mate at row 6 or 7 is not covered, nor is a live-star rear mate at row 8 or 9.

## 1. A two-dimensional forward pure space produces a fourth gate

Normalize \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\), \(C'=\operatorname{diag}(\mathbf x)\). Write \(U=\ker\operatorname{diag}(\mathbf g)\). The five distinct early labels \(a,b,c,d,e\) are the actual clocks in physical rows 3 through 7, and \(q\) is the label that reappears at the rear, initially one of \(a,b,c\). We use the [same supported first-three gates](../sdirk-eight-eight-zero-low-labels/README.md#1-literal-placements-and-exact-profile-gates)
\[
 a=1+2u,\quad Q(u)=0,\quad b^2-(2u+4)b+1+2u=0,\quad C_3(c;D)=0 .
\]
Here \(Q(T)=4T^3-12T^2+3T+2\). The replay regenerates \(C_3\) from the two primitive equations in the [early-repeat proof](../sdirk-eight-eight-zero-early-repeat/README.md#1-physical-to-grouped-ingress).

Let \(\delta\) be the difference of the coordinate rows at the two copies of \(q\). The grouped quadratic pure row \(\mathbf z^\mathsf T\) is a nonzero barycentric row, since it has a nonzero coordinate at at least one singleton rear label: the two different rear labels of rows 9 and 10 have nonzero pure coordinates, and at most one label is doubled. The argument in the [paid early-repeat rank proof](../sdirk-eight-eight-zero-early-repeat/README.md#2-live-arithmetic-a-paid-quartic-with-a-repeated-early-clock) therefore gives \(\delta\notin W_2\) and
\[
 F_5|_U\cap\ker\delta=\langle L_{3,D},L_{4,D},L_{5,D}\rangle|_U ,
\]
where the \(L_{j,D}\) are the usual shifted scaled Legendre polynomials. This step does not assume that either literal weight on the doubled label equals its aggregate.

Multiplication by \(C'-qI\) takes \(F_4|_U\) into \(F_5|_U\) and kills both repeated coordinates, so maps into that three-polynomial span. Every scalar cubic has an actual supported \(E_3\) representative: the supported quadratics \(2T-1-T^2/2\) and \((T-1)(T-1-u)\), multiplied by \(1,T\), form a basis by coprimality. Take the supported input with trace \(\sigma(T)=(T-a)(T-b)(T-c)\). Let \(J\) be formal integration from zero; its pure discrepancy \(\mathbf f=A'\boldsymbol\sigma-(J\sigma)(\mathbf x)\) belongs to \(F_4\). Therefore \((C'-qI)\mathbf f|_U\) is represented by \(V\in\langle L_{3,D},L_{4,D},L_{5,D}\rangle\).

At the three first actual zero rows the read of \(A'\boldsymbol\sigma\) vanishes, so
\[
 V(x)=-(x-q)(J\sigma)(x)\quad(x=a,b,c).
\]
Whenever the three-by-three Legendre evaluation determinant is nonzero, these determine \(V\) uniquely. Every certificate below checks that determinant as a unit, for all possible third-label roots in its chosen good reduction. At the fourth zero row the input on every earlier stage is zero, so its read is the diagonal \(\sigma(d)\). Thus
\[
 C_4(d)=0,\qquad
 C_4(T)=\frac{(T-q)(\sigma(T)-J\sigma(T))-V(T)}{\sigma(T)} .
\]
The division is exact by the three displayed interpolation conditions, yields degree at most two, and cancellation at \(d\) is valid because \(a,b,c,d\) are distinct. No numerical reconstruction of taps is used.

## 2. Ordinary recovery from only singleton ratios

Let \(P_2=(T-d)(T-e)\). In the finite-gap branches write \(s=D-1,t=s-v,r=s-2v\) and \(\kappa=1+2v-v^2\ne0\). A silent eighth has \(H(v)=v^3-4v^2-v+2=0\). Live arithmetic has the [cleared compatibility sextic](../sdirk-eight-seven-zero-pure-distinct/README.md#2-rear-cardinal-rows-and-the-arithmetic-compatibility-sextic), valid with repeats by the same literal three inputs and two-dimensional \(Z_3=\langle\mathbf z^\mathsf T,\mathbf z^\mathsf T C'\rangle\). Its actual rear ratio satisfies \(H(v)\kappa_3=-\kappa Q(v)\). If \(q=s,t,r\) is duplicated, use exactly the other two rear labels to form \(P_5=\sigma\prod_{x\in\{s,t,r\}\setminus\{q\}}(T-x)\). Put \(U_x=P_5/(T-x)\) for a singleton rear label, and \(I_D(T^j)=D^j/(j+1)\). Ordinary precision gives \(I_D(P_5 P_2)=0\); the other mask \(R\) is:

| Phase | \(q=s\) | \(q=t\) | \(q=r\) |
|---|---|---|---|
| Silent eighth | \(U_r\) | \(U_r\) | \(\kappa U_t-U_s\) |
| Live arithmetic | \(Q(v)U_r+H(v)U_t\) | \(\kappa Q(v)U_r+H(v)U_s\) | \(\kappa U_t-U_s\) |

In each case \(I_D(RP_2)=0\). For example at \(q=s\) in live arithmetic, \(\kappa_3 B(r)=\kappa B(t)\) uses only singleton \(r,t\); clearing \(H\) and canceling the nonzero \(\kappa\) gives the listed row. A silent **duplicated** \(r\) is not assumed to have zero grouped ordinary weight, so the \(q=r\) column uses only \(s,t\).

In live star with duplicated \(q=s\) put \(m=D-2\), \(t,r=m\mp(v-1)\). The singleton cardinal equality \(B(t)=B(r)\) gives \(I_D(\sigma P_2)=0\), since their cardinal difference is \((t-r)I_D(\sigma P_2)\). Ordinary precision on \(P_7=\sigma P_2[(T-m)^2-(v-1)^2]\) gives \(I_D(\sigma(T-m)^2 P_2)=0\). These two masks contain no \(v\). No similar simplification for a repeated \(t\) or \(r\) is claimed.

The two ordinary rows uniquely determine the two unknown coefficients of monic \(P_2\) whenever their two-by-two moment determinant is nonzero. Every certificate below checks that determinant as a unit. A necessary condition is then that \(P_2\) and \(C_4\) have a common root. This handles both assignments of the recovered two roots to \(d,e\).

## 3. Good reduction in exact number fields

The finite-gap exact field has primitive \(u+b+2v\), of degree 18 for the ghost cubic and 36 for the arithmetic sextic. The gap-free terminal-star field has primitive \(u+b\), of degree six. The replays verify irreducibility and both coordinate recovery maps; all algebraic choices of the front and rear roots therefore lie in isomorphic abstract fields. The following are simple residue roots of those primitive polynomials. The coordinates are \((p,z_0)\), with \(z_0\) the primitive residue.

| Phase and doubled rear label | \(q=a\) | \(q=b\) | \(q=c\) |
|---|---:|---:|---:|
| Ghost \(s\) | \((79,31)\) | \((17,1)\) | \((17,6)\) |
| Ghost \(t\) | \((59,1)\) | \((59,1)\) | \((17,1)\) |
| Ghost \(r\) | \((83,32)\) | \((59,1)\) | \((17,6)\) |
| Live arith \(s\) | \((103,35)\) | \((113,60)\) | \((59,28)\) |
| Live arith \(t\) | \((103,65)\) | \((103,35)\) | \((59,28)\) |
| Live arith \(r\) | \((103,35)\) | \((59,28)\) | \((59,28)\) |
| Live star \(s\) | \((43,2)\) | \((17,11)\) | \((13,9)\) |

In the \(q=a,b\) columns, \(D=1+q+jv\) for rear slot \(j=0,1,2\); for terminal star use \(D=1+q\). The exact \(C_3\) coefficients are integral at the displayed prime, its degree-two leading coefficient is a unit, and its two roots in the residue field are simple. The replay checks both roots, guarding both determinants and checking constant \(\gcd(C_4,P_2)\) separately.

In the \(q=c\) column use \(c=D-1-jv\) (or \(c=D-1\) in terminal star). The polynomial \(C_3(D-1-jv;D)\) has exact degree at most six by its construction, and indeed degree six with unit lead at the chosen prime. Work in the **entire** residue algebra \(\mathbb F_p[D]/(\overline{C_3(D-1-jv;D)})\). The check does not require a linear factor or search for rational residues of \(D\). Both recovery determinants are units throughout this quotient. With \(P_2=T^2+V_1T+V_0\), reduce \(C_4\) modulo \(P_2\) to \(A_0+A_1T\) and check that \(A_0^2-A_0A_1V_1+A_1^2V_0\) is a unit in the degree-six quotient. This one check excludes common roots above **all** possible residue values of \(D\), including nonsplit factors or multiple roots.

To explain why a chosen good reduction suffices for characteristic zero: Hensel at the simple primitive residue embeds the common exact field in \(\mathbb Q_p\). Any candidate root of a polynomial with integral coefficients and unit leading coefficient is integral at any extension of the valuation. For \(q=a,b\) apply this to \(C_3\) in the clock \(c\); for \(q=c\) apply it to the displayed degree-six polynomial in \(D\). The unit determinants make the recovered \(P_2,C_4\) coefficients integral, and the monic \(P_2\) makes either candidate root \(d\) integral. Reduction in an algebraic closure of the residue field then contradicts the checked coprimality or norm unit. This is not an inference from sampling finite tableaux and does not assert the whole chart impossible in the listed finite characteristics.

## 4. Replay and native scope

Run `python check_first_two.py MODE` and `python check_third.py MODE` for `MODE=ghost,arith,star`, with SymPy 1.14 and Python-flint 0.8. All residue choices are fixed, no search is run. The [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightEightZeroRearEarlyOverlap.lean) checks the fourth gate cancellation and the two-moment Cramer identities; the monic quadratic norm gate was independently checked in the early-repeat companion. The rooted ingress and exact field comparisons remain the mathematical and Python proof. The global ten-stage lower question is unchanged.
