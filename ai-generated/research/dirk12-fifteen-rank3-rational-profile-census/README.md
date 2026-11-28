# DIRK12/15: the singular-denominator census of the rational cubic face

Consider the genuinely rational visible branch of the [rank-four grade-six reverse face](../dirk12-fifteen-rank3-high-visible-cubic/README.md) of ordinary real \(C(2)\) DIRK12/15 with \(f_5=3\). Use tree grade = order minus one, genuine spaces \(T_j,F_j\), their true weighted reverse flag \(\mathcal B_j\), actual literal origin and terminal \(o,t\), node matrix \(C=\operatorname{diag}(\mathbf c)\), and \(\beta\mathbf v=\mathbf b\odot\mathbf v\). Let \(D=L'_6\) be the shifted Legendre derivative and \(\mathbf h=A\mathbf c^2-\mathbf c^{\,3}/3\). The earlier packet leaves \(D(c_i)=T(c_i)h_i\) on nonzero-weight dirty rows for some nonzero polynomial \(T\) of degree at most two, with \(\beta\mathbf h^2\notin\mathcal B_6\), endpoint weights \(1/42\), and at least ten active dirty labels.

This packet rules out a coprime denominator and shows that only these two literal exceptional architectures can survive:

- If \(\deg\gcd(D,T)=1\), the single shared root \(a\) pays the sole clean interior stage, with exactly its fixed Lobatto scalar weight. There are exactly 12 live dirty rows at distinct labels, all with the regular value \(h_i=U(c_i)/V(c_i)\) where \(U=D/\gcd(D,T), V=T/\gcd(D,T)\). A repeated denominator root \(V(a)=0\) forces the label \(a\) to be clean only. Both physical directions have between five and seven dirty rows before the clean interior pivot.
- If \(\deg\gcd(D,T)=2\), then \(V\) is constant. Exactly one shared root \(a\) is anomalous, with a three-row fiber of distinct nonzero amplitudes, none equal to \(U(a)/V\), and the other shared root \(b\) pays the sole clean interior row. There are nine other live dirty rows at distinct labels (possibly one at the same label as clean \(b\)), all on the cubic \(U/V\). Actual chronology forces **two anomalous rows before the clean pivot and one after**, with four or five regular dirty rows on each side.

In the one-shared-root case the asymmetric [five-forward/seven-reverse split](asymmetric-five-seven.md) also fixes the second denominator root projectively and excludes constant or repeated-root remaining factors. No case above asserts a candidate exists, nor has either been excluded in full. The overall real stage interval remains **15–16**. No sign assumptions on individual weights or regularity assumptions on the denominator are used.

## An actual vector identity, including unweighted rows and repeats

The previous packet certifies \(Z=\{\boldsymbol\lambda\in\operatorname{Ann}T_5:\lambda_t=0\}=\mathcal B_6+\langle\beta\mathbf h^2\rangle\), \(\mathcal B_6=(\beta\mathbf h)P_3(\mathbf c)\), and \(F_6=\mathbf hP_3(\mathbf c)+\langle\mathbf h^2\rangle\). Thus weighting is injective on \(F_6\) and all \(F_6\) vanish on physical clean rows. Both endpoint cards \(\mathbf K_o=\mathbf e_o+\beta[(1-\mathbf c)D(\mathbf c)]\), \(\mathbf K_t=\beta[\mathbf cD(\mathbf c)]-\mathbf e_t\) lie in \(\mathcal B_6\), with their representations \((\beta\mathbf h)(1-C)T(\mathbf c)\) and \((\beta\mathbf h)C T(\mathbf c)\). This uses the already-closed exceptional-coefficient branches of that packet and the **true** \(5+6=11\) budget.

As well as \(\mathbf e_t\in T_6\), the ordinary literal origin satisfies \(\mathbf e_o\in T_6\): the full annihilator \(\operatorname{Ann}T_6=\mathcal B_5=(\beta\mathbf h)P_2(\mathbf c)\) is supported on active dirty rows. The scalar component of the genuine \(\mathbf e_o\) is \(-b_o(1-X)D(X)\). Indeed this degree-six polynomial evaluates to 1 at the literal origin, and its moments against powers through degree five give \(b_o\) at exponent zero, zero otherwise, by Legendre integration by parts. Subtract any putative second component and use the positive \(X\,dX\) Gram, since the difference vanishes at zero. The corresponding scalar component for \(\mathbf e_t\) is \(b_t X D(X)\). Hence both ordinary pure endpoint differences are in \(F_6\). Comparing their weighted versions to the two cards, and using injectivity of weighting on \(F_6\), gives the literal identity
\[
                       D(\mathbf c)-\mathbf h\,T(\mathbf c)=42(\mathbf e_t-\mathbf e_o).
\]
In particular a physical nonendpoint row with zero weight is not exempt: every nonendpoint row satisfies \(D(c_i)=T(c_i)h_i\), and every clean nonendpoint row is a root of \(D\) rather than a repeated literal endpoint clock. Dirty rows may still repeat either endpoint clock if the equation permits it.

## The exact three-channel polynomial span

Let \(g=\gcd(D,T)\) monic, \(\ell=\deg g\in\{0,1,2\}\), \(U=D/g\), \(V=T/g\), and \(v=\deg V\le2-\ell\). The derivative \(D\) has five simple real roots. Away from roots of \(g\), every nonendpoint row has \(V(c_i)\ne0\) and \(h_i=U(c_i)/V(c_i)\); this follows from the genuine identity and \(\gcd(U,V)=1\). At a shared root \(a\) of \(g\), \(U(a)\ne0\), even when \(V(a)=0\).

At each numerical nonendpoint label \(z\) let \(m_j(z)=\sum_{i\ne o,t:c_i=z} b_i h_i^j\), with \(m_0\) the ordinary mass. The paid cubic, squared-cubic and cubed-cubic probes are the genuine grades \(3,6,9\) and cost scalar degrees at most \(8,5,2\), respectively. They give
\[
                   \sum_z m_1(z)q(z)=\sum_z m_2(z)r(z)=\sum_z m_3(z)s(z)=0
\]
through degrees \(8,5,2\). Neither endpoints nor unweighted rows contribute for \(j\ge1\).

On every regular label \(U m_1=V m_2\) and \(U m_2=V m_3\) already hold. At a shared root, the same identities follow **fiberwise** from the two global probe combinations: use \((q,r,s)=(Uf,-Vf,0)\) and \((0,Uf,-Vf)\), with \(f\) of degree at most \(\ell-1\) to separate all shared roots. All budgets fit; in particular \(\deg Uf\le4\) in the second combination, and \(\deg Vf\le1\). Thus no division by a possibly zero \(V(a)\) is assumed. There is a scalar \(\nu_z\) at each label with
\[
            (m_1,m_2,m_3)(z)=\nu_z\bigl(V(z)^2,U(z)V(z),U(z)^2\bigr).
\]
Choose \(\nu_z=m_1(z)/V(z)^2\) at \(V(z)\ne0\); if \(V(z)=0\) then \(U(z)\ne0\), \(m_1=m_2=0\) and \(\nu_z=m_3(z)/U(z)^2\). Weight aggregation here is by numerical label; no assumption of distinct physical taps has been made.

The exact test space is
\[
           V^2 P_8+UV P_5+U^2P_2=P_{12-2\ell}.
\]
Here is a direct proof, not a dimension heuristic. If \(v>0\), represent any polynomial of degree at most \(8+2v\) modulo \(V\) by \(U^2s_0\), then its residual divided by \(V\) modulo \(V\) by \(Ur_0\). Coprimality lets \(\deg s_0,\deg r_0<v\); both corrections have degree at most \(8+2v\) because \(\deg U=5-\ell\) and \(2(5-\ell)+v-1\le8+2v\). The remainder is \(V^2q_0\) with \(\deg q_0\le8\). If \(v=0\), \(V^2P_8=P_8\) directly. The possible higher degrees through \(10-\ell+v\) have successively independent leading terms from \(UV X^j\) with \(j\le5\); the remaining ones through \(12-2\ell\) come from \(U^2X^j\) with \(j\le2\). These degree intervals have no gap, since \(v\le2-\ell\). The reverse inclusion is immediate from degrees.

It follows that \(\nu\) annihilates all scalar polynomials through \(12-2\ell\). It is nonzero: otherwise every regular dirty label would have zero ordinary mass (its nonzero amplitude is common), so each of the at least \(10-\ell\ge8\) regular dirty labels would need at least two active rows, exceeding the thirteen nonendpoint slots. By scalar Vandermonde, at least \(14-2\ell\) distinct nonendpoint labels have \(\nu_z\ne0\). This **excludes \(\ell=0\)**, over every signed or repeated arrangement and every nonzero denominator of degree at most two.

## The fixed Lobatto scalar correction and all singular budgets

Subtract the weights at the two literal endpoints. On scalar degree at most eleven the remainder is exactly the fixed five-node interior Lobatto functional
\[
          f\longmapsto\sum_{D(a)=0}\omega_a f(a).
\]
This follows from full scalar exactness of the fixed seven-node Lobatto rule: divide by \(X(1-X)D(X)\) and use \(D\perp P_4\) for \(X(1-X)\,dX\). Its endpoint weights are \(1/42\). Every interior weight \(\omega_a\) is strictly positive by applying exactness to \(X(1-X)[D(X)/(X-a)]^2\), which is nonnegative, positive off finitely many points, and supported only at \(a\) on the fixed grid.

Test this scalar rule against \(U^2 S\) and the true squared-cubic probe against \(V^2 S\) for all \(S\) of degree at most \(1+2\ell\). Both tests are paid, respectively through scalar degree eleven and cubic-square probe degree five. On all regular labels their numeric terms coincide by \(U=Vh\), and the fixed interior rule on \(U^2S\) only sees roots of \(g\). Thus on each shared root \(a\), by interpolation,
\[
       \omega_a=m_0(a)-\gamma_a,\qquad
       \gamma_a=
       \begin{cases}
           m_1(a)/(U(a)/V(a)),&V(a)\ne0,\\
           0,&V(a)=0.
       \end{cases}
\]
This is an exact **positive scalar correction at each shared root**, not a positivity assumption on any individual tableau coefficient.

At a shared root with \(V(a)\ne0\), write \(k=U(a)/V(a)\), and call a live dirty row anomalous if \(h_i\notin\{0,k\}\). The correction weights \(d_i=b_i(1-h_i/k)\) there (zero on normal dirt, equal to \(b_i\) on clean rows) have \(\sum d_i=\omega_a\), \(\sum d_i h_i=\sum d_i h_i^2=0\), by the two paid channel identities. One anomaly is impossible; if there are two they have the same nonzero amplitude and opposite weight, by subtracting one multiple of the first moment from the second, and contribute zero correction. Thus a shared root with anomalies needs at least three **nonnormal** rows: at least three anomalies themselves or two and one active clean. Moreover if three anomalous rows alone pay positive correction, their three amplitudes must be distinct by applying the two moments to the at most two distinct nonzero amplitude groups.

For \(\ell=1\) there are at least twelve \(\nu\)-effective labels, leaving at most one physical slot beyond those labels. If \(V(a)\ne0\) this rules out anomalies; any anomalous site costs at least three nonnormal rows while supplying at most one effective label. The correction then requires exactly one clean row at \(a\) and exactly twelve normal dirty singletons. If \(V(a)=0\), the channel identities give \(m_1(a)=m_2(a)=0\); if \(\nu_a\ne0\) then \(m_3(a)\ne0\), requiring at least three active dirty rows instead of one, impossible. If \(\nu_a=0\), at most one slot remains and even two dirty rows cannot be placed there. The nonzero ordinary correction again forces one clean row. All fifteen weights, including the two literal endpoints, are live in either case. The twelve dirty labels are distinct, possibly including \(a\) only when \(V(a)\ne0\).

For \(\ell=2\), \(V\) is constant and \(W=U/V\) is cubic. At least one live anomaly exists, otherwise \(\beta\mathbf h^2=\beta\mathbf h W(\mathbf c)\in\mathcal B_6\), contrary to the branch. With at least ten \(\nu\)-effective labels, an anomalous root spends at least two extra rows beyond them; the other shared root needs at least one extra correction row. There is room for only these extras: both roots cannot be anomalous; the anomalous one \(a\) is effective, has exactly three nonnormal rows, and no additional normal row; the other \(b\) has precisely one clean row. Two canceling anomalies and a clean stage at \(a\) would have \(m_1(a)=0\), making that site ineffective and overspending an extra slot. Thus \(a\) has three distinct anomalous amplitudes and no clean row, with nine normal dirty singletons and one clean row at \(b\) elsewhere. A normal dirty row may coexist at numerical label \(b\). All weights are live and there is no further clean or unweighted physical row.

## Actual chronology at the lone clean interior row

In either chart \(F_6\) and \(\mathcal B_6\) vanish at the lone clean pivot and at both literal endpoints. Ordinary and weighted reflected primitive reads at the clean pivot are therefore exact through scalar degree five. These statements refer to the true physically triangular arrays \(A\) and reversed \(N=A^{\mathsf T}\), not a hypothesis that an adjoint tableau obeys all rooted equations.

For \(\ell=1\), let \(\mathbf v=U(\mathbf c)-\mathbf h V(\mathbf c)\), of genuine grade at most four. It is supported on just the three clean rows, with scalar profile \(U\) (quartic). For \(\ell=2\), set \(\mathbf v=(C-a)(W(\mathbf c)-\mathbf h)\). It has the same property and its quartic profile is \((X-a)W\). In each case the clean pivot clock \(b\) is the unique root of \(D\) omitted from that quartic factor (write \(b=a\) in the \(\ell=1\) notation). Multiplying by \(C\) kills the forward origin, producing a genuine grade-five input with first nonzero physical coordinate at \(b\). Its ordinary primitive there gives
\[
                   A_{ii}\, b P(b)=\int_0^b XP(X)\,dX ,
\]
where \(P\) is the quartic profile. This is a **nonzero** diagonal by the fixed arithmetic below. In particular no grade-seven commutator is needed to derive it.

In \(\ell=2\), the anomaly triple has a row on each side of the clean pivot. Otherwise in the corresponding direction use the grade-four contrast \(C(W-\mathbf h)\) or its actual weighted reflected analogue with \(1-C\), which vanishes on all the regular dirty rows and that direction's origin. Its first nonzero coordinate would then be the clean pivot. The genuine commutator of grade six forces zero diagonal, contradicting the just-verified diagonal. Now take the actual grade-five weighted reverse vector \(\beta[(1-\mathbf c)\mathbf v]\); it has scalar profile \((1-X)(X-a)W(X)\) and zero coordinates through every anomaly on the reverse-before-pivot side. At each such row, chronological primitive followed by genuine \(\mathcal B_6=(\beta\mathbf h)P_3\) purity yields
\[
               \int_a^1(1-X)(X-a)W(X)\,dX + h_i S(a)=0
\]
for the same polynomial \(S\). Two such rows have different \(h_i\), forcing the fixed integral to vanish. It is nonzero for all twenty ordered fixed roots \((a,b)\), as checked below. Thus there is exactly one anomaly after the pivot in forward order, and two before it.

For completeness the numbers of preceding regular dirty sites also have a tight cut. In a direction with clean clock \(u>0\), take a genuine grade-four contrast \(P(\mathbf c)-\mathbf hQ(\mathbf c)\) with \(\deg P\le4,\deg Q\le1\) (multiply by weights and reflect clocks in the reverse direction). If it vanishes strictly before that pivot, the nonzero diagonal and grade-six clean commutator force \(P(u)=0\), and then its primitive and primitive after one extra scalar power force \(JP(u)=J[XP](u)=0\) (paid grades five and six). With \(P(0)=0\), these three conditions give a scalar profile space of dimension at most one: divide by \(X(X-u)\) and use the positive \(X(u-X)\) Gram on the remaining quadratics against degrees at most one. If also \(P(d)=0\) at a second fixed interior clock \(d\ne u\), those same tests force \(P=0\) by the [fixed \(2\times2\) determinant receipt](../dirk12-fifteen-rank3-four-active-cubic/README.md).

- With no anomalies (\(\ell=1\)), the seven input coefficients, one origin condition and \(m\) earlier distinct dirty conditions leave at least \(6-m\) profiles. The map to \(P\) is injective as soon as there are two distinct earlier dirty labels, since a pure \(Q\) would vanish there. Fewer than two distinct earlier dirty labels is impossible already by scalar exactness through degree five on at most three proposed nodes including the true origin: use \(X\) times a squared hull of the other at most two nodes. Thus \(m\ge5\) in each direction.
- On the forward side with two anomalies at \(d\) (\(\ell=2\)), they force \(P(d)=Q(d)=0\). There are at least \(4-m\) profiles with \(m\) earlier regular dirty labels. The same injection holds using \(d\) and one regular label; if \(m=0\) scalar exactness directly fails as above. All profiles must be zero by the fixed \(2\times2\) determinant, so \(m\ge4\).
- On the reverse side with one anomaly (\(\ell=2\)), there are at least \(5-m\) profiles with \(m\) earlier regular labels and one anomaly. The same injection holds and the scalar profile space has dimension at most one, giving \(m\ge4\). This covers the possibility that a regular dirty clock equals the clean pivot clock or a literal endpoint number: the constraints are on physical rows, so those coincidences cannot increase their rank or destroy the injection at two distinct *dirty* labels.

## Exact arithmetic and native scope

For the diagonal numerator evaluate \(J[X D/(X-b)](b)\) up to the harmless leading coefficient when \(b\) ranges over the five roots of \(D\). For the anomaly gate evaluate \(J^\ast[(1-X)D/(X-b)](a)\) when \(a,b\) are distinct fixed roots, where \(J^\ast f(x)=\int_x^1 f\). The dependency-free replay tests all five and twenty cases independently modulo \(43\) and \(181\). Their symmetric products, with units in the fixed denominators and the leading coefficient, prove characteristic-zero nonvanishing with no modular specialization of unknown tableau coefficients. The known affiliated opposite-diagonal comparison is identically zero and is not used as a certificate. The portable **DIRKOrderTwelveFifteenRationalProfileArithmetic** checks the same fixed diagonal and anomaly numerators modulo 43 on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1, importing the prior fixed-grid core module. **DIRKOrderTwelveFifteenRationalProfileChannels**, checked on Lean/Mathlib 4.36.0, proves the shared-root channel normalization without inverting the possibly zero remaining denominator, the local two-root separation and the two-amplitude cancellation. The actual rooted probes are separately native in the four-active-label packet. The mathematical polynomial-span closure, singular census and chronological cuts above are not an end-to-end Lean exclusion.

    python3 -B check.py
    python3 -B check-asymmetry.py
    sha256sum -c sources.sha256

From **ai-generated/lean** in the pinned Lean/Mathlib environment:

    lake build RKCert.ReviewedNative.DIRKOrderTwelveFifteenRationalProfileArithmetic
    lake build RKCert.ReviewedNative.DIRKOrderTwelveFifteenRationalProfileChannels
