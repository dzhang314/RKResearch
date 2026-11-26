# Tight-rank scalar data with one head and no early Beta factorization

This is a countermodel to sufficient conditions stated only in terms of clock subspaces, model ranks and scalar moments. It is **not** a Runge--Kutta tableau construction; no actual \(A\), rooted recursion or higher ordinary accuracy is posited. Instead it shows why the genuine unary increment in the [delayed-closure proof](DELAYED-CLOCK-CLOSURE.md) is needed.

Fix any \(d\ge6\) and \(1\le h\le d\), and set \(p=2d+1\). Work over an algebraic extension of \(\mathbb Q\) containing the distinct roots \(\mathcal R\) of the paid scalar Radau \(Q=X\pi_d\). Its actual scalar quadrature weights \(\omega_r\) are nonzero and exact through degree \(2d\), as in the companion model proof. Choose \(h+1\) distinct additional head clocks \(\mathcal H\), disjoint from the roots of \(Q\), with \(1\in\mathcal H\) and some \(x_*\in\mathcal H\setminus\{1\}\). Thus all head clocks are nonzero.

Use one physical row for each Radau clock (the first row being the origin), and two physical rows, provisionally called the first and second, at each head clock. In addition use \(d-1\) copies of the origin type, with zero output coefficients. Define the actual numerical subspace \(U\) to consist of all vectors constant on each clock. Define \(w\) to be one on each second head row and zero at every other row. The data space and clock span are
\[
 E=U+wP_{<h}(\mathbf c),\qquad
 W=E+CE=U+wP_{<h+1}(\mathbf c).
\]
Both sums are direct, since the head is zero at the first row of each head clock and present at its second row. The clock span is invariant because there are exactly \(h+1\) effective head labels. In particular the one-step clock gain is one. The subspace \(U\) contains all clock polynomial evaluations and the literal constant.

Let
\[
       N(X)=\prod_{x\in\mathcal H}(X-x)
                 \prod_{\substack{r\in\mathcal R\\r\ne0}}(X-r).
\]
This is a disjoint product of \(h+d+1\) factors. Give each head second row output \(\rho_x=1/N'(x)\) and its first row output \(-\rho_x\). Give the Radau rows their \(\omega_r\). All additional origin-copy outputs are zero. These weights define \(b\). Let \(\alpha(0)=0\) and use the Radau interpolation polynomial \(\alpha\) of degree at most \(d\) with
\[
                      \omega_r\alpha(r)=-1/N'(r)\qquad(r\ne0).
\]
Define the separated model map \(\sigma:E\to K[X]_{\le d}\) to interpolate \(u\in U\) at its Radau-clock values, and to give \(\sigma(wT)\) the Radau-clock values \(\alpha(r)T(r)\). Then \(\sigma(P(\mathbf c))=P\) through degree \(d\), the numerical pure space is \(F=\ker\sigma\), and every pure vector has zero literal origin coordinate. The model of \(U\) is full.

These data have all the paid scalar moments of ordinary order on \(E\):
\[
            bC^j v=\int_0^1 X^j \sigma(v)(X)\,dX
                    \qquad(v\in E,\ 0\le j\le d).
\]
For \(v\in U\) this follows because the two head weights cancel and the Radau weights are exact through \(2d\). For \(v=wT\), the left side is the head measure applied to \(X^j T\) and the right side the Radau measure with weights \(\omega_r\alpha(r)\). Their difference is exactly the barycentric null column on the roots of \(N\), which kills degree at most \(h+d-1\); that covers \(j+\deg T\). Equation \(\sigma(Cv)=X\sigma(v)\bmod Q\) also holds whenever \(v,Cv\in E\), both by these moments and directly on the head powers.

Order the rows as follows: all Radau rows first, then all first head rows, then the \(h-1\) second head rows other than those at \(x_*,1\). Place the second rows at \(x_*,1\) immediately after these, and the \(d-1\) origin copies last. The total stage-count parameter is
\[
 s=2d+2h+2=p+\dim F,\qquad \dim F=2h+1.
\]
Thus it has exactly the ordinary tight-rank numerical relation under discussion, but not a claim of actual stage-minimal RK existence. The target early cutoff \(k=s-p+d=d+2h+1\) is precisely after the \(h-1\) early second head rows. Let \(H\) be their monic clock hull. The vector \(v=wH(\mathbf c)\in E\) vanishes on the entire prefix through \(k\). Its two later physical components are at \(x_*,1\), and
\[
                 b(I-C)v=(1-x_*)\rho_{x_*}H(x_*)\ne0 .
\]
Consequently these scalar data do not permit the early Beta factorization. The late model has nonzero values at every nonzero Radau root, so it does not violate the paid exclusion of a single effective atom.

In this countermodel the invariant core \(U\) has the full formal model and \(h\le d\). One may pick a pure generator by subtracting from \(w\) a suitable \(U\)-vector to remove \(\alpha\). But restoring zero values at the chronological core pivots gives back the displayed \(w\), not a pure vector. Thus neither a small head height nor the existence of a pure abstract generator replaces that measured chronological condition. If these scalar data could come from a genuine order-\(p\) tableau with the same measured \(E\), the actual late \(Av\) would have to leave the first clock closure \(W\), by the companion rank/rent theorem. This is the precise distinction exposed by the model.
