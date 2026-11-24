# Exact LaTeX source for the revised order-twelve proof


```tex
\documentclass[11pt]{article}
\usepackage[letterpaper,margin=0.95in]{geometry}
\usepackage{mathtools,amssymb,bm}
\usepackage[hidelinks]{hyperref}
\setlength\parindent{0pt}
\setlength\parskip{5pt plus 1pt}
\allowdisplaybreaks[1]
\newcommand{\e}{\mathbf e}
\newcommand{\cvec}{\mathbf c}
\newcommand{\bvec}{\mathbf b}
\newcommand{\yvec}{\mathbf y}
\newcommand{\fvec}{\mathbf f}
\newcommand{\phit}[1]{\boldsymbol{\Phi}_{#1}(A)}
\newcommand{\Q}{\mathbf Q}
\newcommand{\dvec}{\mathbf d}
\newcommand{\reals}{\mathbb R}
\newcommand{\rsum}{\mathbin{\#}}
\newcommand{\bushy}[1]{[\bullet]^{\# #1}}
\newcommand{\cpow}[1]{\cvec^{\odot #1}}
\newcommand{\spn}{\operatorname{span}}
\title{\vspace{-1.8em}An order-twelve stage bound in \(Q\) and \(D\) notation}
\author{}
\date{}
\begin{document}
\maketitle
\vspace{-2.5em}
Every real explicit Runge--Kutta method of order at least twelve has at least sixteen stages. The proof first establishes identities for arbitrary Runge--Kutta methods. Strict triangularity then gives two dimension bounds for explicit methods, which we apply at order twelve.

\section{Identities for arbitrary Runge--Kutta methods}

Let \(A\) be the stage matrix of a real \(s\)-stage Runge--Kutta method and \(\bvec\) its weight vector. No triangularity or order assumption is made at this point. The stage data are
\[
\e\coloneqq (1,\ldots,1)^\top\in\reals^s,\qquad
\cvec\coloneqq A\e,\qquad C\coloneqq\operatorname{diag}(\cvec).
\]
The Butcher weight vectors are defined in terms of extension and rooted sum:
\[
\phit{\bullet}\coloneqq\e,\qquad
\phit{[t]}\coloneqq A\phit{t},\qquad
\phit{t\rsum u}\coloneqq\phit{t}\odot\phit{u}.
\]
The rooted-sum powers are
\[
t^{\#0}\coloneqq\bullet,\qquad
t^{\#k}\coloneqq\underbrace{t\rsum\cdots\rsum t}_{k\text{ copies}}\quad(k\ge1).
\]
The bushy tree \(\bushy{k}\) has \(k\) leaves attached directly to its root. The weight recursion and the tree factorial give
\[
\phit{\bushy{k}}=\cpow{k},\qquad
(\bushy{k})!=k+1\quad(k\ge0),\qquad
\cpow{0}\coloneqq\e.
\]

\subsection*{Stage values, stage derivatives, and the stage residual}

For the equation \(\yvec'=\fvec(\yvec)\), let \(\yvec(x)\) denote the exact solution at time \(x\) with \(\yvec(0)=\yvec_0\). The Runge--Kutta stage values satisfy
\[
\mathbf Y_i=\yvec_0+h\sum_{j=1}^s a_{ij}\fvec(\mathbf Y_j).
\]
An integer superscript \((m)\) denotes the ordinary \(m\)-th derivative of \(\fvec\). A tree superscript \((t)\) denotes the elementary differential defined by
\[
\fvec^{(\bullet)}(\yvec)\coloneqq\fvec(\yvec),\qquad
\fvec^{([t_1]\rsum\cdots\rsum[t_m])}(\yvec)
\coloneqq\fvec^{(m)}(\yvec)
 \bigl(\fvec^{(t_1)}(\yvec),\ldots,\fvec^{(t_m)}(\yvec)\bigr).
\]
The symmetry factor is
\[
\sigma(t)\coloneqq\text{the number of automorphisms of \(t\) that fix its root}.
\]
At each vertex, the Taylor denominator cancels the permutations of its arguments except for permutations of identical subtrees. This leaves the factor \(1/\sigma(t)\) in the coefficient of \(\fvec^{(t)}(\yvec_0)\).

In the rooted-tree expansion of the stage derivative \(\fvec(\mathbf Y_i)\), the term for \(t\) is
\[
h^{|t|-1}\frac{\fvec^{(t)}(\yvec_0)}{\sigma(t)}\bigl(\phit{t}\bigr)_i.
\]
The stage equation multiplies the coefficients of the stage derivatives by \(hA\). Thus the term for the \emph{same} tree \(t\) in \(\mathbf Y_i-\yvec_0\) is
\[
h^{|t|}\frac{\fvec^{(t)}(\yvec_0)}{\sigma(t)}
 \bigl(A\phit{t}\bigr)_i
=h^{|t|}\frac{\fvec^{(t)}(\yvec_0)}{\sigma(t)}\bigl(\phit{[t]}\bigr)_i.
\]
Conversely, the linear term in Taylor's formula applies \(\fvec'(\yvec_0)\) to this stage increment. It changes \(\fvec^{(t)}(\yvec_0)\) to \(\fvec^{([t])}(\yvec_0)\) without changing the power of \(h\) or the symmetry factor. This is why \(\phit{[t]}\) gives the normalized coefficient for \(t\) in the stage values as well as for \([t]\) in the stage derivatives.

The exact solution satisfies \(\yvec(x)=\yvec_0+\int_0^x\fvec(\yvec(z))\,dz\). The two expansions start from the same constant term in the derivative. The exact recursion uses integration in place of multiplication by \(hA\). For \(t=[t_1]\rsum\cdots\rsum[t_m]\), the normalized coefficient in the derivative is the product of the child coefficients \(z^{|t_j|}/t_j!\), and integration gives
\[
\int_0^x\prod_{j=1}^{m}\frac{z^{|t_j|}}{t_j!}\,dz
=\frac{x^{|t|}}{|t|\prod_{j=1}^{m}t_j!}
=\frac{x^{|t|}}{t!}.
\]
For \(\bullet\), integration of the constant \(1\) gives \(x\). Thus at \(x=c_i h\) the term for \(t\) in \(\yvec(c_i h)-\yvec_0\) is \(h^{|t|}\fvec^{(t)}(\yvec_0) c_i^{|t|}/(\sigma(t)t!)\).

The \emph{stage residual} for \(t\) is
\[
\Q(t)\coloneqq A\phit{t}-\frac{\cpow{|t|}}{t!}.
\]
In the expansion of \(\mathbf Y_i-\yvec(c_i h)\), the coefficient of \(h^{|t|}\fvec^{(t)}(\yvec_0)/\sigma(t)\) is exactly \(\Q(t)_i\). This interpretation does not require the method to have any particular order.

\subsection*{The spaces spanned by stage residuals}

For each integer \(j\ge0\), define
\begin{equation}
F_j\coloneqq\spn\left\{
\cpow{k}\odot\Q(t_1)\odot\cdots\odot\Q(t_m):
m\ge1,\ k\ge0,\ k+\sum_{i=1}^m|t_i|\le j
\right\},
\label{eq:fspace}
\end{equation}
where \(m,k\) are integers and \(t_i\) are rooted trees. For a nontrivial tree \(t=[t_1]\rsum\cdots\rsum[t_m]\) the weight recursion gives
\[
\phit{t}
=\left(\frac{\cpow{|t_1|}}{t_1!}+\Q(t_1)\right)\odot\cdots\odot
 \left(\frac{\cpow{|t_m|}}{t_m!}+\Q(t_m)\right).
\]
The product of the monomial vectors in these factors is
\[
\frac{\cpow{(\sum_i|t_i|)}}{\prod_i t_i!}
=\frac{|t|}{t!}\cpow{(|t|-1)}.
\]
Every other summand contains at least one stage residual. The exponent of \(\cvec\) in that summand is the sum of \(|t_i|\) over the factors contributing monomial vectors, so the bound in \eqref{eq:fspace} is met with \(j=|t|-1\). Therefore \(t!\phit{t}-|t|\cpow{(|t|-1)}\in F_{|t|-1}\), also for \(\bullet\), for which the difference is zero. It follows that \(F_j\) contains all differences
\begin{equation}
t!\phit{t}-u!\phit{u},\qquad |t|=|u|\le j+1.
\label{eq:diffs}
\end{equation}

Conversely, each stage residual is a scaled difference of this form:
\[
\Q(t)=\frac{[t]!\phit{[t]}-(\bushy{|t|})!\phit{\bushy{|t|}}}{(|t|+1)t!}.
\]
If \(|t|=|u|\), then
\[
\frac{(t\rsum v)!}{t!}
=\frac{|t|+|v|-1}{|t||v|}\,v!
=\frac{(u\rsum v)!}{u!}.
\]
The rooted-sum recursion therefore gives
\[
\bigl(t!\phit{t}-u!\phit{u}\bigr)\odot\phit{v}
=\frac{t!}{(t\rsum v)!}\bigl((t\rsum v)!\phit{t\rsum v}-(u\rsum v)!\phit{u\rsum v}\bigr).
\]
In a generator in \eqref{eq:fspace}, \(\Q(t_1)\) is a scalar multiple of a difference of tree weights of order \(1+|t_1|\). Each remaining residual is a linear combination of tree weights of its own order \(1+|t_i|\), and \(\cpow{k}\) is the weight of \(\bushy{k}\). The identity above applies to each product in the resulting expansion. The final tree order is \(1+k+\sum_i |t_i|\le j+1\), since identifying two roots reduces the combined vertex count by one. Thus \eqref{eq:diffs} spans \(F_j\).

It follows that
\begin{equation}
CF_j\subseteq F_{j+1},\qquad AF_j\subseteq F_{j+1}.
\label{eq:closure}
\end{equation}
For the first inclusion, multiplication by \(C\) is coordinatewise multiplication by \(\phit{[\bullet]}=\cvec\), so the preceding product identity applies with \(v=[\bullet]\). For the second, the extension rule gives
\[
A\bigl(t!\phit{t}-u!\phit{u}\bigr)
=\frac{[t]!\phit{[t]}-[u]!\phit{[u]}}{|t|+1}.
\]
The extended trees have equal order at most \(j+2\) when \(|t|=|u|\le j+1\). For \(j\ge0\), define the space of weights of trees with at most \(j+1\) vertices by
\[
E_j\coloneqq\spn\{\phit{t}: |t|\le j+1\}.
\]
It contains \(F_j\) by \eqref{eq:diffs}. In \eqref{eq:diffs}, taking \(u=\bushy{|t|-1}\) expresses each tree weight as a multiple of \(\cpow{(|t|-1)}\) plus an element of \(F_j\). Since the powers of \(\cvec\) are themselves weights of the bushy trees,
\begin{equation}
E_j=F_j+\spn\{\e,\cvec,\ldots,\cpow{j}\}.
\label{eq:esplit}
\end{equation}

\subsection*{The \(D\)-type residuals}

Let \(I\) be the \(s\times s\) identity matrix. The backward \(D\)-type residuals are
\[
X\coloneqq I-C,\qquad
\dvec_k\coloneqq A^\top X^{k-1}\bvec-\frac{X^k\bvec}{k}\quad(k\ge1).
\]
The polynomial underlying \(\dvec_k\) is \((1-x)^{k-1}\). Matrix powers of \(X\) act by evaluation of these powers on the diagonal. The following spaces combine the residuals with their images under \(A^\top\) and \(X\):
\[
L_1\coloneqq\spn\{\dvec_1\},\qquad
L_k\coloneqq L_{k-1}+A^\top L_{k-1}+XL_{k-1}+\spn\{\dvec_k\}\quad(k\ge2).
\]

\subsection*{Consequences of order \(p\)}

If the method has order at least \(p\), its tree conditions imply
\begin{equation}
\bvec\cdot\cpow{m}=\frac1{m+1}\quad(0\le m\le p-1),
\qquad \bvec\perp F_j\quad(0\le j\le p-1).
\label{eq:moments}
\end{equation}
The first identity is the condition for \(\bushy{m}\). Each of the two normalized weights in \eqref{eq:diffs} has inner product \(1\) with \(\bvec\) when \(j<p\), which proves the second assertion.

For the monomial \(x^m\), the corresponding \(D\)-type vector is \(A^\top C^m\bvec-(I-C^{m+1})\bvec/(m+1)\). It is orthogonal to \(\phit{u}\) if \(m+|u|+1\le p\): the tree conditions give
\[
\bvec\cdot(C^m A\phit{u})=\frac{1}{(|u|+m+1)u!},\qquad
\bvec\cdot(C^{m+1}\phit{u})=\frac{|u|}{(|u|+m+1)u!}.
\]
The first tree is \(\bushy{m}\rsum[u]\); the second is \(\bushy{m+1}\rsum u\). Together with \(\bvec\cdot\phit{u}=1/u!\), these values give orthogonality. The residual \(\dvec_k\) is the corresponding linear combination of these vectors for the polynomial \((1-x)^{k-1}\): the exact term follows from integrating \((1-y)^{k-1}\) from \(x\) to \(1\), which gives \((1-x)^k/k\). Thus \(\dvec_k\perp E_{p-1-k}\) for \(1\le k\le p-1\).

By the weight recursion, \(A\) sends \(E_{p-1-k}\) into \(E_{p-k}\). The operator \(X\) does so as well, since for each tree it subtracts the weight of its rooted sum with \([\bullet]\) from its own weight. If \(L_{k-1}\perp E_{p-k}\), then \(A^\top L_{k-1}\) and \(XL_{k-1}\) are orthogonal to \(E_{p-1-k}\), by transposition and the symmetry of \(X\). The other summands of \(L_k\), namely \(L_{k-1}\) and \(\spn\{\dvec_k\}\), are also orthogonal to \(E_{p-1-k}\). Since \(\dvec_1\perp E_{p-2}\) when \(p\ge2\), induction gives
\begin{equation}
L_k\perp E_{p-1-k}\quad(1\le k\le p-1).
\label{eq:orth}
\end{equation}

\section{Strict growth for explicit methods}

From this point on the method is explicit: \(A\) is strictly lower triangular. Both dimension bounds use the same linear algebra fact. Let \(N\) and \(Y\) be real \(n\times n\) matrices, with \(N\) strictly triangular and \(Y\) diagonal. If a subspace \(W\subseteq\reals^n\) is invariant under both \(N\) and \(Y\), then for each \(\mathbf v\in\reals^n\),
\[
NY\mathbf v-\tfrac12Y^2\mathbf v\in W
\quad\Longrightarrow\quad Y\mathbf v\in W.
\]
For diagonal \(Y\), its Moore--Penrose pseudoinverse \(Y^\dagger\) is a polynomial in \(Y\), by interpolation on the distinct diagonal entries. Thus \(Y^\dagger\) preserves \(W\). Since \(Y^\dagger Y^2=Y\), the hypothesis gives
\[
(I-2Y^\dagger N)Y\mathbf v
=-2Y^\dagger\bigl(NY\mathbf v-\tfrac12Y^2\mathbf v\bigr)\in W.
\]
The matrix \(2Y^\dagger N\) is strictly triangular and hence nilpotent. The inverse of \(I-2Y^\dagger N\) is a finite sum of powers of \(2Y^\dagger N\), all of which preserve \(W\). Consequently \(Y\mathbf v\in W\).

Suppose the method has order at least \(p\). If \(F_{j-1}=F_j\) for \(2\le j\le p-1\), the common space is invariant under \(A,C\) by \eqref{eq:closure} and contains \(\Q([\bullet])=A\cvec-\cpow{2}/2\). The implication above with \(N=A\), \(Y=C\), and \(\mathbf v=\e\) yields \(\cvec\in F_j\). This contradicts \eqref{eq:moments}, which gives \(\bvec\cdot\cvec=1/2\) and \(\bvec\perp F_j\). Since \(F_1=\{0\}\) by \(\Q(\bullet)=0\), each strict inclusion yields
\begin{equation}
\dim F_j\ge j-1\quad(1\le j\le p-1).
\label{eq:fgrowth}
\end{equation}

Likewise, if \(L_{k-1}=L_k\) for \(2\le k\le p-1\), the common space is invariant under \(A^\top,X\) and contains \(\dvec_2=A^\top X\bvec-X^2\bvec/2\). The implication with \(N=A^\top\), \(Y=X\), and \(\mathbf v=\bvec\) yields \(X\bvec\in L_k\). But \eqref{eq:orth} gives \(L_k\perp\e\), while \eqref{eq:moments} gives \((X\bvec)\cdot\e=1/2\). Thus
\begin{equation}
\dim L_k\ge k-1\quad(1\le k\le p-1).
\label{eq:lgrowth}
\end{equation}

\section{The dimension count at order twelve}

Assume now that the explicit method has order at least twelve, and set \(p=12\). Equations \eqref{eq:orth}--\eqref{eq:lgrowth} give \(\dim F_6\ge5\), \(\dim L_5\ge4\), and \(L_5\perp E_6\). To finish, it suffices to show that \(\dim E_6\ge12\).

The seven vectors \(\e,\cvec,\ldots,\cpow{6}\) are independent modulo \(F_6\). Indeed, suppose \(q(\cvec)\in F_6\) for a polynomial \(q\) of degree at most six evaluated at each entry of \(\cvec\). The first row of \(A\) is zero, so \(c_1=0\) and every stage residual vanishes there. Thus the first component gives \(q(0)=0\), and the quotient
\[
r(x)\coloneqq q(x)/x
\]
is a polynomial of degree at most five. Then \(q(\cvec)\odot r(\cvec)\in F_{11}\) by \eqref{eq:fspace}. Its inner product with \(\bvec\) is zero by \eqref{eq:moments}. The same inner product is the integral of \(xr(x)^2\), a polynomial of degree at most eleven, by the first identity in \eqref{eq:moments}. Thus
\[
0=\bvec\cdot\bigl(q(\cvec)\odot r(\cvec)\bigr)=\int_0^1 xr(x)^2\,dx .
\]
The integral is zero only if \(r=0\), hence \(q=0\). By \eqref{eq:esplit}, the seven vectors contribute seven dimensions in addition to \(\dim F_6\), so \(\dim E_6\ge5+7=12\). Since \(L_5\) and \(E_6\) are orthogonal subspaces of \(\reals^s\), their dimensions sum to at most \(s\). Consequently \(s\ge4+12=16\). \hfill\(\square\)

\medskip
{\small The monomial residuals come from Butcher's \(C\) and \(D\) conditions (\emph{Implicit Runge--Kutta Processes}, 1964, p.~52). The stage residual \(\Q(t)\) is Stepanov's \(Q(t)\) (\emph{On Runge--Kutta Methods of Order 10}, 2025, Section~2). The columns \(\dvec_k\) use the basis \((1-x)^{k-1}\) in the \(D\) equations, rather than \(x^{k-1}\).}
\end{document}
```
