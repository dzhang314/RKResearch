# Nonzero shifted top excludes \(s=p+1\) in SDIRK

**Theorem.** Let \(K\) be a field of characteristic zero or characteristic greater than \(p\), and take \(\gamma\ne0\) in \(K\). Let an actual \(s\)-stage tableau \(A=\gamma I+B\), with \(B\) strictly lower triangular in chronological order, satisfy all rooted order conditions through \(p\). For \(p\ge9\),
\[
 \lambda_{p-1}:=\mathbf b\cdot B^{p-1}\mathbf1\ne0
 \quad\Longrightarrow\quad s\ge p+2 .
\]
No assumptions on clock distinctness, adjacent entries, output signs or support are made. The zero-top branch is separate. This applies uniformly at real algebraic diagonals, including every order \(9\le p\le20\).

## 1. Two dual defects, each of grade at most two

Put \(\mathbf c=A\mathbf1\), \(C=\operatorname{diag}(\mathbf c)\). As usual the formal stage polynomial of a tree \(\tau\) of grade \(|\tau|-1\) is \((|\tau|/\rho(\tau))x^{|\tau|-1}\), where \(\rho\) is the tree factorial. Unary lift by \(A\) applies the formal polynomial primitive \(Jf(x)=\int_0^x f(u)\,du\); \(C\) multiplies by \(x\), appending a leaf at the root. Each operation raises the stage grade by at most one. The literal paid output applies the polynomial integral \(I f=\int_0^1 f(x)\,dx\). These rules follow from the tree factorial, and \(B=A-\gamma I\) consequently acts as \(T=J-\gamma I\) at cost one.

For the reverse model use \(J^*g(x)=\int_x^1 g(u)\,du\). The identity \(I(gJf)=I((J^*g)f)\) is algebraic: integrate the derivative of \((J^*g)(Jf)\), which vanishes at the endpoints. Multiplication by \(x\) is its own adjoint. Thus any cost-\(t\) combination of actual reverse context rows whose exact density is zero annihilates any grade-\(h\) actual stage combination for \(h+t\le p-1\). Similarly any forward combination with zero formal model is killed by all reverse contexts at paid total grade. These are assertions about formal witnesses expanded before payment; no formal polynomial is assumed to descend to a function on the actual stage space.

Use the forward column and the single reverse row
\[
 z=A\mathbf c-\tfrac12\mathbf c^{\odot2},
 \qquad
 y=\mathbf b^\top\big[(1-3\gamma)B-BC-2B^2-\gamma^2 I_s\big].
\tag{1}
\]
The forward model is \(Jx-x^2/2=0\). For the reverse row let
\[
 u_1=(J^*-\gamma I)1=1-x-\gamma,\qquad
 u_2=(J^*-\gamma I)^2 1=\tfrac12(1-x)^2-2\gamma(1-x)+\gamma^2.
\]
Its exact density is
\[
 (1-3\gamma)u_1-xu_1-2u_2-\gamma^2=0
\]
by direct expansion. In particular the term \(BC\), not \(CB\), gives the density \(xu_1\). The iterates \(B^i z\) and \(yB^j\) remain formal-zero with costs at most \(i+2\) and \(j+2\) respectively.

## 2. Paid dimension capacity

Let \(h,t\ge2\), \(h+t\le p-1\), \(q=\min(h,t)\). Assume \(z,Bz,\ldots,B^{h-2}z\) are independent and \(y,yB,\ldots,yB^{t-2}\) are independent. The \(q+1\) vectors \(1,\mathbf c,\ldots,\mathbf c^{\odot q}\) are independent modulo the forward defect span. Indeed the rows \(\mathbf b^\top C^i\), \(0\le i\le q\), kill that span by payment and give the Hilbert matrix \(1/(i+j+1)\) on these vectors by the bush trees. To see nonsingularity algebraically, a kernel vector \((v_j)\) would make the degree-\(\le q\) polynomial \(\sum_j v_j\prod_{k\ne j}(X+k+1)\) vanish at \(0,\ldots,q\); evaluation of the zero polynomial at \(-j-1\) then gives \(v_j=0\) for every \(j\). All cleared denominators and distinct evaluation differences are units under the stated characteristic hypothesis.

The reverse defect span is orthogonal to the whole sum of forward probes and defects, of dimension \(q+1+(h-1)\). The actual row-column pairing therefore gives
\[
                     s\ \ge\ (q+1)+(h-1)+(t-1)
                       = h+t+q-1.
\tag{2}
\]
This is a dimension argument in the full actual stage space; it does not use an output-weighted diagonal form. The highest order paid in it is \(h+t+1\le p\).

## 3. Actual long pivots, without assuming cyclicity

If a nilpotent \(B\) satisfies \(B^N z\ne0\), then \(z,\ldots,B^N z\) are independent: in a dependence multiply by a power that sends the least occurring index to the final nonzero iterate and kills all larger indices. The same holds for row iterates when \(yB^N\ne0\). The long nonzero reads used next are purely structural tests for this independence. They are not additional order payments.

Let \(\Lambda=\mathbf b\cdot B^{s-1}\mathbf1\). If \(\Lambda\ne0\), set \(N=s-1\). The only possible nonzero entry of \(B^{s-1}\) is its row-\(s\), column-1 entry, and \(z_1=\gamma^2/2\). In (1) every strict term vanishes after right multiplication by \(B^{s-1}\) (for \(BCB^{s-1}\) there are already \(s\) strict factors even with \(C\) diagonal). Hence
\[
 \mathbf b\cdot B^N z=(\gamma^2/2)\Lambda\ne0,\qquad
 yB^N=-\gamma^2\mathbf b^\top B^N\ne0.
\tag{3}
\]

Otherwise assume \(\Lambda=0\) but \(L=\mathbf b\cdot B^{s-2}\mathbf1\ne0\); set \(N=s-2\). The row \(\alpha=\mathbf b^\top B^N\) is supported on the first two coordinates, \(\alpha_1+\alpha_2=L\), and \(\Lambda=\alpha_2 B_{21}\). Directly from the first two actual rows of \(A\),
\[
 z_1=\gamma^2/2,\qquad z_2-z_1=B_{21}(\gamma-B_{21}/2).
\]
Thus \(\mathbf b\cdot B^N z=(\gamma^2/2)L+(\gamma-B_{21}/2)\Lambda=(\gamma^2/2)L\ne0\).

For the reverse row, exact full-path geometry gives
\[
 B C B^{s-2}=c_{s-1}B^{s-1}.
\tag{4}
\]
Indeed both matrices can have only the row-\(s\), column-1 entry nonzero. Its unique strict path passes through all \(s\) physical stages and \(C\) marks stage \(s-1\), so the identity holds even when the full product is zero. Also \(\mathbf b^\top B^{s-1}=\Lambda e_1^\top=0\) and \(B^s=0\). Applying these to (1) gives \(yB^N=-\gamma^2\mathbf b^\top B^N\ne0\), since \(\mathbf b^\top B^N\mathbf1=L\). This completes the actual pivot proof, including broken adjacent entries and zero terminal output weight.

## 4. Stage conclusion

A nonzero \(\lambda_{p-1}\) first implies \(s\ge p\) by strict nilpotence. If \(s=p\), then \(\Lambda=\lambda_{p-1}\ne0\); if \(s=p+1\), then \(L=\lambda_{p-1}\ne0\), and either case of the physical pivot proof applies according to the actual \(\Lambda\). Take \(t=q=\lfloor(p-1)/2\rfloor\) and \(h=p-1-q\); the required short iterates are within \(N\ge s-2\). Thus (2) gives \(s\ge p+\lfloor(p-1)/2\rfloor-2\), at least \(p+2\) for \(p\ge9\), a contradiction in both cases.

The proof uses the genuinely mixed row \(BC\) and the rooted forward defect \(A\mathbf c-\mathbf c^{\odot2}/2\); paid tall and bush conditions by themselves are not being asserted sufficient. Nor is the actual full moment \(\Lambda\) equated with an unpaid reference when \(s=p+1\).

**Ring reduction.** Over a nonzero commutative ring the paid denominator-cleared tall tree of order \(p\) makes \(p!\) a unit. The same stage conclusion follows if \(\gamma\lambda_{p-1}\) is not nilpotent. Choose a prime avoiding that product and pass from the quotient domain to its fraction field. Order conditions and strictness map to the field, and \(p!\) being a unit ensures characteristic zero or greater than \(p\). In particular both \(\gamma\) and \(\lambda_{p-1}\) being units suffices; merely nonzero nonunits in an arbitrary ring do not justify this reduction.

*Proof provenance:* the explicit two-sided paid capacity and actual near-top pivot argument are separated above; the single reverse seed is an independent audit’s combination of the two pure reverse defects and the once-leaf-decorated reverse defect.
