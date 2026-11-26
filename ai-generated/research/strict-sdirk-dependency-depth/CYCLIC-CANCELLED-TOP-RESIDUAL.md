# A three-hole residual rigidifies the cyclic cancelled-top chart

Mathematical source-only proof, not kernel-checked. Let \(A=\gamma I+B\)
be a triangular common-diagonal RK tableau over a characteristic-zero
field, with \(s=p+1,\ p\ge8\), passing every order condition through
\(p\). Assume the actual physical full chain is nonzero, and that
the top **paid** tall coefficient \(\lambda_{p-1}=b^TB^{p-1}e\) is zero.
The preceding vanishing-chart theorem supplies full physical
cyclicity at these orders; here it can simply be assumed.
Use
\[
        L=b_s\prod_{i=2}^s B_{i,i-1}\ne0
\]
as an actual physical product, without assigning it the value of
any unpaid tall moment. The proof uses only rooted orders at most
\(p\).

**Main structural conclusion.** The paid moments force either
an arithmetic prefix through \(s-4\), or two literal arithmetic
runs, anchored at the first and last physical stages, with just
three unresolved clocks between them. Both steps in the split
case are nonzero; its last clock is \(1-\gamma\) and its actual
penultimate output weight is nonzero. Normalized one-hole
occupation sums are affine on the interior gaps of these runs.
In particular if no two clocks at index distance at least two
are equal, the whole ordered tableau can be recovered rationally
from at most twelve scalar inputs per split chart over
\(\mathbb Q(\gamma)\), or eleven in the no-split chart.
This is a necessary-data reduction only, not an existence,
finite-attainment, or stage-number claim.

## 1. Path bands and the cancellation

Put \(n=p-2=s-3\), \(x_i=c_i-\gamma\), and
\(g_i=x_{i+1}-x_i\). For a physical hole set \(H\), \(w_H\) is
the actual path weight of its increasing retained list, namely
its product of strict entries times the last retained output
weight. If an entry is zero, this weight is zero.
Each contiguous omitted interval replaces a consecutive
segment of the full path by its actual skip, or modifies a
boundary. For separated intervals these modify disjoint blocks
of edges, possibly sharing a retained vertex. Thus after
dividing by \(L\) the normalized weights multiply across
separated omitted intervals. This uses no positivity and
does not divide by a skip weight.

Write \(\omega_i=w_{\{i\}}\) and \(\Omega_{ij}=w_{\{i,j\}}\)
for \(i<j\). Set
\[
       U_k=\sum_{i\le k}\omega_i,\qquad
       \sigma_k=g_k U_k/L,\qquad
       G^-_k=\sum_{i<j\le k}\Omega_{ij},\quad
       G^+_k=\sum_{k<i<j}\Omega_{ij}.
\]
The paid one-hole band has \(p\) retained sites and no mark
budget; its sum is \(\sum_i\omega_i=\lambda_{p-1}=0\).
In particular \(\sum_{i>k}\omega_i=-U_k\).
The paid two-hole band has \(n+1\) retained sites, total
\(M=\lambda_n\ne0\), and one clock mark available.
The paid three-hole band has \(n\) retained sites and two
clock marks available.

The scalar recurrence for the paid tall coefficients is
\[
 \lambda_j=\sum_{u=0}^{j}\binom ju
        \frac{(-\gamma)^{j-u}}{(u+1)!},\qquad
 (j+2)\lambda_{j+1}=(1-2(j+1)\gamma)\lambda_j-j\gamma^2\lambda_{j-1}.
\]
It implies \(\gamma\ne0\), \(M\ne0\), and
\(\lambda_{n+1}=0\). Put
\[
 \epsilon=\frac{1-2\gamma}{n},\quad
 v=\frac{\gamma\lambda_{n-1}}{M},\quad t=\frac{\epsilon}{\gamma}=v+2 .
\]
The same paid formal clock model as before sends \(C\) to
multiplication \(X\), \(B\) to \(T=J-\gamma I\) for formal
integration \(J\) from zero, and the output to integration
from 0 to 1. Expansion of \(B\) just uses unary lifts, and
a clock multiplier adjoins a leaf at the current root.
A word with \(d\) strict hops and \(j\) clock marks pays
at most \(d+j+1\) rooted vertices.
The one-mark formula for the two-hole band, using
\([X,J]=J^2\) and \(\lambda_{n+1}=0\), gives the shifted
clock mean at occupied slot \(k\) as
\(M(k-1)\epsilon\).

In the two-hole band the number of holes passed at slot \(k\)
is 0, 1, or 2. The offset-one event is
\(i\le k,\ j>k+1\), so its weight is
\(-U_kU_{k+1}/L\) by separated-hole factorization and
the actual signed one-hole sum. The offset-two event has
weight \(G^-_{k+1}\), and the offset-zero event has weight
\(G^+_k\). Subtract the two extreme clock values in turn
from the paid mean to get
\[
\begin{aligned}
 (g_i+g_{i+1})G^-_{i+1}
        &=M((i-1)\epsilon-x_i)+g_i U_iU_{i+1}/L,\\
 (g_{j+1}+g_{j+2})G^+_{j+1}
        &=M(x_{j+3}-j\epsilon)+g_{j+2}U_{j+1}U_{j+2}/L .
\end{aligned}
\tag{1}
\]
Here \(1\le i\le j\le n\), so both two-hole marked slots
\(i\) and \(j+1\) exist. There is no division by a clock gap.

## 2. The exact three-hole residual

Let \(Z_i\) denote the shifted clock at occupied position \(i\)
of a three-hole path. Consider the paid two-mark product
\((Z_i-x_i)(Z_j-x_{j+3})\), for \(i\le j\).
If its offset at \(i\) is zero or its offset at \(j\) is
three, the product vanishes. The only remaining offset
pairs are \((1,1),(1,2),(2,2)\).
For clarity, writing the three physical hole indices as
\(r_1<r_2<r_3\), these cases have exact aggregated weights:
\[
\begin{array}{c|c|c}
 \text{offsets} & \text{index conditions} & \text{weight}\\ \hline
 (1,1) & r_1\le i,\ r_2>j+1
        & U_iG^+_{j+1}/L\\
 (1,2) & r_1\le i,\ i+2\le r_2\le j+1,\ r_3>j+2
        & -U_i(U_{j+1}-U_{i+1})U_{j+2}/L^2\\
 (2,2) & r_2\le i+1,\ r_3>j+2
        & -G^-_{i+1}U_{j+2}/L .
\end{array}
\]
The conditions follow because the threshold for having
passed the \(h\)-th hole at an occupied slot is
\(r_h-(h-1)\). In the first and third cases the isolated
hole is separated from the other two, and in the middle
case all three are separated. This justifies all the
factorizations, including internal adjacent pairs in
\(G^\pm\) and boundary omissions.

The clock factors in the three rows are respectively
\(-g_i(g_{j+1}+g_{j+2})\), \(-g_i g_{j+2}\),
and \(-(g_i+g_{i+1})g_{j+2}\).
Multiply each row by its clock factor, substitute (1),
and sum. All terms with three cumulative weights cancel:
their shared multiplier times
\(-U_{j+1}+(U_{j+1}-U_{i+1})+U_{i+1}\) is zero.
The result is the exact division-free clock residual
\[
 \boxed{\
   \langle(Z_i-x_i)(Z_j-x_{j+3})\rangle
       =M\big[\sigma_i(j\epsilon-x_{j+3})
                +\sigma_{j+2}((i-1)\epsilon-x_i)\big],
                 \quad 1\le i\le j\le n .\
       }
 \tag{2}
\]
This uses the actual zero one-hole total twice: in the
two-hole offset-one cut and in the three-hole rectangles.
It retains neither an independent two-run interval weight
nor a cubic term in the one-hole cut masses.

## 3. Formal target and the triangular rank-two system

Set
\[
 Q=\gamma^2\lambda_{n-2}/M,\quad R=\gamma^3\lambda_{n-3}/M,
 \quad S=1+2v+Q,\quad V=4+6v+4Q+R,\quad K=v^3-2vQ+R.
\]
The paid scalar recurrence gives
\((n-1)Q=nv^2+2v-n-1\) and
\((n-2)R=(nv+4)Q-nv\). Hence
\[
 K=\frac{C_{n+1}(t)}{(n-1)(n-2)},\qquad
 C_m(t)=(m+1)t^3-4m t^2+2(m-3)t+4.
\]
The top zero \(\lambda_{n+1}=0\) and
\(t=(1/\gamma-2)/n\) imply \(K\ne0\) by the exact
alpha-one Laguerre/cubic exclusion proved earlier.
This uses that paid scalar only.

To check the formal double-mark expression, put
\(a=i-1,\ b=j-1\). The normalized shifted one-mark
moments in this band are \(1+aS,\,1+bS\), upon
dividing by \(M\); its total is \(M v/\gamma\).
The normalized shifted two-mark moment, divided by
\(\gamma M\), is
\[
             t(1+b)+a(8+7v+2Q)+a(b-1)V .
\]
This follows from the unshifted two-mark formal polynomial
\(2J^2T^{n-1}+ (b+3a)J^3T^{n-2}
                          +a(b-1)J^4T^{n-3}\) on 1,
followed by two shifts by \(\gamma\).
All terms have maximal formal tall index \(n+1=p-1\).

Center the two actual baseline clocks in (2) by defining
\[
 \begin{aligned}
 d_i&=x_i/\gamma-(i-1)t,& e_j&=x_{j+3}/\gamma-jt,\\
 B_a&=1+a(S-tv), & A_b&=1+bS-(b+1)tv .
 \end{aligned}
\]
The model value of
\(\langle(Z_i-a\epsilon)(Z_j-(b+1)\epsilon)\rangle/(\gamma M)\)
is \(a(b-(n-1))K\). To verify, its \(ab\) coefficient is
\(V-2tS+t^2v=K\); its coefficient of \(a\) with \(b=0\)
is \(v^3+2v^2-v-(v+4)Q-R=-(n-1)K\), by the two displayed
scalar recurrences. Its \(a=0\) term cancels exactly.
Adding the two centered deviations then makes the normalized
model value in (2)
\[
     a(b-(n-1))K-d_i A_b-e_j B_a+v d_i e_j.
\]
By (2) its actual value is
\(-\sigma_i e_j-\sigma_{j+2}d_i\).
For \(2\le i\le j\le n-1\) define
\[
  P_i=\frac{(d_i,\,\sigma_i-B_{i-1}+v d_i)}{i-1},
 \qquad
  Q_j^{\rm vec}=\frac{(\sigma_{j+2}-A_{j-1},\,e_j)}{n-j}.
\]
The paid identity is the constant triangular pairing
\[
                          P_i\cdot Q_j^{\rm vec}=K\ne0 .
 \tag{3}
\]
Here the dot is the ordinary bilinear coordinate pairing
over the coefficient field, not an inner product or a
sign assumption. At \(j=n\), before dividing by zero,
the right target is zero instead. The known scalar
\(A_{n-1}=1+(n-1)S-ntv=-1\) from the same recurrence
gives the exact terminal condition
\[
 P_i\cdot Q_{\mathrm{end}}=0,\qquad
 Q_{\mathrm{end}}
        =\big(\sigma_{s-1}+1,\ (c_s+\gamma-1)/\gamma\big),
                         \quad 2\le i\le n-1.                \tag{4}
\]

## 4. Literal clock runs and weight constraints

All \(P_i\)'s in (3) pair with the same last
\(Q_{n-1}^{\rm vec}\) to give the same nonzero scalar.
Thus if distinct they are nonproportional and linearly
independent in dimension two. If all \(P_i\) coincide,
the first coordinate gives \(x_i=(i-1)\alpha\) on
\(2\le i\le n-1\). Since \(x_1=0\), the literal prefix
through \(n-1=s-4\) is arithmetic. The step
\(\alpha=x_2=B_{21}\) is nonzero by physical cyclicity.
The second coordinate makes \(\sigma_i\) affine there
with constant term 1. This extends to \(i=1\) because
\(\sigma_1=g_1\omega_1/L=1\), where
\(\omega_1=L/B_{21}\) is the actual path omitting the
first physical stage. On every adjacent gap wholly
within that prefix, \(g_i=\alpha\ne0\), so its normalized
one-hole cumulative \(U_i/L=\sigma_i/\alpha\) is affine.
Even in this no-split chart, (4) imposes one terminal
linear relation on the clock and weight data.

Otherwise let \(i_0\ge3\) be the first \(P_i\ne P_2\).
Then \(P_2,P_{i_0}\) are independent and impose for each
\(j\ge i_0\) the same two linear equations in
\(Q_j^{\rm vec}\). Thus all these vectors coincide, and
(4) forces \(Q_{\mathrm{end}}=0\) outright. In particular,
\[
                 c_s=1-\gamma,\qquad \sigma_{s-1}=-1 .
 \tag{5}
\]
From the constant \(P_i\)'s the prefix through \(i_0-1\)
is arithmetic exactly as above. From the constant
\(Q_j^{\rm vec}\)'s, for scalars \(\rho,\tau\),
\[
       x_{j+3}=j\epsilon+(n-j)\rho,\qquad
       \sigma_{j+2}=A_{j-1}+(n-j)\tau,
                            \quad i_0\le j\le n-1 .
\]
By (5) the same formulas hold at \(j=n\), since
\(n\epsilon=1-2\gamma\) and \(A_{n-1}=-1\).
Hence the tail is literal physical \(i_0+3,\ldots,s\),
arithmetic with step \(\beta=\epsilon-\rho\).
It includes at least the final two stages, and
\(\beta=g_{s-1}\ne0\) because \(\sigma_{s-1}=-1\).
Since \(U_{s-1}=-\omega_s\), equation (5) also gives
\(\omega_s/L=1/\beta\ne0\), an actual penultimate-output
constraint \(b_{s-1}=b_s B_{s,s-1}/\beta\ne0\).
On each adjacent gap wholly inside the tail,
\(U_i/L=\sigma_i/\beta\) is affine.
Thus actual normalized one-hole weights themselves
are constant well inside either run, as differences
of these affine cumulative values. The two runs need
not have the same step. The three unprescribed middle
clocks have physical indices \(i_0,i_0+1,i_0+2\);
no artificial arithmetic or clock-distinctness restriction
is imposed there.

## 5. Constant-size reconstruction frontier

For each split index the clock array in the split branch
has at most five scalar inputs: the two run steps and
the three middle clocks. The prefix and tail origins are
anchored by \(c_1=\gamma,\ c_s=1-\gamma\).
The \(\sigma\) formulas on the two sets of adjacent
interior gaps have two additional scalar slope/cut
inputs altogether, one for each run, with the given
endpoint normalization. The two runs contain \(s-3\)
physical stages, hence their interior gaps number \(s-5\).
Those gaps determine \(s-5\) of the \(s-1\) normalized
one-hole cumulatives \(U_i/L\); at most four remaining
cumulatives are inputs. The entire one-hole vector
follows by differences since its total is zero.
Keeping the actual, unpaid \(L\) as a further scalar
gives at most \(5+2+4+1=12\) inputs.
In the no-split branch the arithmetic prefix of length
\(s-4\) gives one step and four remaining clocks; the
cut formula has one scalar and four remaining
cumulatives, plus \(L\), hence at most eleven inputs.
These are upper bounds on rational input data, not
claims of independence of the parameters. The terminal
equations and other paid tests may restrict them further.

If \(c_i\ne c_j\) for every \(j-i\ge2\), the existing
one-mark run recurrence reconstructs the rest of the literal
tableau from these inputs. Indeed at physical hole grade
\(h\ge2\), total and first marks are paid at order at most
\(s-h+1\le p\). Disconnected hole sets of size \(h\)
are already determined by shorter intervals via their
actual run product. Subtract them. The residual total
and first mark at slot \(i\) determine the cumulative
weight of contiguous \(h\)-runs starting at at most \(i\)
by dividing their residual difference by \(c_{i+h}-c_i\).
These gaps are nonzero by the stated hypothesis, so this
gives all next interval weights inductively.
Leading intervals recover actual adjacent products,
internal intervals all strict entries, and trailing
intervals all output weights, with the same diagonal.
Only the actual initial seed \(L\) and the one-hole
weights are required to start that inverse.
No such reconstruction is claimed where a required
longer-range clock gap vanishes, but (1)--(5) still
hold there.

The scalar diagonal is fixed by the paid root condition
\(\lambda_{p-1}=0\) (its reciprocal has the alpha-one
Laguerre degree \(p-1\) over the rational prime subfield).
The new result is the structural and rational-data
reduction, not classification of feasible roots,
attainment, or another stage floor.

The 12 and 11 counts are upper bounds on sufficient reconstruction data, not counts of independent parameters or claims of attainment. Conditions on nonzero distance-at-least-two clock gaps apply only to the reconstruction, not to the structural clock constraints.
