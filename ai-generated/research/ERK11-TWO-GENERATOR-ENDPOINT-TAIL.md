# The actual two-generator ERK11 endpoint tail

This supplies the normal-form prerequisite of the
[all-live analysis](ERK11-ALL-LIVE-ENDPOINT-REDUCTION.md).
Assume a 17-row strictly explicit ordinary order-eleven method,
the [literal dense first eleven](ERK11-RANK-FREE-FIRST-ELEVEN-CUTOFF.md),
rank two on their positive shifted grade-six alias read, and
maximal alias dimension four. The paid field calculations
below need \(11!\ne0\), with no ordering.
No existence, full exclusion, or stage-floor change is claimed.

## Actual suffix modes

From the [rank-two exception](ERK11-SHARP-PREFIX-MOMENT-OBSTRUCTION.md)
and [Jacobi endpoint atom](ERK11-ARBITRARY-PREFIX-JACOBI-GATES.md),
we have \(c_{17}=1,\ bA=bY\), \(Y=I-\operatorname{diag}(c)\);
\(e_{17}\in E_6\), and row 17 is individually exact through grade
four. There are actual \(u,w\in E_6\), zero on the first eleven
and leading respectively at physical rows 12 and 13, with
\(bA^4w\ne0\). The four-word gate proves that all four adjacent
edges 13–17 are live, \(y=1-c_{13}=1-c_{14}\ne0\),
\(1-c_{15}\ne y\), \(1-c_{16}\ne0\), and
\((Y-y)w\in K e_{17}\).
Subtract the row-17 coordinate from \(w\) using the actual atom
\(e_{17}\). It is now an actual eigenvector at clock \(y\).
Its ordinary read is nonzero: \(bA=bY\) yields \(bAw=ybw\),
and the four-word ratios imply \(bAw\ne0\).
Normalize \(bw=1\).

Put \(D=A/y,\ Z=Y/y\); these are scaled word operators,
not a different RK tableau. The physical scaled clock labels
at 12–17 are \((t,1,1,p,q,0)\) with \(p\ne1,\ q\ne0\).
Define \(x_0=u,\ x_j=D^{j-1}w\) for \(1\le j\le5\).
These form a physical echelon basis, with \(x_j\) leading at
\(12+j\), and \(x_5\) a nonzero multiple of \(e_{17}\).
The reads \(b x_j\) for \(j=1,\ldots,5\) are
\(1,1,1/2,1/6,1/24\) by the known ratios.
The exact \(E_7\) late kernel is \(\langle u,x_1,x_2,x_5\rangle\)
from the reverse cap and its four independent pivots. Thus
\[
        Du=a x_1+d x_2+f x_5,\qquad
        Zu=t u+B x_1+e x_2+h x_5 .
\]
Writing \(m_j=j!\,bD^j u\), one has \(m_j=ja+d\)
for \(j=2,3,4\).
The paid words \(bD^i Zu\), \(i=1,2,3\), give
\[
             m_{i+1}=t m_i+B+\frac e{i+1}.
\]
Subtract adjacent equations and clear paid constants:
\[
               e=12a(t-1),\qquad t(m_1-d)=a.                \tag{1}
\]
If \(a=0\), rank two implies \(m_1\ne d\) since the
positive mode of \(w\) is \((1,1,1,1)\).
Then \(t=e=0,\ B=d\).
The physical last row of \(Z\) is zero, so
\(Z(u-dw)=h x_5\) forces \(h=0\).
It follows from \(bD=bZ\) that \(m_1=d\), impossible.
Thus \(a\ne0\): the leading coefficient of \(Du\) proves
that the edge 12–13 is live. All **five** adjacent edges
are now live and \(bA^m\) ends exactly at row \(17-m\)
for \(m\le5\).
Equation (1) forces \(t\ne0\).
If \(t=1\), it gives \(e=0\), and the \(i=2\) word gives
\(B=a\); evaluating \((Z-t)u\) at the physical row 13
instead gives \(B=0\), impossible.

Subtract a multiple of \(w\) and then of \(e_{17}\)
so \(u_{13}=u_{17}=0\). This sets \(B=0\) and leaves
\(a\ne0\) unchanged. Rescale \(u\) to set \(a=1\).
Writing \(v=1/t\), the remaining equations give
\[
 (d+6)(t-1)=1,\qquad e=12(t-1),\qquad
 tf=24(1-t),\qquad
                 (m_1,m_2,m_3,m_4)=(d+v,d+2,d+3,d+4).      \tag{2}
\]
For example \(m_1=1+d+f/24\) from \(Du\);
\(m_1=d+v\) comes from (1); the \(i=1\) word
then yields the first equation of (2).
For \(Q(Z)=\sum_{j=1}^4 a_j Z^j\), the actual row
\(\sum a_j j! bA^j/y^j\) is exact through grade six.
It factors on the first eleven precisely when it kills
the actual late space \(\langle u,w,x_5\rangle\).
It automatically kills the endpoint; the two explicit
modes in (2) yield the calibration
\[
                     Q(1)=0,\qquad Q'(1)=(1-1/t)Q'(0).
\]
Thus the first eleven have two exact grade-six weighted
rows, for instance those for \(Z^2(Z-1)^2\) and
\(Z(Z-1)(1-(2-1/t)Z)\), with physical weight argument
\(Z=(1-X)/y\). This is not Beta size-eight exactness.

## Normalized clock matrix and actual mixed quadratic products

The remaining actual clock columns are
\[
\begin{aligned}
 Zx_1&=x_1, & Zx_2&=x_2-x_3,\\
 Zx_3&=p x_3+(2-4p)x_4+4(p-1)x_5,&
 Zx_4&=q x_4+(1-4q)x_5,\qquad Zx_5=0 .
\end{aligned}                                             \tag{3}
\]
For \(Zx_2\), its \(x_2\) coefficient is its physical
diagonal 1; apply the three paid words \(bD^2Zx_2\),
\(bDZx_2\), \(bZx_2\) to solve the other three
coefficients in descending order: they are \(-1,0,0\).
The \(x_4\) coefficient of \(Zx_3\) follows from
\(bDZx_3=2bD^4w\), and the endpoint coefficient
from \(bZx_3=bDx_3\). The last shifted coefficient
of \(Zx_4\) likewise follows from \(bZ=bD\).
Each word on \(w\) has length at most four.

At row 15, \((Z-1)x_2=-x_3\) forces \((x_2)_{15}\ne0\),
so \((Z-t)u=e x_2+h x_5\) excludes \(t=p\).
If \(p\ne1/2\), then at row16
\((q-p)(x_3)_{16}=(2-4p)(x_4)_{16}\ne0\).
This excludes \(q=p\), while \(q=1\) would force
\((x_3)_{16}=0\) by \(Zx_2=x_2-x_3\).
Also \(q=t\) would force \((x_2)_{16}=0\) by
the actual \(Zu\) action, a contradiction.
Put \(s=(x_2)_{17}/(x_5)_{17}=(x_3)_{17}/(x_5)_{17}\)
and \(J=(x_4)_{17}/(x_5)_{17}\).
At the terminal coordinate, (3) gives
\[
       qJ=4q-1,\qquad p s+(2-4p)J+4(p-1)=0.               \tag{4}
\]
In particular \(p=0\) requires \(q=1/2\).
Write \(g=bu\). The endpoint equality \(h=-es\) and
the identity \(bZ=bD\) on \(u\) give
\(24t g+24e-e s=24(d+v)\).

Let \(\delta=Ac-c^{\odot2}/2\), and let \(M\) be its
physical diagonal multiplier. It commutes with \(Z\);
\(Mx_5=0\) by the exact terminal grade-four profile.
Both \(Mu,Mw\) are actual pure grade-eight late
vectors, since \(u,w\) have grade six. The exact grade-eight
late space is \(\langle u,x_1,x_2,x_3,x_5\rangle\);
both products are also killed by \(b,bD,bD^2\).
Writing \(L=\delta_{12}\), zero at the second site of \(u\)
therefore gives \(Mu=L u+k_2x_2+k_3x_3+k_5x_5\).
The three pure reads and zero endpoint coordinate give
\[
\begin{aligned}
24L g+24k_2+12k_3+k_5&=0,\\
6L(d+v)+3k_2+k_3&=0,\qquad
12L(2+d)+4k_2+k_3=0,\\
k_5+s(k_2+k_3)&=0 .
\end{aligned}
\]
In particular \(k_2=-6L(4+d-v)\), \(k_3=12L(6+d-2v)\).
Substituting, multiplying by \(t\), and using the
equation for \(g\) yields
\(6L((4-s)(d+6)+4v)=0\).
With (2) and \(tv=1\), this becomes \(L(ts-8t+4)=0\).
Combining with (4) without dividing by \(p\) gives
\[
            L\bigl(2pq(t+1)-2t(p+q)+t\bigr)=0.             \tag{5}
\]
If \(p=1/2\), its other factor is \(q(1-t)\ne0\), so \(L=0\).

The pure restrictions on \(Mw\), similarly, give
\(Mw=k(x_1-6x_2+12x_3-24x_5)\) with \(k=\delta_{13}\).
As an eigenvector at \(1\), its \(x_3\)-coordinate in
\((Z-1)Mw\) gives \((2p-1)k=0\).
Hence \(Mw=0\) when \(p\ne1/2\).
From \(e Mx_2=(Z-t)Mu\) compare the physical leading
site at 14: \(e\delta_{14}=eL+(1-t)k_2\).
Using (2), this gives
\[
                          2t(t-1)\delta_{14}=L .
\]
When \(L\ne0\), (5) implies \(p\ne1/2\).
Then \(w\) has zero at 14 because \(Mw=0,\delta_{14}\ne0\).
It has no other potential nonzero coordinate but 13 at
this clock, so \(w\) is a literal nonzero multiple of \(e_{13}\).
Its degree-six lift \((w,P)\) makes row 13 individually
exact through grade four: for any grade-four pair \((r,R)\),
the mixed product gives \(b(w\odot r)=\ell_0(PR)\), while
the same product with the pure bush representative
\(R(c)\) gives \(b(w\odot R(c))=R(c_{13})\).
Since \(bw=1\), these identify the literal row-13 read.

Finally when \(L=0\), the pure product formula gives \(Mu=0\).
Commute with \(Z\): \(e Mx_2=(Z-t)Mu\), then
\(Mx_3=-(Z-1)Mx_2\). Thus \(Mx_2=Mx_3=0\).
If \(p=1/2\), we already get
\(\delta_{12}=\delta_{14}=\delta_{15}=\delta_{17}=0\).
If \(p\ne1/2\), commuting with \(Zx_3\) also gives
\(Mx_4=0\), and \(Mw=Mx_5=0\); the whole tail is clean.
The grade-two defect is nonzero globally (first nonzero clock).
The full first-eleven \(E_5\) then shows that at each early
quadratic carrier all four taps \(bA^j,\ 0\le j\le3\),
have zero coefficient: the pure mixed row
\(bA^j\operatorname{diag}(\delta)\) kills \(E_5\) and is
supported on the first eleven.

ERK11TwoGeneratorTailGate.lean checks the scalar paid word
modes, normalization, actual-product elimination, and
three-clock and tied-defect gates, with rooted chronology
supplied in this note.
