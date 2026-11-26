# Fewer scalar sites for signed-reverse explicit methods

Allowing rational gaps instead of gaps invertible in \(\mathbb Z[1/19!]\) reduces the signed-reverse order-nineteen example from 71 to **70 stages**. Over the real algebraic numbers, the same approach gives examples of order nineteen in 67 stages and order twenty in 75 stages. The latter two counts do not improve the existing real-algebraic bounds of 46 and 51 stages.

## Quadrature with prescribed sites

In the centered reverse coordinate \(u\), write
\[
\langle f\rangle\coloneqq \tfrac12\int_{-1}^1 f(u)\,du,\qquad
H(u)\coloneqq\prod_{i=1}^n(u-u_i).
\]
For distinct sites \(u_1,\ldots,u_n\), the cardinal quadrature is exact through degree \(d\ge n-1\) if and only if
\[
\langle u^jH\rangle=0\qquad(0\le j\le d-n).
\]
Indeed, division by \(H\) gives a remainder evaluated exactly by cardinal quadrature. The term divisible by \(H\) vanishes at every site, so its integral must also vanish. The same argument proves necessity for any choice of masses at those sites.

For the signed reverse construction, we need degree \(p-1\) at order \(p\). The sites must contain all the reverse clocks. The two endpoint mergers use the zero row and the old forward order-nine output row, so they do not require a symmetric grid.

## Order nineteen over the rationals

Use the 27-row grade-nine forward chart from the [78-stage order-twenty construction](REFLECTED-ORDER-20.md). The reverse chart also has 27 rows and grade nine; its first four new centered sites are \(-1/3,1/3,1/2,-2\), and its last five are \(0,\pm1/3,\pm1/2\). The constructions and replay use [the reconstruction](construct.py).

Let \(H_{15}\) be the nodal polynomial of zero and both signs of \(1/3,1/2,1,2,2/3,5/6,3/2\). Its needed moments are
\[
\langle uH_{15}\rangle=-\frac{17779}{10410120},\qquad
\langle u^3H_{15}\rangle=-\frac{272231}{197792280}.
\]
The three additional sites \(a,b,c\) are
\[
a\coloneqq1/5,\qquad b\coloneqq1/7,\qquad
c\coloneqq\frac{-272231/337801-ab}{a+b}
=-\frac{4932943}{2026806}.
\]
Here \(0<b<a<1/3\) and \(-3<c<-2\). As \(H_{15}\) is odd,
\[
\big\langle H_{15}(u-a)(u-b)(u-c)\big\rangle
 =\langle u^3H_{15}\rangle+(ab+ac+bc)\langle uH_{15}\rangle=0.
\]
The 18-site grid therefore integrates degree eighteen. The signed reverse argument gives order nineteen, with \(27+27+18-2=70\) distinct rows. The size-twenty tree with a child \([\bullet]\) and eighteen other single-vertex children has defect \(-21023370096133/183907520282870415360\) in its order condition, so the order is exactly nineteen.

The [literal tableau](tableau-19-rational.json) and [next-order witness](witness-19-rational.json) can be rebuilt or checked with:
~~~sh
python construct.py 19 --rational-grid
python verify.py 19 --rational-grid
python verify-reflection-20.py --rational-grid
~~~
The unqualified order-nineteen options still give the 71-stage tableau over the factorial localization.

## Two shorter real-algebraic grids

For the same symmetric reverse grade-nine chart, define
\[
H_9(u)\coloneqq u\!\!\prod_{r\in\{1/3,\,1/2,\,1,\,2\}}(u^2-r^2),
\qquad H_{11}(u)\coloneqq(u^2-16/49)H_9(u).
\]
The monic even quartic
\[
Q(u)\coloneqq u^4-\frac{392428382}{247531411}u^2
                    +\frac{2580568171}{4208033987}
\]
satisfies \(\langle uH_{11}Q\rangle=\langle u^3H_{11}Q\rangle=0\) by exact monomial integration. It has positive roots in \((81/100,41/50)\) and \((19/20,24/25)\): its signs at the four endpoints are \(+,-,-,+\), respectively. Evenness gives two further roots, and the four intervals account for all four distinct roots. None is a root of \(H_{11}\) or equals \(-8/11\).

At order nineteen use the 15 sites of \(H_{11}Q\). Its oddness and the two moment identities give degree-eighteen quadrature. At order twenty all reverse clocks occur among these sites except \(-8/11\), so use the 16 sites of \((u+8/11)H_{11}Q\). Testing against \(1,u,u^2,u^3\) reduces by parity to the same two moment identities, giving degree-nineteen quadrature. The resulting signed-reverse row counts are \(27+27+15-2=67\) and \(27+34+16-2=75\). The next-order mixed-word defects are unchanged under these grid replacements: their scalar integrands already have degree at most \(p-1\). In the two orders, one such nonzero raw defect is respectively \(-332/5316597\) and \(47042/352546425\). Thus these methods have the claimed exact orders. The real-algebraic variants are described by their charts and nodal polynomials here, not supplied as literal JSON tableaux or Lean certificates.
