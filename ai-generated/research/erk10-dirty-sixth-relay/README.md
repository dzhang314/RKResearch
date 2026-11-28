# A rational size-six ghost restores an exact grade-five decoder

This is a genuinely non-pure opening ingredient for a prospective
15-stage ERK10 architecture, **not an ERK10 tableau**.
It escapes the [pure-high FSAL obstruction](../erk10-seven-opening-pure-high/README.md)
by paying size-five purity but not size-six purity at one actual
high row, the ghost. Its immediately following stage is truly pure
through derivative size six.

Start with the repository's
[seven-row rational port](../erk10-six-opening-singleton/README.md):
six true order-five rows followed by their actual FSAL at \(\xi=1\).
Append the following physical rows (indices beginning at one):
\[
\begin{array}{c|c|l}
 \text{row} & \text{clock} & \text{strict incoming coefficients}\\\hline
 8&1/3&(19/162,0,0,1250/5103,-32/729,17/1134,0)\\
 9&2/3&(74/729,0,0,2000/15309,256/2187,4/189,-1/27,1/3).
\end{array}
\]
The literal matrix and decoder are in [opening.json](opening.json).
Their common denominators are \(1224720=2^4 3^7 5\cdot7\) and
\(756=2^2 3^3 7\), so this is a single paid opening, not a local-ring
selection. The exact primitive through size five fails at row 8 on
the five-vertex bush by \(11/4860\) (equivalently its normalized
primitive value is \(3/4\) rather than \(1/5\)).
No higher-order full method is inferred.

## General causal relay geometry

For a rational six-row order-five opening with actual FSAL at a
nonzero horizon \(\xi\), the seven physical rows have exactly two
missing degree-at-most-four derivative models. Indeed the
[rational rank-four result](../erk10-rank-three-port-one-label/README.md)
gives joint physical/model dimension nine, hence the missing image
has dimension at least two. For any missing model \(f\), its primitive
\(Jf=\int_0^X f(u)\,du\) has double roots at \(0,\xi\):
\(f\) vanishes at both pure endpoints, and \(Jf(\xi)=0\) follows
from the actual order-five FSAL weights. Thus these primitives
span exactly \(J_0=X^2(X-\xi)^2,\ J_1=XJ_0\).
In particular the physical profile span on the first seven rows
is seven-dimensional.

Give the next actual row clock \(z\notin\{0,\xi\}\) and make it
pure through size five. If a new pure-through-size-six stage at
\(w\notin\{0,\xi\}\) can use that row and the original seven,
its matching coefficient \(\alpha\) into the ghost must satisfy
\[
  J_0(w)=\alpha J_0'(z),\qquad J_1(w)=\alpha J_1'(z).
\]
If \(2z=\xi\), the first derivative is zero, disallowing the
new pure clock. Otherwise these equations are equivalent to
\[
 w=\frac{z(5z-3\xi)}{2(2z-\xi)},\qquad
 \alpha=\frac{w^2(w-\xi)^2}{2z(z-\xi)(2z-\xi)}.
\]
These conditions are also sufficient for the local linear solve:
the previously unobservable grade-five modes are exactly the
two displayed derivatives and the ghost gains one independent
evaluation on them. Thus, provided \(w\notin\{0,\xi\}\),
the target primitive is in the span of the eight actual input
rows precisely under these two equations. The remaining
physical coefficients are then determined uniquely.
If the two derivative evaluations at \(z,w\) are independent on
these missing modes, all nine rows carry an exact
degree-four decoder of nominal profiles through size five.

For \(z=\xi/3\) one gets \(w=2\xi/3\), \(\alpha=\xi/3\).
The two evaluation ratios \(J_1'/J_0'\) are \(2\xi/3\) and
\(\xi/3\), proving independence. In our literal example the
ghost is built by polynomial integration on the four genuinely
pure size-four old sites \(0,3/10,3/4,1\). The exact row solve
then gives the stated relay. The decoder's evaluation at each
of \(1,1/3,2/3\) is precisely the physical coordinate vector
of the FSAL, ghost, and relay, respectively; the replay checks
this identity on all nine entries, not only selected trees.

## Verification and next constraint

Independent replay uses only the literal file and standard-library
rational arithmetic. It checks the 37/17/37 actual local derivative
profiles through the indicated respective sizes, the nonzero defect,
all 17 decoder profiles with all five polynomial coefficients, and
the three full physical alias rows.

For any complete ERK10 continuation this ghost's degree-six errors
can still appear under up to four marked or unary exterior steps.
The construction does not yet cancel those responses; raw reverse
moments and forward alias corrections have to be paid jointly.
In particular the local seed by itself makes no assumption on which
high output weights are nonzero.

    python -B build.py /tmp/dirty-sixth-opening-rebuilt.json
    cmp opening.json /tmp/dirty-sixth-opening-rebuilt.json
    python -B replay.py
    sha256sum -c sha256.txt

From ai-generated/lean:

    lake env lean RKCert/ReviewedNative/ERK10DirtySixthRelay.lean

The Lean audit checks actual normalized primitive HasOrder at the
three physical rows, the ghost's exact failed fifth primitive, and
the denominator-cleared full-tree decoder check. The general causal
rank reasoning above is the mathematical part of the packet.
