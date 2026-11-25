# The order-eight donor: contraction and abscissa scope

The [diagonal-twin theorem](../../lean/RKCert/ReviewedNative/DiagonalTwin.lean)
works over any commutative ring. If two rows have the same diagonal and
agree after subtracting their respective diagonal entries, then the
corresponding Butcher weight entries agree for every tree. Merging the
two columns and adding the output weights preserves `HasOrder p A b`.
For a lower triangular tableau, keeping the earlier twin also preserves
lower triangularity and every retained diagonal. The typed example
checks the contraction with retained index 2 and deleted index 4,
both zero based, from 12 stages to 11. It takes the actual corrected-row
identity as a premise; it does not certify the donor's parameter root
or its chart identities.

The abscissa restriction is independent. On the guarded chart let
\(13/32\le s\le14/32\), \(1/8\le t\le13/100\), and set
\[
 z\coloneqq(1+3s)/2,\qquad
 Z(v)\coloneqq(v-2)(v-1-s)(v-2s)(v-2t),\qquad
 M_j\coloneqq840\int_0^{2z}v^jZ(v)\,dv\quad(0\le j\le3).
\]
The scaling by 840 makes the coefficients of the \(M_j\) integers.
Define the three Cramer numerators by
\[
 D\coloneqq M_0M_2-M_1^2,\quad
 N_1\coloneqq M_1M_2-M_0M_3,\quad
 N_0\coloneqq M_1M_3-M_2^2.
\]
The monic quadratic \(B_*\) in the original coordinate is determined
by these moment equations. In the doubled coordinate its cleared form is
\[
 4D B_*(v/2)=Dv^2+N_1v+N_0.
\]
The [integer replay](check_sdirk_order8_node_signs_20261125.js) verifies
\(D>0\), \(N_0<0\), and \(4D B_*(z)<0\) on the whole rational box by
conversion to the tensor Bernstein basis. A uniform strict coefficient
sign is a strict sign on the box because the nonnegative basis
functions sum to one.

Consequently the two ordered real roots (b_*<c_*) obey
\(b_*<0<z<c_*\). The retained abscissae \(1-c_*/z<0\) and
\(1-b_*/z>1\) belong to different rows from the deleted diagonal twin.
This excludes an additional all-positive or unit-interval abscissa
requirement for this donor. It does not conflict with strict SDIRK
as used here, which imposes lower triangularity and a common nonzero
diagonal. The integer replay is not a proof of the chart's existence;
it does not search for or evaluate any parameter root.
