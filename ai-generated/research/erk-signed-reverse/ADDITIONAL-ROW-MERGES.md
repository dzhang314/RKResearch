# Four shorter tableaux from the same signed reverse construction

The rooted-order argument in [the construction](CONSTRUCTION.md) applies without modification. The changes concern the choice and position of the two charts and the exact identity of some pure rows with previous forward stages.

## Orders eleven and twelve

Use the nine-row grade-five forward chart \(\Pi_5\) in Section 2 of the construction. In the reverse direction use that grade-five chart at order eleven, and the eleven-row grade-six chart at order twelve. Their reverse clocks are on the grid \(j/12\) for \(0\le j\le12\). Omit \(j=1\) at order eleven and retain all the sites at order twelve. All differences are units in the corresponding coefficient ring.

In both tableaux the pure row at physical clock one equals the earlier copy of the order-six output row, since the chart prescribes that output as its zeroth moment on arbitrary data. The pure row at clock one-half also exists in the prefix. Indeed, the difference between \(\Pi_5\) and the zero-padded \(\Pi_4\), on any data, has zero endpoint values and zero zeroth and first moments. In the centered variable \(v=2x-1\) it is a multiple of \((1-v^2)(v^2-1/5)\). This polynomial is even and has zero integral on \([-1,1]\), so its integral on \([-1,0]\) is zero. Thus \(I_{1/2}\Pi_5=I_{1/2}\Pi_4\), the entire literal row at stage nine. The usual origin merge is already included in the allocated count. The two additional merges reduce 29 to 27 stages at order eleven and 32 to 30 stages at order twelve.

## Order fourteen

Use grade six forward and grade seven in reverse, rather than the other way around. Both use the same total of 27 old rows. The existing order-fourteen grid contains all reverse grade-seven sites. Now the forward chart \(\Pi_6\) pins the zeroth moment on arbitrary data, so the pure row at clock one equals the earlier literal output row. The count is \(11+16+14-1=40\).

## Order twenty

Use grade nine forward and grade ten in reverse, with the 34-row [two-read chart](TWO-PRIMITIVE-READS.md) as the actual reverse chart. Use the 21 reverse sites consisting of \(4/5\) and the fractions \(j/12\) at
\[
 j\in\{-10,-8,-6,-4,-3,0,2,3,4,6,7,8,9,10,11,12,14,16,18,24\}.
\]
The chart's reverse clocks lie among these sites. The index differences are at most 34 and avoid 23, 29, and 31; the gaps to \(4/5\) have numerators over 60 equal, up to sign, to \(98,88,78,68,63,48,38,33,28,18,13,8,3,2,7,12,22,32,42,72\). These are all units in \(\mathbb Z[1/20!]\). The forward grade-nine chart pins the old zeroth moment, so the pure clock-one row merges into the old output row. The count is \(27+34+20-1=80\).

The literal tableaux for orders 11, 12, and 14 pass all rooted conditions by exact integer replay. The order-20 tableau has the symbolic all-tree proof and a sample replay. At all four orders the next bush has defect \(-1\).
