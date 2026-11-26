# A cross-order floor for the single stage-order-two defect class

The argument in [the eleven-row proof](SINGLE-SECOND-ROW-DEFECT-SIX-LOWER-BOUND.md) has a structural conclusion stronger than a lone ten-row exclusion. In an actual explicit tableau, suppose \(\mathbf q=A\mathbf c-\mathbf c^{\odot2}/2\) has one nonzero component and
\[
      \dim F_3=1,\quad \dim F_4=2,\quad \dim F_5=3,\quad \dim F_6=4 .
\]
Over a field with \(5!\) invertible, it then has at most four distinct physical clocks. Apart from the unique offending row, they belong to \(\{0,aN,aT\}\), where \(a\) is the first nonzero clock before normalization. If there is no fifth row after merging repeated histories, this statement follows already from the first four rows. Otherwise the earlier classification forces a genuinely new fifth profile to be a repeated clock \(T=2N\), and the grade-six identity then prevents any subsequent new clock outside \(\{0,N,T\}\), apart from row 2. No dense or ordinary model assumption entered that row algebra once the displayed pure dimensions were supplied.

For clarity, merging is harmless even without a decoder. Physically equal incoming rows have the same rooted derivative coordinates at all sizes. Redirect a later coefficient on the removed copy to its earlier identical coordinate. The data on retained rows are unchanged, and every vector in the old rooted span has equal coordinates at the two copies. Thus both pure rank and clock labels are unchanged. Also every stage before the first nonzero clock has the exact origin profile at all sizes, by the strict recurrence, and those origin histories can be merged. Repeat the finite reductions when the stated first-four or fifth-row alternative produces a duplicate.

Two consequences follow.

1. **Dense through size \(m\ge6\).** Size six pays six independent model powers, so fewer than six clock values are impossible. The chronological no-plateau lemma then gives \(\dim F_6\ge5\), and at each subsequent paid size the dimension increases. Therefore
\[
              s\ge m+\dim F_m\ge 2m-1.
\]
The bound is sharp at \(m=6\). For larger sizes no matching construction is asserted.
2. **Ordinary order \(r\ge6\).** The output annihilates the sole nonzero coordinate of \(\mathbf q\), so the offending row has weight zero. If \(\dim F_6=4\), the structural conclusion would leave ordinary scalar degree-five quadrature on clocks contained in \(\{0,u,v\}\), now in the original unscaled coordinate. Their monic cubic hull would be orthogonal to \(1,X,X^2\). The ordinary degree-two moment Gram determinant is \(1/2160\), a paid unit, so this monic cubic is unique. It is
\[
          X^3-\tfrac32X^2+\tfrac35X-\tfrac1{20}.
\]
Its constant is nonzero, unlike the required hull. If there are fewer effective clocks, pad the proposed hull by any additional factors to make it monic cubic with constant zero; the same contradiction holds. Thus \(\dim F_6\ge5\) under ordinary order as well, and \(\dim F_k\ge k-1\) through paid sizes \(6\le k\le r\). The stronger forward preparation charge applies to any dense continuation of such an unchanged ordinary prefix.

The assertions are over nonzero paid fields and pass to arbitrary nonzero commutative paid rings by residue specialization when every entry of \(\mathbf q\) outside the same one physical row vanishes. Dense derivative profiles need only the product of the factorials of the branches below the root, not invertibility of the root's own size. In particular the derivative profile denoted \((|t|/t!)X^{|t|-1}\) in the earlier notes means the reduced coefficient
\[
        \frac{X^{|t|-1}}{\prod_{u\text{ child at the root}} u!};
\]
the factorials up to \(m-1\) suffice through size \(m\). Each residue field still has nonzero \(\mathbf q\) because its first nonzero explicit clock has nonzero defect. This automatic survival is specific to the single-defect ERK setting plus the paid order or decoder of the hypothesis.
