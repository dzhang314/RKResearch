# Native real midpoint DIRK12: physical grouped reverse assembly

These Lean modules construct the **literal 15 physical rows** of the
previously published real-algebraic tableau via the verified five-row head and
the actual chronological order
\[
  \text{origin},\ \text{four ghosts},\ \text{five openings},\
  1-u,\ 1-d,\ 1-v,\ 1-d,\ 1.
\]
The two occurrences of \(1-d\) at zero-based physical stages 11 and 13 are
distinct stages with equal signed nonzero weights, not a single effective
stage. The visible low primitive checks are against the entries of this
matrix; no reduced scalar-only method is used.

## Exact construction and native results

* **Seed and Groups.** The seed uses the exact three normalized reverse
  rows on physical stages 11, 12, 13, in ascending physical order.
  Their normalized primitive tests at positive degrees 1–3 and their
  paired image are field identities. For earlier targets, including the
  physical row at \(1-u\), first subtract the actually causal weighted
  entries from the five verified opening rows. The three distinct nonzero
  labels \((d,v,u)/d\) then solve the three required power reads by positive
  cardinals. The normalized group at \(d\) is split into the two actual
  taps by the unique signed pair-image equation, with no unsigned or
  positive-weight hypothesis.
* **Physical and Guards.** The installed \(\mathit A\) preserves every
  opening entry, inserts just these four later ordinary return rows,
  inherits the actual ghost column taps, and uses the preexisting literal
  terminal correction and origin row-sum completion. Its entire physical
  terminal column is zero. Every used physical nonzero weight, the group
  weights' deweighting factors, and the needed normalized clock pivots
  are guarded from the verified real boxes. In particular
  \(0.31<v/d<0.33\) is a strict directed rational bound.
* **Shape, Bary, and Masses.** The normalized moment ratios follow
  algebraically from the actual quadratic orientation and third group
  label. The three cardinal masses factor as a cofactor integral times a
  nine-site barycentric weight divided by the corresponding nonzero
  reflected label. The exact two-way cofactor identity gives the same
  normalization \(\rho\) at the first physical repeat and at the
  singleton. The independent \(u\) identity and normalized zero-diagonal
  primitive factor are available without reading any unknown table entry.
* **Profile.** The physically constructed \(\mathbf H\) is exactly the
  pushforward of the nine-site barycentric weights times \(\rho\), with
  the common \(d\)-amplitude placed only at physical stage 11. The literal
  weighted transpose satisfies
  \[
     \mathit A^{\mathsf T}\mathbf G
        =\frac d2\mathbf G+\mathbf H,
     \qquad
     G_{13}=d^3 b_{13}/6=-G_{11},
  \]
  and all other \(G_i\) vanish. The theorem concerns all 15 coordinates:
  the actual ghost taps cancel entrywise, and the origin follows from
  the actual row sums and the verified zero total. The profile exactly
  annihilates \(\mathbf c^m\) for \(0\le m\le7\), so the physical forward
  primitive defects at stages 11 and 13 agree in that range.
* **PhysicalLow.** For entering reflected powers 1, 2, and 3 the actual
  visible unscaled reverse defects are respectively \(0,\mathbf G,
  (3d/2)\mathbf G+\lambda\mathbf H\). A generic adapter promotes those
  visible identities to all coordinates when its stated actual ghost
  projection and paid scalar hypotheses are furnished. That adapter
  does not itself prove the ghost projection.

The degree-five reverse live check, transpose closure on \(\mathbf H\),
and complete native real rooted-tree theorem are not proved in this
package. The mathematical real-algebraic construction and order proof
remain in [the exact characteristic-zero construction](../dirk12-fifteen-midpoint-real-upper/README.md).
No new stage bound or fourth positive entering live moment is asserted.

## Build and audit

Build these modules in the existing native Lean project, with matched
Mathlib. One dependency order, with common prefix
**DIRK12MidpointReverse**, is Seed, Groups, Physical, Guards,
PhysicalLow, Shape, Bary, Masses, Profile, then Audit. The completed
check used Lean/Mathlib 4.36.0 with kernel-only proofs and standard
logical axioms; there is no completed cross-release Mathlib sweep in
this receipt.
