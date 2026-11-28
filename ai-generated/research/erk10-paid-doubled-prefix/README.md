# Factorial-localized gate for the canonical doubled opening in ERK10

Work in \(S=\mathbb Z[1/10!]=\mathbb Z[1/210]\). The canonical
doubled opening used in the
[deterministic mirror family](../erk10-sixteen-rational-mirror-family/README.md)
has only one possible regular normalized horizon for a paid tableau of this
pure-high shape:
\[
  (\theta,v)=(5/2,5/3),\qquad s=\xi/\theta\in S^\times .
\]
The arithmetic theorem here does not require a mirrored or aligned late
geometry. It is conditional on the following actual opening, support, and
high-row identities. It is not a lower bound on unrestricted ERK10 or on
arbitrary factorial-localized tableaux.

## Exact assumptions

* The actual eight-row opening has clocks
  \(s(0,e,1,2,2,v,v,\theta)\), where \(s,\theta\ne0\),
  \(v\notin\{0,1,2\}\), \(\theta\notin\{1,2,v\}\), and
  \(N=12\theta^2-45\theta+40\), \(v=\theta N/[15(\theta-2)^2]\).
  Its actual protected \(a_{6,3}\) is \(s v^2(v-1)/3\), with indices
  starting at one. All actual coefficients and physical clocks are in \(S\).
* The row at physical horizon \(\xi=s\theta\) is stage-wise pure through
  the order-five tests: its incoming row gives scalar degree-four
  integration at \(\xi\), with zero coefficient at the starter \(se\).
  Repeated clocks are aggregated. Thus its only four possible integration
  sites are \(0,s,2s,sv\). The incoming row is explicit, so that row
  cannot itself contribute at site \(\xi\).
* The second-stage starter is the only row where
  \(\boldsymbol d=A\boldsymbol c-\boldsymbol c^2/2\) may be nonzero.
  Its defect is \(-c_2^2/2\). The high rows, **including** the
  opening endpoint at \(\xi\), satisfy \(A\boldsymbol d=0\).
  The final output \(\boldsymbol b\) is supported only on the origin
  and those high rows, and \(\boldsymbol b^\top\boldsymbol c=1/2\).

These properties hold for the named canonical constructions; the arithmetic
argument below uses them as hypotheses, not as asserted conditions for
general order-ten methods.

## The scale cannot hide an unpaid normalized pole

Fix \(p>7\) and reduce the actual paid coefficient matrix modulo \(p\).
If \(s=sv=0\) after reduction, the only potentially nonzero clock before
the high rows is the starter. Its nonzero clock would imply nonzero
\(\boldsymbol d\) at that row, so \(A\boldsymbol d=0\) forces every
high row to receive zero from it. The second-moment row identities
\(c_i^2=2(A\boldsymbol c)_i\) and strict triangularity then force
all high clocks to vanish by chronological induction. This contradicts
\(\boldsymbol b^\top\boldsymbol c=1/2\).
The induction is kernel-checked independently of the valuation calculation
in `ERK10PaidPrefixCleanClock.no_suffix_nonzero_of_only_impure`.

Consequently at least one of \(s,sv\) remains nonzero modulo each unpaid
prime. This eliminates two possibilities:

* If \(\theta\) has a pole at \(p\) of order \(k>0\), \(v\) has
  a pole of order \(k\), since its leading ratio is \(4\theta/5\).
  The protected tap entails \(v_p(s)\ge3k\). Thus both \(s\) and \(sv\)
  would vanish, a contradiction.
* If \(v_p(\theta-2)=k>0\), then \(N(2)=-2\) and
  \(v_p(v)=-2k\). The protected tap entails \(v_p(s)\ge6k\),
  again forcing both physical clocks to vanish.

Therefore \(\theta\in S\), \(\theta-2\in S^\times\), and \(v\in S\).
Since at least one of \(s,sv\) survives at each unpaid prime,
\(s\in S^\times\).

## Old endpoint weights and complete horizon census

Divide the old endpoint row by \(s\), now a unit. Its four scalar
degree-four quadrature sites \(0,1,2,v\) have paid aggregate coefficients.
In particular the last aggregate must be
\[
  \frac{\int_0^\theta X(X-1)(X-2)\,dX}{v(v-1)(v-2)}
   =\frac{\theta^2(\theta-2)^2}{4v(v-1)(v-2)} .
\]
If \(p\mid v-1\) or \(p\mid v-2\), then \(\theta\) is a \(p\)-unit
(because \(v=\theta N/[15(\theta-2)^2]\)), so the displayed coefficient
has a pole. Similarly if \(p\mid N\), then \(\theta\) is a \(p\)-unit
because \(N(0)=40\), but \(v\) vanishes and the same pole occurs. Thus
\(v-1,v-2,N\in S^\times\).

Apply the complete census for \(u+(1-u)=1\) with \(u=v-1\). The 63
positive primitive triples up to unsigned reciprocal symmetry and 375
signed first coordinates are covered by the
[published S-unit computation](https://arxiv.org/abs/1605.06079) and
[authors' Table 1](https://bmatschke.github.io/solving-classical-diophantine-equations/#data-for-s-unit-equations);
the first six prime sets are attributed there to de Weger. The exact
replay independently enumerates 63 such triples. Completeness uses the
published count, never the enumeration cutoff alone.

For each coordinate \(v\), the replay finds *all* rational roots of
\(\theta N-15v(\theta-2)^2\), using exact rational polynomial factoring.
After deleting degenerate roots this produces exactly \((5/2,5/3)\)
and \((3,13/5)\). The latter has \(N=13\) and an unpaid old aggregate
coefficient \(375/416\). At the remaining candidate the normalized
old scalar aggregates are
\((115/384,625/384,625/384,-135/128)\).
In particular the \(\theta=5/4\) aligned width-16 witness cannot be made
factorial-only by multiplying its alias clock by 17 or any other
rescaling within this chart, regardless of the late row coefficients.

## Replay and native scope

From `ai-generated`, with Python 3 and SymPy:

    python research/erk10-paid-doubled-prefix/horizons.py
    sha256sum -c research/erk10-paid-doubled-prefix/sha256.txt

With the project's Mathlib-enabled Lean environment (tested with 4.36.0):

    cd lean
    lake build +RKCert.ReviewedNative.ERK10PaidPrefixCleanClock

The named Lean theorem checks the strict-triangular suffix induction
over any field, with only standard axioms. The rational valuations and
externally complete S-unit enumeration are a mathematical/exact-arithmetic
certificate, not part of that native endpoint.
