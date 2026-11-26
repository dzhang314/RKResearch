# Checked propagation of native forest-scaled tree columns

Over a commutative semiring, take an actual stage matrix A on layers with
fibres Fin (h+1), and assigned labels x. LayerMonomialStep is an explicit
row-action premise: any actual input column whose receiving and parent
slices are both the degree-d monomial in those labels has a cleared
(d+1) response of the degree-(d+1) monomial at the receiving row, for
d<h. The labels are not assumed to be tableau clocks.

The native induction keeps all layers generalized. Under that premise,
the forest-factor-scaled raw column of every reviewed tree of size at
most h+1 equals the degree-(size−1) monomial at layer h. The branch is
then paid both on the receiving and parent layers. No factorial inverse
is used. This is conditional propagation, not a proof that a particular
matrix satisfies the row premise, a matrix realization, an output order
condition, or a stage-count certificate.

The [measured body](../../RKCert/ReviewedNative/LayerMonomialPropagation.lean)
exited zero with an empty compiler log and its single parent family.
The [standalone typed audit](../../AuditReviewedNativeLayerMonomialPropagation.lean)
spells out the actual row premise and native forest-scaled column
explicitly. It exited zero and requested no output object. Its
[exact transcript](typed-audit-output.txt) has one named report and
only propext, Classical.choice and Quot.sound. The [result ledger](result.json)
records source, provider, object and actual receipt hashes.

Integration base checked: 2856425368ecb372c3ce18faba84ee7a9413a14c.
This is an additive sources-only publication packet with no compiled
artifacts, package configuration changes, or cold-build claim.
