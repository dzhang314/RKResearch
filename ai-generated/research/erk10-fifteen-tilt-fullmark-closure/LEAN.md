# Scalar Lean and exact proof scope

The new portable scalar source is

    lean --threads=1 ai-generated/lean/RKCert/ReviewedNative/ERK10TiltJacobiFour.lean

It states the four integer-cleared moments of the degree-four
Jacobi polynomial and the finite homogeneous no-root
certificate modulo 11 (including infinity). The exact Python
replay of both is green. Lean releases were started
independently; a completed compiler log is recorded in a
separate receipt only once a run finishes.

For the raw directional projection, the pure word erasure uses
the existing prefix lemma ERK10TiltSilentErasure.eraseSilentAxes,
which is verified in the separate native follow-up. The
endpoint-blind corrected cubic reuses the already checked core
scalar theorem ERK10ZeroHighSevenScalars.threeEndpointGhostSquare.
The actual old interface, gray/model-blind support cases and
new exact moment inference are mathematical, not a single
native order theorem.
