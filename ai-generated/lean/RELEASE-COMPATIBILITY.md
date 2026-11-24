# Checked Lean and Mathlib releases

The [full compatibility report](../release-compatibility-eb274e3/README.md) covers the 280-module proof tree at `eb274e3` with the portability patch applied. It passed clean builds on x86-64 Linux with these matching Lean and Mathlib releases: v4.34.1, v4.35.0, v4.36.0, and the current v4.37.0-rc1. Each run built every proof module, issued 428 axiom queries, and ran 30 named kernel replays.

The 36 checked proof edits are applied to the sources in this commit. The default Lean and Mathlib pins remain v4.36.0. This report does not certify the later proof modules added after `eb274e3`; its fingerprints and reproduction commands refer to that exact earlier tree. Historical release candidates and mismatched Lean/Mathlib pairs are outside the matrix.
