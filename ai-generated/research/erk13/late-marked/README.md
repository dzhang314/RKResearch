# Late marked ERK(13): excluding width 19

This package gives a paper proof over every characteristic-zero field for a strict explicit 19-row tableau satisfying the reviewed rooted-tree `HasOrder 13` conditions, with first reflected seed zero and the literal last-stage coordinate absent from the actual grade-seven tree space. It does not claim an unrestricted stage bound, an early-terminal result, or an end-to-end Lean proof.

## Proof order

1. [Paid marked staircase](PAID-STAIRCASE.md): measure the original marked ranks and advances; force the paid degree-seven first escape; earn true grade-seven equality and restrict to radius two or three.
2. [Late square](LATE-SQUARE.md): exclude radius three by a second square shift; for radius two, exclude the zero-leading case by both physical first ports and obtain exactly 18 marked classes in the nonzero-leading case.
3. [Final three classes](LATE-FINAL-THREE.md): fold on the 18 marked classes using original weights and the true row difference; exclude the residual by the three positive-index paid transpose rows. This treats both pure and nonpure squares, whether the terminal enters at grade nine, grade ten, or is still absent at grade ten.
4. [Exhaustion index](EXHAUSTION.md): all chart premises, branches, and links. [Prerequisites](PREREQUISITES.md) identifies the verified conditional leaves, the proof-only joins, and the draft boundaries.

The [independent pure modular certificate](PURE-CLEAN-RANK.md) is a backup for the pure leading-mismatch case with true grade-nine or grade-ten terminal entry. It is not needed by the main proof. Its exact checker uses only Python's standard library:
```sh
python3 certificates/pure_late_clean_rank.py
```

The links point to the checked Lean prerequisites in the repository. The new marked-staircase module has also been checked and replayed; that does not yet check the entire late proof.
