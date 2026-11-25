# One divisibility and one square test for any ground field

The normalized genuine quartic profile of QUARTIC-GLOBAL has an especially direct ground-field count. Put

    S = 3478762188949 = 53 · 64279 · 1021127,
    Q = 11712161789730284342016914945454990277045396849422221142542420594260361,
    D = 8483038916109478940533923281725988412336325038253298332050421596975837.

For a field K of prime characteristic p>13:

* If p divides S, there is exactly one normalized ordered (t,u,b,R,κ) in K, already defined over the prime field. It is self-reflected: **t+u=1 and b=3**.
* If p divides Q, there are exactly two normalized ordered solutions in K when D is a square in K, and none otherwise. The quadratic component involution exchanges them by **(t,u,b) ↦ (1−u,1−t,6−b)**.
* Otherwise there are no scalar solutions.

The integers S and Q are coprime and D is coprime to Q. Thus a contemplated characteristic does not require a factorization. D is the CRT combination of the discriminants of the two original quadratic component polynomials. In odd characteristic a monic separable quadratic has two roots in K exactly when its discriminant is a square. The displayed conjugation identities are direct evaluations in the two universal quadratic rings. They explain why the only extension ever required is quadratic and identify the complementary symmetry of the two solutions. This counts the normalized scalar profiles, not Runge–Kutta tableaux. Replay the parent certificate and then run `python3 quartic_symmetry.py .`.
