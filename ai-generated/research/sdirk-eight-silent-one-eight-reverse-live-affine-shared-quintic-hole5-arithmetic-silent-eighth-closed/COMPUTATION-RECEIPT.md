# Exact verification receipt

The full bounded source computation used the frozen core before passing to the independent exceptional fiber.

* Symbolic audit: all four actual-cofactor determinants agree with independent extraction of both \(s\)-basis coefficients of \(\Lambda(D)\) and \(\mathcal P(D)\), with the true terminal factors and \(F\) identity.
* The \(u\)-resultant has bidegrees \((98,276)\) before and \((71,186)\) after the exact \(\gamma^{12}\alpha_N^3H_N(x)^6\) division.
* Exact outer CRT: nominal cap 5079, 270 split primes, checked coefficient-bound bit length 16152; the whole first and 65537 images independently agree with standard FLINT. Resource bounded to one recycled worker. The outer CRT itself took about 109 seconds.
* Raw degree 4323; exact guards \(\gamma^{702}\beta_N^{117}\); full retained monic degree 3153.
* At \((1129,t=203)\) the 22 factors off the leading-loss cubic, with multiplicities, are \((1,1),(1,1),(1,1),(1,4),(3,1),(4,1),(4,4),(6,4),(8,1),(8,4),(8,4),(10,1),(16,1),(22,1),(29,1),(36,1),(80,1),(95,1),(112,1),(219,1),(965,1),(1440,1)\). All pass. Degrees 29, 112, 219, 1440 are inconsistent already in \(s\); the others passed the signed/terminal check.
* The remaining cubic factor \(X^3+24X^2+620X+79\) has multiplicity one. Independently, the complete exact common \(Y\)-leading gcd is \(\gamma^{12}L\), with the monic \(L\) in the proof. This proves \(L\) divides the characteristic-zero retained diagonal via the padded determinant. Its residue is exactly that single cubic. Full exact \(Y\)-coefficient specialization at \(L\) gives degrees 16 and 70 and complete gcd one on its cubic fiber. No degree-loss factor was omitted.
* The portable wrapper reconciles exactly these two complete verified checks. A clean dependency-only run independently replayed the symbolic audit and the whole specialized cubic check. It did not recompute the expensive outer a second time; the entry recomputes it when run as main. No new native Lean check is claimed.
