# Exact verification receipt

The frozen core files were run unchanged with their declared sibling proof dependencies. Results:

* True symbolic mass-free coefficient audit: both \(s\) coefficients agree with direct polynomial expansions of \(\mathcal P(E_6)\), \(\mathcal P(XE_6)\); both actual terminal factors hold as exact polynomial identities.
* First gap resultant: \((89,300)\), legal factor powers \(\gamma^{16}\alpha_N^4\), retained \((77,260)\).
* Outer nominal cap 6499, integral coefficient-bound bit length 20560. Serial recycled exact split CRT used 343 primes and independently compared the entire first image and the entire image at 65537 to standard FLINT resultant images. The source-level exact run took about 186 seconds for the outer CRT alone.
* Raw diagonal 5635, guards \(\gamma^{770}\beta_N^{171}\), retained full monic degree 4181. Exact simultaneous nominal \(Y\)-leading norm gcd degree zero.
* At \((1129,t=203)\) the complete factor degrees are \(3,4,5,6,7,8,12,19,25,31,36,50,55,154,169,228,272,465,503,518,1611\), all multiplicity one. The seven inconsistent-in-\(s\) degrees are \(3,7,8,36,50,503,1611\). All other components pass the independent terminal and mass-free signed unit tests.
* In isolation with only the pinned Python packages and declared dependency directories, the portable entry imports and independently replays the symbolic coefficient audit. The expensive outer wasn't recomputed a second time for that import check. The portable entry performs the full exact replay when run as the main script. No native Lean check is claimed here.

The memory-killed attempt with a worker that was not recycled is not part of this certificate; the complete recycled exact run exited successfully.
