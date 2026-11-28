# Complete alpha-two quadratic-carrier exclusion

**Result.** Both \(\alpha=2\) counts of the normalized no-late
invisible-six DIRK11/13 census are impossible for a quadratic
forward carrier over a characteristic-zero field. Here
\((\alpha,\beta,\gamma)=(2,0,4)\) or \((2,1,3)\).
This is a scoped exclusion for the original literal normalized
rooted-order chart, not a larger numerical lower bound.
The unrestricted real stage interval remains **13–14**.

Use the actual shape and root-order inputs of the
[early profile census](../dirk11-thirteen-invisible-six-early-profile-census/README.md)
and the [alpha-two debit](../dirk11-thirteen-invisible-six-alpha-two-debit/README.md).
In particular the fourth regular reverse \(V\) has
\(d_V=0\) by the complete actual adjoint commutator row
vanishing; the two early ghost clocks \(z,w\) are distinct
and are the two roots of the actual quadratic \(w_0\).
No numerical ghost-clean disjointness is added.
The reciprocal multiplier is live because a quadratic
carrier cannot vanish at all three live old reverse samples.

## 1. Three paid tests at the actual zero diagonal

Use \(P_0=YR\), \(V=1-a,\ B=1-b\) as in the prior papers,
and normalize the common clean heads so
\(k(y)=G_y/b_y=yJ_4(y)/U_{\rm rev}(y)\) at ordinary nonendpoints;
here \(U_{\rm rev}(Y)=U(1-Y)\).
The old degrees \(\deg U_{\rm rev}\le2\) and live samples give
\[
 U_{\rm rev}=(J_4/m)\bmod R,\quad
 w_0=(IP_0/(Ym))\bmod R,\quad
 Q_0=(I(YP_0)/(Ym))\bmod R.
\]
A common scale of these three fits is harmless, since it
changes \(k\) by its inverse.

The literal quartic at \(V\) uses no dot product with
unweighted ghosts, and because \(d_V=0\), its only possibly
nonzero weighted donor would already have input zero.
Thus \(IP_0(V)=w_0(V)k(V)\).
Let \(L_0=IP_0/Y,\ L_1=I(YP_0)/Y\) as polynomials. Form
\[
 D_4=(L_0 U_{\rm rev}-w_0J_4)/R,\quad
 D_5=(L_1 U_{\rm rev}-Q_0J_4)/R .
\]
Both are exact polynomial quotients; their numerators vanish
at the three old roots by construction. Since \(R(V)\ne0\),
the quartic gate is precisely \(D_4(V)=0\).

For the forward read, define \(F_b=I[X(X-b)U]\),
\(H=XJ_4(X)\), \(r_b=F_b(b)/H(b)\).
The true grade-six column \(A[C(C-b)\phi]\) vanishes at the
first clean \(b\) and at \(a\), the latter because its only
possible nonzero clean donor is itself and \(d_V=0\).
The \(F_6\) shape forces \(F_b(a)-r_b H(a)=0\).
Compute its necessary polynomial numerator, dividing
the live \(a b(a-b)\) before evaluation. The program does
this by working with \(F_b(X)/X\) and the difference
against \(J_4\), which has \(X=b\) as an exact polynomial root.
No independence of this condition and the reverse quartic
is asserted.

The actual quintic \(YP_0\) has primitive error
\(GQ+\theta H_{\rm bary}\), with
\(Q=Q_0-\theta U_{\rm rev}+\mu R\) by the old three samples.
At \(V\), the \(H\) term cancels the \(U_{\rm rev}\) term.
Then the literal \(d_V=0\) gives
\(\mu=D_5(V)/J_4(V)\). At the two first ghosts the weighted
inputs and output weight both vanish, hence
\(Q_0+\mu R=\theta U_{\rm rev}\) at those two genuine
distinct roots of \(w_0\). The two linear remainders modulo
\(w_0\) have zero determinant. Use the polynomial
degree-two/three remainder columns after multiplying by
one/two powers of its live leader. Clearing only this
leader and \(J_4(V)\) gives the actual quintic gate used by
the source. This also preserves equal numerical residues
of the two ghosts; the actual distinctness is used *before*
forming the coefficient determinant.

## 2. Exhaustive regular and singular old profiles

The [monomial](../dirk11-thirteen-invisible-six-quadratic-monomial-early/README.md)
and [mixed contacts](../dirk11-thirteen-invisible-six-quadratic-contact-early/README.md)
are already excluded. Thus \(m=Y^2+rY+s\) up to scale,
\(rs\ne0,\ c_2s\ne c_0\). The early profile census gives the
literal quadratic
\[
 D=c_0r^2-(2s^2+c_1s)r+3c_2s^2-3c_0s=0
\]
and the exact affine remainder \(A_1(s)r+A_0(s)=0\).
Its projected factors leave some \(F_1,F_2,F_n\) root.
If \(A_1\ne0\), \(F_1\) forces old affine slope \(-1\),
forbidden by the second ghost debit. \(F_2\) forces \(m\mid R\),
forbidden by the individually live old \(m\) samples.
Thus \(F_n=0\) and
\[
 r_n=\frac{6c_2s}{c_1+6s}.
\]
The two denominators \(c_2\) and \(c_1+6s\) are live here.
The proof of this profile formula is verified by the early
census. In what follows the **regular arithmetic** actually
only uses the explicit \(r_n\) formula and those guards;
it makes no further \(A_1\) assumption.

When \(A_1=0\), the affine equation also gives \(A_0=0\).
One must not insert the \(r_n\) formula all across this locus.
Instead split on which \(F_i\) vanishes, retaining overlaps.
On \(F_1\) a known root of \(D\) is
\(r_1=15(c_2s-c_0)/(16s)\), impossible from slope \(-1\) if
it is the actual \(r\). On \(F_2\) a known root is
\(r_2=(c_2s-c_0)/s\), impossible by the old \(m\) contact.
On \(F_n\), with \(c_1+6s\ne0\), the known root is \(r_n\)
as above and \(c_2\ne0\) by \(F_n\).
It is excluded by the regular arithmetic even when \(A_1=0\).
Thus in each respective chart the actual \(r\) must be the
other root of \(D\):
\[
 r=\frac{2s^2+c_1s}{c_0}-r_i .
\]
The three known-root identities are verified exactly by the
source. A repeated known root cannot create another actual
branch. The three finite algebras also enforce the actual
necessary equation \(A_1=0\), with coefficients checked
directly against the previous exact remainder.

Finally on \(F_n,\ c_1+6s=0\) one has \(c_2=0\).
The exact old \(c_2\)-projection then leaves only \(J_4(V)\)
(forbidden) and one degree-twelve ordinary factor. Recover
\(B\) directly from \(c_2=0\), a linear equation in \(B\)
with live leading coefficient \(132J_4(V)\).
Thus \(s=-c_1/6\) and \(D\) reduces to the monic quadratic
\(r^2+(4s^2/c_0)r-3s=0\). In the full rank-24 algebra,
including both possible \(r\)'s and without using a pivot,
the d=0 reverse quartic numerator is a unit modulo 103.
This handles the finite denominator loss independently.

## 3. Exact projections and guarded rank saturation

In each of the four nondegenerate charts, over \(\mathbb Q[V]\)
take the monic finite-free clock/profile tower of rank \(4\cdot3\).
Scale clocks by \(L=132J_4(V)\): the other ordinary
\(\widehat B=L B\) satisfies the rescaled monic quartic
and shares the actual old hull coefficients in scaled
units. For the branch polynomial in \(s\) with leader
\(L_3\), adjoin \(\sigma=L_3 L^2s\) using its monic cubic.
The source builds numerator \(m,w_0,Q_0,U_{\rm rev}\)
with common nonzero scalar gauges. The only removed
nonconstant *base coefficient* content throughout the
exact determinants and norms has support \(J_4(V)\).
The checker verifies this for every logged division.

A putative actual solution maps the monic tower to its
coefficient field by evaluating the actual clocks/profile.
If an equation vanishes at it, multiplication by that
equation has zero specialized norm: evaluation is a
nonzero functional annihilating the multiplication map.
All arithmetic on these first projected norms is exactly
over \(\mathbb Q\). The exact joint gcd data are:

| Profile tower | Joint degree | Distinct irreducible support |
|---|---:|---|
| \(r=r_n\) | 324 | \(J_4\), two degree-12 factors, degree 60 |
| \(F_1\) alternate + \(A_1=0\) | 196 | \(J_4\), endpoint quartic, degree 36 |
| \(F_2\) alternate + \(A_1=0\) | 196 | \(J_4\), endpoint quartic, degree 36 |
| \(F_n\) alternate + \(A_1=0\) | 504 | \(J_4\), endpoint quartic, degree 12, degree 48 |

In the first row the three exact norm degrees
(reverse, forward, quintic) are 516, 456, 2328.
All exponents and the full coefficient data are replayed.
The separate endpoint quartic is the factor of
\(J_5(V)+J_4(V)\) after dividing \(2V\);
it would imply \(\lambda=1\) and \(T_5(0)=0\).
Neither quartic case can be actual.

For each residual irreducible factor \(f(V)\) work over the
**exact field** \(K_f=\mathbb Q[V]/f\).
In the rank-12 tower above it, the chosen old guard
\(g\) has exact zero norm, checked by exact division of
its projected polynomial by \(f\). Thus its multiplication
rank is at most 11; for the lower quartic clock guard \(c_2\)
the upper rank is \(3\cdot3=9\).
But the replay computes at 103 a nonzero residue minor
showing the images of the necessary equations multiplied by
\(g\) already have dimension at least this exact upper rank.
Their sum is contained in the image of \(g\), so equals
it over \(K_f\). An actual evaluation killing the equations
would kill all of that image and hence \(g=g\cdot1\).
This contradicts the listed **actual** nonzero guard, even
though it vanishes at a *different* formal component.

| Tower and degree of \(f\) | Guard | Exact cap | Residue extension degree |
|---|---|---:|---:|
| \(r_n\), 60 | old \(m\)-norm | 11 | 1 |
| \(r_n\), 12 | scaled \(c_1+6s\) | 11 | 12 |
| \(r_n\), 12 | lower \(c_2\) | 9 | 4 |
| \(F_1\) alternate, 36 | old \(m\)-norm | 11 | 1 |
| \(F_2\) alternate, 36 | old \(m\)-norm | 11 | 36 |
| \(F_n\) alternate, 48 | old \(m\)-norm | 11 | 2 |
| \(F_n\) alternate, 12 | lower \(c_2\) | 9 | 4 |

Ranks in the raw residue check are measured over
\(\mathbb F_{103}\) as the listed cap times the residue
extension degree. Only the lower bound on the exact
rank is inferred from the residue nonzero minor.
Nothing reduces or assumes integral a tableau, its
weights, or an actual ghost clock.

## 4. Reproduction and native scope

Use Python 3 with python-flint 0.9.0 and SymPy. In this directory
**python3 check-old-pivot.py** checks the literal A1 coefficient
list and the three exact D-roots, and **python3 degenerate.py**
checks the omitted denominator contact. The latter accepts
**--research PATH** for sibling arithmetic sources.

**bash run-guard-ranks.sh** uses the small frozen exact
joint/guard inputs. The following regenerates all inputs:

    d=$(mktemp -d)
    for c in regular F1 F2 Fn; do
        mkdir "$d/$c"
        if [ "$c" = regular ]; then
            python3 regular.py --p 0 --write "$d/$c"
            python3 regular.py --p 0 --trace-guards --write "$d/$c"
        else
            python3 singular.py --branch "$c" --p 0 --write "$d/$c"
            python3 singular.py --branch "$c" --p 0 --trace-guards --write "$d/$c"
        fi
        python3 check-joint.py "$c" "$d/$c" --out "$d/$c/joint.txt"
        for f in proof-inputs/"$c"/*.txt; do
            cmp "$f" "$d/$c/$(basename "$f")"
        done
    done
    bash run-guard-ranks.sh "$d"

The shared native **DIRKOrderElevenInvisibleSixAlphaTwoDebit**
module checks the undivided coefficient remainders and pair
determinant, the distinct-root Vieta step, and the pure
Jacobi gates. The rooted-space transfer and complete finite
elimination are exact source proofs, not a new end-to-end
Lean order theorem.
