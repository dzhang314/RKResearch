# A universal fifth-diagonal pivot in live alpha-one beta-zero DIRK11/13

**Result.** In any characteristic-zero field, a normalized
no-late invisible-six DIRK11/13 candidate with live reciprocal
multiplier and \((\alpha,\beta,\gamma)=(1,0,5)\) must have
\(d_B=0\) and \(D_B\ne0\), where \(D\) is the matched quartic
column and \(B\) is the fifth regular reverse row. This includes
alternate old fits, finite old contacts, and the previously
treated direct noncontact \(F_n\) chart. It does not itself
exclude the remaining zero-diagonal candidates.

## Literal pivot without an old-profile ratio

Use the actual reverse prefix \(T,v,u,w,z,V,B,x\), with the
first post-\(B\) ghost \(x\), and the notation of the
[earlier fifth-pivot proof](../dirk11-thirteen-invisible-six-alpha-one-live-fn-beta-zero-fifth-pivot/README.md).
In particular \(P=Ym\), \(P_0=YR\), \(R=(Y-v)(Y-u)(Y-w)\),
\(K_*=(V-z)(G_V/b_V-P(V))/P_0(V)\),
\(Q_4=(Y-z)P+K_*P_0\), and \(D=(Y-z)G-W(Q_4)\).

Section 1 of that proof requires only the live reciprocal and
the literal prefix, **not** the direct \(F_n\) ratio. The
weighted quartic and once-marked \(G\) give
\(\mathcal C D\in Z_6\) for \(\mathcal C=YN-NY-N^2\);
injective evaluation through \(V\) and triangularity give
\(\mathcal C D=0\). Its literal value at \(B\) is
\(-d_B^2 D_B\). Supposing \(D_B=0\) makes \(D,ND\) vanish
through \(B\), while \(D_x=(x-z)G_x\ne0\) gives \(d_x=0\)
and \((ND)_x=0\).
The genuine primitive fit \(ND=G L-W(IQ_4)\) has \(\deg L\le2\)
and roots \(z,x\). If \(L=0\), the five ordinary reads and
polynomial origin force \(IQ_4=0\), contrary to the live
old \(P\) values. Otherwise \(L=\lambda(Y-z)(Y-x)\),
\(\lambda\ne0\), and the same five reads and origin force
\(IQ_4=\lambda(Y-x)Q_4\) identically.
Origin valuation now forces \(x=0\); coefficient comparison
gives \(Q_4=aY^j\), \(a\ne0\), \(1\le j\le4\).
In particular \(z\ne0\), since the ghost clocks are distinct.

## Two possible monomial shapes

The earlier genuine old identity is
\[
 IP=\ell_1(Y-z)P+\delta P_0 ,
 \qquad \ell_1\ne0 .
\]
If \(m\) is monomial, the old quotient \(IP/P\) is a nonzero
multiple of \(Y\), so \(\ell(z)=0\) forces \(z=0\), excluded.
If \(\deg m\le1\), degree comparison gives \(\delta=0\);
also for quadratic \(m\), \(\delta=0\) would give
\(IP=\ell P\), forcing a monomial by origin valuation and
the primitive coefficients. Thus normalize the actual
\(m=Y^2+rY+s\), with \(\delta\ne0\).
The coefficient of \(Y\) in the old identity forces \(s\ne0\)
because \(\delta R(0)\ne0\).

* **\(j\ge2\).** The coefficient of \(Y\) in
  \((Y-z)P+K_*P_0=aY^j\) forces
  \(K_*=zs/R(0)\ne0\). Substitute in the old identity:
  \[
     IP=(\ell_1-\delta/K_*)(Y-z)P+(\delta a/K_*)Y^j.
  \]
  Its coefficient of \(Y\) forces
  \(\ell_1-\delta/K_*=0\), since \(zs\ne0\).
  This makes \(IP\) a monomial, hence \(P\) monomial, impossible.
* **\(j=1\).** The quartic leader of the matched column gives
  \(K_*=-1\). Now \(P_0=(Y-z)P-aY\) and the old identity gives
  \(IP=(\ell_1+\delta)(Y-z)P-\delta aY\).
  Its three positive leaders give
  \(\ell_1+\delta=1/4\), \(4r=3(r-z)\),
  and \(2s=s-rz\), so \(r=-3z, s=3z^2\).
  Thus \(R=(Y-z)m-a=Y^3-4zY^2+6z^2Y+c_0\).
  At all five ordinary sites \(D=0\) and
  \(G/b=YJ_4/U_r\), hence \((Y-z)J_4-aU_r=42T_5\)
  as a polynomial, using the actual monic ordinary pencil
  \(T_5=(J_5+\mu J_4)/132\).
  The exact same coefficient and Bézout calculation as in
  [the checked contact certificate](../dirk11-thirteen-invisible-six-alpha-one-live-fn-beta-zero-fifth-pivot/README.md#2-excluding-the-old-monomial-including-the-ungauged-contact)
  now applies, without distinguishing any old ratio. It forces
  \(\mu=(11/7)(1-2z)\) and two coprime polynomials of degrees
  4 and 5 at \(z\), a contradiction.

Therefore \(D_B\ne0\) and the domain implication from
\(-d_B^2D_B=0\) gives \(d_B=0\). The argument makes no
ordering, splitting-extension, old-profile leader, or
ghost-to-ordinary clock separation assumption. It reuses the
exact standalone and Lean Bézout certificate of the earlier
packet. The unrestricted real DIRK11 stage interval stays **13–14**.

The accompanying Lean module checks the nonzero positive-monomial
coefficient pivot, the exact cubic/quadratic coefficient comparison,
and the monic scale used for the lost-ratio quadratic in the
finite-contact follow-up. These are local scalar receipts checked
with Lean 4.36.0 and the standard axiom set.
