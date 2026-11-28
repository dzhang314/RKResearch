"""Exact width and paid-contact replay for the q10, n11 Runge–Kutta chart."""
import sympy as s
import flint

T4=[1,-32,216,-480,330]
U44=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],
     [216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],
     [330,-9240,55440,-110880,69300]]

def data():
    a,d,X=s.symbols('a d X')
    R4=42*X**4-84*X**3+56*X**2-14*X+1
    R5=132*X**5-330*X**4+300*X**3-120*X**2+20*X-1
    assert s.Poly(R4,X).gcd(s.Poly(R5,X)).degree()==0
    R=s.expand(R5.subs(X,a)*R4-R4.subs(X,a)*R5)
    h=a/2
    Phi=s.Poly(s.exquo(R.subs(X,d),d-a,d)/(-2),a,d,domain=s.ZZ)
    L=s.Poly(s.cancel(2*(4*(a-d)*R.subs(X,h)+(h-a)*(h-d)*s.diff(R,X).subs(X,a))/a),
             a,d,domain=s.ZZ)
    Q=s.Poly(L.as_expr().subs({a:1-d,d:1-a},simultaneous=True),a,d,domain=s.ZZ)
    P=lambda z:s.Poly(z,d,domain=s.ZZ)
    assert [g.degree_list() for g in (Phi,L,Q)]==[(4,4),(9,1),(1,9)]
    left,right=[P(Phi.resultant(g)).primitive()[1] for g in (L,Q)]
    assert left.degree()==right.degree()==40
    W=P(Phi.as_expr().subs(a,d))
    assert W.degree()==8 and left.gcd(right)==W
    q=s.Poly(Q.as_expr(),a)
    q0,q1=P(q.nth(0)),P(q.nth(1))
    assert q1.gcd(right).degree()==0
    fr=right.factor_list()[1]
    assert [(g.degree(),k) for g,k in fr]==[(8,1),(8,1),(24,1)]
    E=next(g for g,_ in fr if g.degree()==8 and g!=W)
    H=next(g for g,_ in fr if g.degree()==24)
    assert (q0+P(d)*q1).rem(W).is_zero
    assert (2*q0+P(1+d)*q1).rem(E).is_zero
    assert all(P(g.as_expr().subs(a,d)).rem(W).is_zero for g in (Phi,L,Q))
    print('Exact width projections: degrees 40,40; gcd is the diagonal octic;',flush=True)
    print('reflected projection has only two forbidden octics and one degree-24 factor.',flush=True)
    return Phi,L,Q,W,H,q0,q1

def replay():
    Phi,L,Q,W,H,q0,q1=data()
    C=flint.fmpz_mod_poly_ctx(23)
    conv=lambda P:C([int(c) for c in reversed(P.all_coeffs())])
    ww=conv(W)
    assert ww.degree()==8 and ww.is_irreducible()
    K=flint.fq_default_ctx(modulus=ww/ww[8],fq_type='FQ_NMOD')
    F=flint.fq_default_poly_ctx(K);X=F.gen();d=K.gen()
    tests=[sum((K(int(c))*X**i*d**j for (i,j),c in g.terms()),F.zero())
           for g in (Phi,L,Q)]
    assert [f.degree() for f in tests]==[4,9,1]
    assert all((f%(X-d)).is_zero() for f in tests)
    h0,h1,h2=[f//(X-d) for f in tests]
    assert h0.gcd(h1).gcd(h2).degree()==0
    print('Non-half pair: exact diagonal removed, full-degree residue gcd is 1.',flush=True)

    hh=conv(H)
    hs=hh.factor()[1]
    assert hh.degree()==24 and sorted((f.degree(),m) for f,m in hs)==[(1,1),(4,1),(7,1),(12,1)]
    for f,_ in hs:
        K=flint.fq_default_ctx(modulus=f,fq_type='FQ_NMOD')
        F=flint.fq_default_poly_ctx(K);X=F.gen();d=K.gen()
        ev=lambda P:F([int(c) for c in reversed(P.all_coeffs())])(d)
        assert ev(q1)!=0
        a=-ev(q0)/ev(q1);b=1-d;h=a/2;e=(1+d)/2
        assert all(t!=0 for t in (a,b,a-d,a-1,d,e-a,h-d))
        R4=F([1,-14,56,-84,42]); R5=F([-1,20,-120,300,-330,132])
        R=R5(a)*R4-R4(a)*R5
        td=(X-a)*(X-d)
        assert R.degree()==5 and (R%td).is_zero()
        K0=R//td
        assert K0(a)!=0 and K0(d)!=0
        KP=-a*a/(2*K0(a))*K0
        kap=-b*b/(2*KP(d))
        LS=(1-X)**2*(X-d)/b
        assert LS(h)-kap*a*a/8!=0
        gR=LS-kap*KP
        assert gR(e)==0 and gR.degree()==3
        AR=gR//(X-e)
        r0,r1=AR(d),-AR(K.one())
        J0=r0+F(T4)(b)*r1
        J1=F(T4)(a)*r0+F([F(row)(b) for row in U44])(a)*r1
        g=KP-X*X*(a-X)/a
        mark=J0*KP(a)*X+J1*KP(K.zero())*(a-X)
        assert g.degree()==3 and g.gcd(mark).degree()==0
        print('Half pair: degree',f.degree(),'residue excludes both opposite-flank and middle placements.',flush=True)
    print('All q10, n11 characteristic-zero width and contact branches close.',flush=True)

if __name__=='__main__':
    replay()
