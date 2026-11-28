"""Fixed exact low/low boundary proof including all possible fourth reads."""
import sympy as S
from low_geometry import graph
from literal_fourth import exact
x=S.Symbol('a')
C={
 'A3A3':28*x**6-168*x**5+193*x**4+348*x**3-438*x**2-268*x-10,
 'SS':7*x**6-70*x**5+263*x**4-408*x**3+10*x**2+740*x-682}
def run():
    for mode in ('A3A3','A3S','SS'):
        assert graph(mode,'half')==S.Poly(1,x,domain=S.QQ)
        Q=graph(mode,'curve')
        if mode=='A3S':
            assert Q==S.Poly(1,x,domain=S.QQ)
        else:
            E=S.Poly(C[mode],x,domain=S.QQ)
            assert Q.monic()==E.monic() and E.is_irreducible
            K=S.QQ.algebraic_field((E,x));a=K.unit
            H=2*K.one/(a-2)
            assert exact(K,a,H,mode)==[True,True,True]
            print(mode,'rank-zero-curve sextic: all three fourth clock options excluded',flush=True)
    P=S.Poly(7*(2*x-1)**2-36,x,domain=S.QQ)
    assert P.is_irreducible
    K=S.QQ.algebraic_field((P,x));a=K.unit
    assert exact(K,a,2*K.one,'A3A3')==[True,True,True]
    print('nonzero R line at H=2, A3A3: all fourth options excluded',flush=True)
    for m in ('pcenter','qcenter'):
        assert graph('A3S',m)==S.Poly(1,x,domain=S.QQ)
    print('all low-law R-line-zero and H=2 cases, and A3/S identical S offsets, excluded',flush=True)
if __name__=='__main__':run()
