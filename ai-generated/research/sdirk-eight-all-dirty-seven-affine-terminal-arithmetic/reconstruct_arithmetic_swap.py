"""Exact arithmetic S,D,S singleton opener and doubled terminal projection."""
import sympy as S
from sympy.polys.rings import ring

U,V=S.symbols('u b')
ZZ,u,b=ring('u,b',S.QQ)
def l3(y,d):return 5*y**3-3*d*d*y
def l4(y,d):return 35*y**4-30*d*d*y*y+3*d**4
def kk(y,z,d):
    return -9*d**6+15*d**4*y*y-75*d**4*y*z+15*d**4*z*z+105*d*d*y**3*z-45*d*d*y*y*z*z+105*d*d*y*z**3-175*y**3*z**3
def den(u):return 2*(u-2)*(u**3-3*u*u+1)
def hub(u):return -2+u+4*u*u-u**3
def kap(u):return 1+2*u-u*u
def num(u):return (1+4*u-4*u*u)*hub(u)+4*u*u*(3*u-2)

an,ad=hub(u),den(u)
bn=b*ad
d0,z0=2*ad-an-bn,bn-an
ee=-an-bn
ff=an+bn+2*u*ad
f,et=(S.Poly.from_dict({(j,i):c for (i,j),c in kk(y,z0,d0).to_dict().items()},V,U,domain=S.QQ) for y in (ff,ee))

def fibers():
    r=f.resultant(et)
    rs=r.factor_list()[1]
    assert sorted((g.degree(),p) for g,p in rs)==[(1,12),(1,45),(3,12),(3,45),(18,1),(58,1)]
    for pol,ex in rs:
        if pol.degree()==1:
            assert pol.monic().as_expr() in (U-1,U-2)
            if pol.monic().as_expr()==U-1:
                assert hub(1)==den(1) and kap(1)==2
            print('guarded linear projection',pol.as_expr(),ex,flush=True)
            continue
        if pol.degree()==3 and pol.monic().as_expr()==U**3-3*U**2+1:
            print('guarded denominator cubic',pol.as_expr(),ex,flush=True)
            continue
        assert pol.is_irreducible
        E=S.QQ.algebraic_field((pol,U))
        ua=E.unit
        ah=hub(ua)/den(ua)
        assert ah and ua and 3*ua!=E(2) and kap(ua) and hub(ua) and num(ua)
        assert (ah==E.one)==(pol.degree()==3)
        RR,T=ring('b',E)
        def sp(P):return sum(RR(E(c)*ua**i)*T**j for (j,i),c in P.terms())
        fp,ep=sp(f),sp(et)
        gg=fp.gcd(ep).monic()
        print('gap degree',pol.degree(),'a=1',ah==E.one,'b-fibre gcd degree',gg.degree(),flush=True)
        if pol.degree()==3:
            assert gg==(T-1)**3
            print('  exact b gcd is (b−1)^3',flush=True)
            yield pol,E,ua,ah,RR,T,fp,ep,T-1
        else:
            assert gg.degree()==1
            yield pol,E,ua,ah,RR,T,fp,ep,gg

def reconstructed():
    for pol,E,u,a,RR,T,fp,ep,g in fibers():
        assert g.degree()==1
        b=-g[(0,)]/g[(1,)]
        assert not fp.evaluate(T,b) and not ep.evaluate(T,b)
        d=2-a-b
        if pol.degree()==3:
            assert a==E.one and b==E.one and not d
            print('covered a=1 cubic: unique b=1 forces zero interval',flush=True)
            continue
        z=b-a
        xf=1+u
        xe=d-1
        yf=2*xf-d
        ye=2*xe-d
        assert all((d,d-2,l3(z,d),l4(z,d)))
        assert (yf==ye)==(pol.degree()==18)
        print('guarded arithmetic S,D,S mesh',pol.degree(),'coincident',yf==ye,flush=True)
        yield 'T',E,u,a,b,d,z,xf,yf,ye

if __name__=='__main__':
    list(reconstructed())
