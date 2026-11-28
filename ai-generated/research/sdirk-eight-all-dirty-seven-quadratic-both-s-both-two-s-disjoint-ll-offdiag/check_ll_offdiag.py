"""All three exact low/low off-diagonal fields; keep leading-degree drops."""
from projection_ll import CASES,project
from number_field import field,spec,gcd,trim,U
from sympy.polys.rings import ring
from sympy import Poly,QQ
PROFILES={
 'SS':([327,142],2), 'A3S':([327,388],4),'A3A3':([327,508],2)}
def run(modes):
    count=0
    for mo in modes:
        ff,rows,guards,degs=project(mo)
        ds,m1=PROFILES[mo]
        assert degs==ds and len(ff)==1
        h,n=ff[0]
        hf,K,H=field(h)
        assert n==m1 and hf.monic()==Poly(2*U**4-19*U**3+13*U**2+64*U+32,U,domain=QQ).monic()
        R,a=ring('a',K)
        f=lambda z:spec(z,R,H)
        eq=sorted((p for r in rows if (p:=f(r))),key=lambda r:r.degree())
        assert eq
        E=eq[0].monic()
        for x in eq[1:]:E=gcd(E,x%E)
        assert E.degree()==2
        assert trim(E,f(guards['clocks'][0]))==R.one
        print(mo,'exact quartic+quadratic fibre lies entirely on a=b',flush=True)
        count+=1
    print('complete LL off-diagonal exclusion',count,'phase pairs',flush=True)
if __name__=='__main__':
    from sys import argv
    run(argv[1:] or CASES)
