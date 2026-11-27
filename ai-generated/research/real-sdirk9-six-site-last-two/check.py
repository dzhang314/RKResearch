"""Exact exclusion gates of the last two six-site SDIRK9 twin-port charts."""
import sys
from importlib import util
from math import comb
from pathlib import Path
from sympy import Poly, symbols, interpolate, integrate, cancel, rem, expand, Rational
import check_ap
import check_siblings
import check_anchors

def load_forward_arithmetic():
    # Default: released sibling. An explicit path also supports package staging.
    argv=[x for x in sys.argv[1:]if not x.startswith('--')]
    p=Path(argv[0]) if argv else Path(__file__).parent.parent/'real-sdirk9-six-site-three-terminal'/'check.py'
    spec=util.spec_from_file_location('forward',p)
    out=util.module_from_spec(spec);spec.loader.exec_module(out)
    return out

def exact_early_calculation():
    a,b,x = symbols("a b x")
    # Regular AP with nonzero second quadratic defect and third tap u3.
    den=a**3-7*a*a+10*a-2
    u3=-2*(a-1)*(3*a-5)/den
    g1=2*a-1-a*a/2
    rr=2*a-1
    g2=2*rr-1-rr*rr/2+u3*(a-1)
    assert cancel(2*g1*((rr-1)/2+u3*(g1-Rational(1,2)))-(rr-1)*g2)==0
    gate=check_ap.P.subs({check_ap.A:a,check_ap.T:x})
    half=Rational(1,2)
    h=interpolate([(1,half),(a,g1),(rr,g2)],x)
    assert cancel(integrate(h,x)-h+gate/(6*den))==0
    # Pure rank-two defect in the vanishing-second-defect case.
    deg=(a-1)*(3*b*b+2*(b-1)-b**3)+(3*a*a-2)*(b*b/2-2*b+1)
    assert rem(expand(deg+(b*b-4*b+2)*(a*b-5*a-b+3)),a*a-4*a+2,a)==0
    assert expand((a-2)**2*(a-3))==a**3-7*a*a+16*a-12

def five_site(p,v,w):
    q=symbols('g')
    Q=lambda n,r:Poly(sum((-1)**(n-i)*comb(n,i)*comb(n+i,i)*(q*r)**i
                           for i in range(n+1)),q,modulus=p)
    def f(x):
        return Q(5,x)*Q(4,1)+Q(4,x)*Q(5,1)
    return f(v),f(w)

def main():
    f=load_forward_arithmetic()
    x=f.x
    # Independently replay the common characteristic-zero tower certificates.
    f.simple(f.seed(31),11,31)
    f.irreducible(f.first_port(11,31),31,2)
    f.simple(f.seed(17),16,17)
    f.simple(f.first_port(16,17),1,17)
    f.irreducible(f.shifted_second(16,1,17),17,3)
    def lift(p,s,v,w):
        f.simple(f.seed(p),s,p)
        f.simple(f.first_port(s,p),v,p)
        f.simple(f.shifted_second(s,v,p),w,p)
    def other(s,p):
        return Poly(x*x+(s-9)*x+s*s-9*s+18,x,modulus=p)
    lift(13,9,6,2)
    f.irreducible(other(9,13),13,2)
    lift(37,8,3,19)
    def qa(p):return Poly(x*x-4*x+2,x,modulus=p)
    f.irreducible(qa(37),37,2)

    results=[];constants=[]
    def bez(p,d,pair):
        a,b=pair
        assert a.degree()==b.degree()==d
        U,V,e=a.gcdex(b)
        assert e.as_expr()==1 and U*a+V*b==e
        array=lambda Q:[int(Q.nth(i))%p for i in range(Q.degree()+1)]
        results.append((p,d,array(a),array(b),array(U),array(V)))
    def cst(p,arr):
        x=[int(v.as_expr())%p for v in arr]
        assert all(x)
        constants.extend((p,y)for y in x)

    bez(37,9,five_site(37,3,19))
    lift(43,26,16,39)
    for sr in [26,41]:
        if sr!=26:f.simple(other(26,43),sr,43)
        ff,ss=check_anchors.scan(43,16,39,(1+sr)*pow(2,-1,43)%43,sr)
        bez(43,10,ff[:2]); assert len(ss)==6
        # The already paid terminal s_r is disjoint from both ports.
        cst(43,ss[:4])
        F,C=check_siblings.scan(43,16,39,sr)
        for k,d in [('none',9),('terminal-repeat',10),(('one-Mid',0),10)]:
            bez(43,d,F[k][:2])
        cst(43,C.values())
    # Avoid an accidental degree drop in the other one-mid pin by changing
    # the good residue embedding, not the characteristic-zero branch.
    F,_=check_siblings.scan(37,3,19,8)
    bez(37,10,F[('one-Mid',1)][:2])
    lift(43,28,4,31)
    f.simple(other(28,43),26,43)
    F,_=check_siblings.scan(43,4,31,26)
    bez(43,10,F[('one-Mid',1)][:2])

    lift(41,30,3,18)
    a=19
    f.simple(qa(41),a,41)
    for b in ((4-a)%41,(2*a-1)%41):
        ff,ss=check_anchors.scan(41,3,18,a,b)
        bez(41,10,ff[:2]); cst(41,ss)

    assert len(results)==13 and len(constants)==38
    if '--lean-data' in sys.argv:
        print('def pairs : List Certificate := [')
        for ix,(p,d,f,g,u,v) in enumerate(results):
            print(f'  ⟨{p}, {d}, {f}, {g}, {u}, {v}⟩'+(',' if ix+1<len(results) else ''))
        print(']')
        print('def residues : List (Nat × Nat) := [')
        print('  '+', '.join(f'({p}, {i})'for p,i in constants))
        print(']')
        return

    exact_early_calculation()
    test=check_ap.scan(37,3,19)
    assert len(test)==59 and all(test.values()), [k for k,r in test.items()if not r]
    print('Exact original third-row/cubic primitive identities checked symbolically.')
    print('Forward tower good reductions and the two adjunction irreducibilities checked.')
    print('13 full-degree Bézout pairs and 38 nonzero pinned/cofactor values.')
    print('Regular AP: all 59 exact finite or compactification checks passed at p=37.')

if __name__=='__main__':
    main()
