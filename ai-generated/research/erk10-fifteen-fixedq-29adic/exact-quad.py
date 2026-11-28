"""Exact characteristic-zero audit in QQ[c,a]/(D(c),a²-s(c)a+q(c))."""
import sys, time, collections, json
from math import lcm
from pathlib import Path
from fractions import Fraction
import sympy as sy
ROOT=Path(sys.argv[1])
sys.path.insert(0,str(ROOT/'erk10-fifteen-split-fixed-q-spectrum'))
sys.path.insert(0,str(ROOT/'erk10-fifteen-fixedq-29adic'))
import spectrum as S
import literal as L
from generate_remainder import P_LIST
sys.set_int_max_str_digits(0)
x=sy.Symbol('x')
P=sum(v*x**i for i,v in enumerate(P_LIST))
K=sy.QQ.alg_field(sy.CRootOf(P,0)) if hasattr(sy.QQ,'alg_field') else sy.QQ.algebraic_field(sy.CRootOf(P,0))
assert K.mod.degree()==10
C=K.unit
ka,kb=K.zero,K.zero
all_den=[]
def coeff(a):
    vals=list(reversed(a.to_list()))
    return [(int(z.numerator),int(z.denominator)) for z in vals]
def coords(t):
    ns=[coeff(t.x),coeff(t.a)]
    den=lcm(*(q for l in ns for _,q in l))
    return [[p*(den//q) for p,q in l] for l in ns],den
class Q:
    """Pair of degree <10 power-basis coordinates, not an approximate number."""
    __slots__=('x','a')
    def __init__(self,x=0,y=1):
        if isinstance(x,Q):
            v=x if y==1 else x/Q(y)
            self.x,self.a=v.x,v.a
        elif isinstance(x,type(C)):
            self.x,self.a=x,K.zero
            if y!=1:
                v=self/Q(y);self.x,self.a=v.x,v.a
        else:
            self.x,self.a=K.convert(Fraction(x,y)),K.zero
    @staticmethod
    def pair(x,a):
        z=Q.__new__(Q);z.x,z.a=x,a;return z
    def __add__(x,y):
        y=Q(y);return Q.pair(x.x+y.x,x.a+y.a)
    __radd__=__add__
    def __neg__(x):return Q.pair(-x.x,-x.a)
    def __sub__(x,y):return x+-Q(y)
    def __rsub__(x,y):return Q(y)+-x
    def __mul__(x,y):
        y=Q(y)
        if not x.a:return Q.pair(x.x*y.x,x.x*y.a)
        if not y.a:return Q.pair(x.x*y.x,x.a*y.x)
        u=x.a*y.a
        return Q.pair(x.x*y.x-kb*u,x.x*y.a+x.a*y.x+ka*u)
    __rmul__=__mul__
    def __pow__(x,n):
        if n==0:return Q(1)
        if n==1:return x
        if n<0:return (1/x)**(-n)
        u=x**(n//2);return (x if n%2 else Q(1))*u*u
    def inv(x):
        if not x.a:
            z=Q.pair(K.one/x.x,K.zero)
        else:
            sx=x.x+ka*x.a
            di=K.one/(x.x*sx+kb*x.a*x.a)
            z=Q.pair(sx*di,-x.a*di)
        return z
    def __truediv__(x,y):return x*Q(y).inv()
    def __rtruediv__(x,y):return Q(y)*x.inv()
    def __eq__(x,y):
        y=Q(y);return (x.x,x.a)==(y.x,y.a)
    def __hash__(x):
        xs=x.x.to_list()
        if not x.a and len(xs)<=1:
            return hash(Fraction(int(xs[0].numerator),int(xs[0].denominator)) if xs else 0)
        return hash((tuple(xs),tuple(x.a.to_list())))
    def __bool__(x):return bool(x.x or x.a)
    def __repr__(x):
        ns,d=coords(x);return "(deg=%s, denDigits=%s, residue=%s)"%(list(map(len,ns)),len(str(d)),mod(x) if d%29 else 'pole')
def mod(v):
    z,d=coords(v)
    if d%29==0:raise ZeroDivisionError('canonical coefficient denominator pays 29')
    return (sum(n*2**i for i,n in enumerate(z[0]))+11*sum(n*2**i for i,n in enumerate(z[1])))*pow(d,-1,29)%29
def symmetric(c,d,g,R,ims):
    e,f,h,_,_=ims
    T=S.nodes([f,g,h]);B=S.mul(S.mul([Q(0),Q(-1),Q(1)],S.nodes([c,d,e])),T)
    E0,E1=S.moment(B),S.moment(B,1)
    kk=S.moment(S.mul(S.mul([Q(0),Q(-1),Q(1)],S.nodes([c,c,R])),T))
    oo=(S.delta(c)-1)/c
    jj=S.moment(S.mul(S.mul(S.mul([Q(1),Q(-1)],S.nodes([g,h,R])),S.nodes([f,Q(0),c])),[Q(1),oo]))
    assert kk+jj-2*kk/c==0
    kk*=d*e;ll=-kk
    V=S.cubic(c);Phi=S.mul(S.nodes([Q(1),c,d,e]),S.add(V,S.scale(T,-V[0]/T[0])))
    u=E0*R*c*c-2*kk*c
    v=-E0*R*c-E0*c*c+E1*c+2*kk-ll*c
    w=-E1*R*c*c+kk*c*c
    uu,vv,ww=-S.moment(Phi,1),S.moment(Phi),S.moment(Phi,2)
    det=u*vv-v*uu
    return (v*ww-w*vv)/det,(w*uu-u*ww)/det
class DonePrefix(Exception): pass

def check(prefix=11):
    global ka,kb
    S.F=L.F=Q
    c,d,g,R=map(Q,(C,26,6,15))
    ims=S.late(c,d,g,R);s,q=symmetric(c,d,g,R,ims)
    ka,kb=s.x,q.x
    a=Q.pair(K.zero,K.one);b=s-a
    print("exact paid head scalar spectrum and monic quadratic:",[mod(z) for z in [s,q,a,b]],flush=True)
    H=S.head(c,d,g,R,a,b,ims,origin=True)
    print("all exact literal head ratios, poles",[k for k,v in H['w'].items() if coords(v)[1]%29==0],flush=True)
    T=S.nonlinear(H)
    print("all pair and nonlinear contacts exact",flush=True)
    print("coordinate denominator-paid raw lanes", {k:[coords(z)[1]%29!=0 for z in T[k]] for k in ('ys','w','u','eta')},flush=True)
    y=T['ys']
    des=L.host_system(1-y[10],1-y[9],1-y[8],T['eta'][9],T['eta'][8])[-1]
    print("three chronological exact forward taps", [repr(z) for z in des],flush=True)
    orig=L.lin
    count=0
    def paid_lin(m,r,k):
        nonlocal count
        count+=1
        z=orig(m,r,k)
        paid=[coords(x)[1]%29!=0 for x in z]
        assert all(paid), f"unpaid coefficient at row {count-1}"
        print("all 8 exact identities row",count-1,"against",k,"preceding solved columns",
              "den-paid",paid,flush=True)
        if count==prefix and prefix<11:
            raise DonePrefix
        return z
    L.lin=paid_lin
    try:
        raw=L.high_reverse(H,T,des)
    except DonePrefix:
        print("complete algebraic prefix, actual row count",prefix,flush=True)
        return None
    print("all literal eight-word rows verified, largest normalized coefficient digits",max(len(str(coords(x)[1])) for row in raw for x in row),flush=True)
    return dict(ys=[[coords(v) for v in T[k]] for k in ('ys','w','u','eta')],K=[[coords(v) for v in row] for row in raw])
if __name__=="__main__":
    import argparse
    p=argparse.ArgumentParser()
    p.add_argument("research")
    p.add_argument("--prefix",type=int,default=8,choices=range(1,12))
    p.add_argument("--save",type=Path)
    a=p.parse_args()
    h=check(a.prefix)
    if a.save is not None:
        assert h is not None, "save the full eleven-row literal only"
        a.save.write_text(json.dumps(h,separators=(',',':'))+'\n')
