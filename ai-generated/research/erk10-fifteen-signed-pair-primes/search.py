"""Search for exact width-15 ERK10 literals in the first signed-pair chart."""
from pathlib import Path
from math import prod
from functools import cache
from contextlib import redirect_stdout
from io import StringIO
from itertools import permutations
import json, sys, importlib.util
from sympy import primerange, sqrt_mod

base=Path(sys.argv[1])
out=Path(sys.argv[2])
limit=int(sys.argv[3])
def load(name,path):
    sp=importlib.util.spec_from_file_location(name,path)
    ns=importlib.util.module_from_spec(sp)
    sp.loader.exec_module(ns)
    return ns
C=load('chart',base/'erk10-fifteen-17-power'/'chart.py')
G=load('geometry',base/'erk10-fifteen-17-power'/'geometry.py')
step={int(r[0]) for r in json.loads((base/'erk10-stepanov-all-primes'/'seeds.json').read_text())['seeds']}

class StrictF(C.F):
    def inv(self,a):
        assert a%self.p
        return super().inv(a)

def N(a):
    return ((((((((5376000*a-10590720)*a+9105600)*a-4477616)*a+1385568)*a-279450)*a+36720)*a-3036)*a+144)*a-3

def Np(a):
    return (((((((48384000*a-84725760)*a+63739200)*a-26865696)*a+6927840)*a-1117800)*a+110160)*a-6072)*a+144

def det(M,p):
    M=[list(map(lambda x:x%p,row)) for row in M]
    res=1
    n=len(M)
    for j in range(n):
        k=next((i for i in range(j,n) if M[i][j]),None)
        if k is None: return 0
        if k!=j: M[k],M[j]=M[j],M[k];res=-res
        q=M[j][j];res=res*q%p
        jq=pow(q,-1,p)
        for i in range(j+1,n):
            h=M[i][j]*jq%p
            M[i][j:]=[(a-h*b)%p for a,b in zip(M[i][j:],M[j][j:])]
    return res%p

def guards(T,F,chart,literal,donor):
    p=F.p; _,_,d,e,f,g=T
    x=[(1-y)%p for y in literal['reverse_y']]
    w=literal['b'][:4:-1]
    y=literal['reverse_y']
    h=chart.h+[chart.hu[z] for z in (d,e,f,g)]
    u=chart.u+[0]*4
    O=[[v*pow(xx,j,p)%p for v,xx in zip(w,x)]for j in range(5)]
    O += [[v*z%p for v,z in zip(w,feat)] for feat in (u,h,[yy*hh%p for yy,hh in zip(y,h)])]
    O +=[[int(i==j)for i in range(10)]for j in (9,8)]
    xx=[sum(row)%p for row in literal['a'][5:]]
    K=[[(F.dot(literal['a'][5+j][5:],[pow(z,k,p) for z in xx])-pow(xx[j],k+1,p)*F.inv(k+1))%p
         for k in (1,2)] for j in range(2)]
    return {'observer_det':det(O,p),'kernel_det':det(K,p),'donor_det':donor,'h_split':(chart.h[4]-chart.h[3])%p,
            'first_six_det':det(chart.M,p),
            'first_five_det':det([r[:4]+[r[5]] for r in chart.M[:5]],p),
            'd_fixed_geometry_det':det([[r[j] for j in (0,1,3,4,5)]for r in G.jac(T,p)],p)}

results=[]
for p0 in primerange(13,limit+1):
    p=int(p0)
    if p in step or p==17:
        continue
    F=StrictF(p)
    result=None
    for a in range(1,p):
        if N(a)%p or (2*a)%p in (0,1,a) or a==1:
            continue
        b=2*a%p
        q4=(896*a**4-840*a**3+300*a*a-48*a+3)%p
        if not q4: continue
        m=-(5600*a**4-5400*a**3+1984*a*a-327*a+21)*F.inv(5*q4)%p
        n=(1600*a**4-1600*a**3+611*a*a-105*a+7)*F.inv(5*q4)%p
        discriminant=(m*m-4*n)%p
        if not discriminant: continue
        ds=sqrt_mod(discriminant,p)
        if ds is None: continue
        roots=[(-m+ds)*F.inv(2)%p,(-m-ds)*F.inv(2)%p]
        U=F.mul([-1,1],[n,m,1])
        M=[0,0,b*b,-2*b,1]
        UM=F.mul(U,M)
        s0,s1,s2=[F.integ([0]*j+UM) for j in range(3)]
        if not s0: continue
        assert (s0*s2-s1*s1)%p==0
        e=s1*F.inv(s0)%p
        if len({0,1,a,b,e,*roots})!=7: continue
        nu=F.mul(U,[-e,1])
        G1=F.hull([0,a,b])
        for d in range(2,p):
            if d in (a,b,e,*roots): continue
            poly=F.mul(F.mul(nu,[-d,1]),G1)
            den=F.integ(poly)
            if not den: continue
            c=F.integ([0]+poly)*F.inv(den)%p
            if c in (0,1,a,b,d,e,*roots): continue
            for f,g in permutations(roots):
                T=[a,c,d,e,f,g]
                try:
                    eq,(mu,donor,zz,r1,r2)=G.system(T,p,True)
                    if any(eq): continue
                    W={z:mu[z]*F.inv(prod(z-u for u in mu if z!=u))%p for z in mu}
                    if not all(W.values()): continue
                    ch=C.Chart(a,b,c,(d,e,f,g),W,mu,F)
                    L=ch.terminal((d,e,f,g))
                    if L is None: continue
                    lit=ch.forward((d,e,f,g),L)
                    if not lit: continue
                    gd=guards(T,F,ch,lit,donor)
                except (AssertionError,ValueError,ZeroDivisionError): continue
                if not all(gd.values()): continue
                x=[sum(row)%p for row in lit['a']]
                defect=(11*sum(w*pow(z,10,p) for w,z in zip(lit['b'],x))-1)%p
                if not defect:continue
                with redirect_stdout(StringIO()):
                    assert C.actual(lit)
                result={'p':p,'geometry':T,'guards':gd,'a_q9_derivative':Np(a)%p,
                        'defect':defect,'A':lit['a'],'b':lit['b'],'low_clocks':lit['low_clocks']}
                break
            if result: break
        if result: break
    if result:
        results.append(result)
        out.write_text(json.dumps(results,indent=2)+'\n')
        print('prime',p,'geometry',result['geometry'],'jacobian',result['guards']['d_fixed_geometry_det'],
              'defect',result['defect'],flush=True)
print('total new verified prime fields',len(results))
