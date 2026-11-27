from itertools import permutations,combinations
from functools import reduce
from sympy import symbols, Poly
z=symbols('g')
def scan(p,v,w,s,t,verbose=False):
    Q=lambda x:Poly(x,z,modulus=p)
    O=Q(1);Z=Q(0);X=Q(z)
    a=(1+s)*pow(2,-1,p)%p
    def ymul(a,b):
        c=[Z]*(len(a)+len(b)-1)
        for j,x in enumerate(a):
            for k,y in enumerate(b):c[j+k]+=x*y
        return c
    def ymoment(a,j=0):
        return sum((u*pow(i+j+1,-1,p)for i,u in enumerate(a)),Z)
    def JP(a):return [Z]+[u*pow(i+1,-1,p)for i,u in enumerate(a)]
    def det(A):
        if len(A)<2:return A[0][0] if A else O
        return sum(((-1)**j*u*det([row[:j]+row[j+1:] for row in A[1:]])for j,u in enumerate(A[0])),Z)
    def gp(roots):return reduce(ymul, ([-r,O]for r in roots),[O])
    def eq(g,f,l,m): # first, second, third live sites
        G=gp([O-g*v,O-g*w,l,m]); K=gp([g*s,g*t])
        D=ymul(ymul(G,K),[-f,O])
        P=[]
        for K in (K,[Z]+K):
            P.append(ymul(G,[u-r*g for u,r in zip(JP(K),K+[Z])]))
        return [ymoment(D,j)for j in range(2)]+[ymoment(T)for T in P]
    def c0(g,arr):return eq(g,*arr)
    def show(poly): return poly.as_expr().factor(modulus=p) if not poly.is_zero else 0
    out={}
    for i,j in permutations(range(3),2):
        z0=next(k for k in range(3)if k not in [i,j])
        da=[Z,Z,Z];da[i]=X;da[j]=X*a
        c=c0(X,da)
        da[z0]=O
        df=[x-y for x,y in zip(c0(X,da),c)]
        A=list(zip(c,df))
        mins={ij:det([A[i] for i in ij]) for ij in combinations(range(4),2)}
        g=reduce(lambda x,y:x.gcd(y),mins.values())
        deg=sorted(x.degree()for x in mins.values())
        out[('none',i,j)]={'polys':mins,'gcd':g,'max':max(deg)}
        if verbose:print('none',i,j,'free',z0,deg,show(g))
    for ia,ib in [(1,a),(a,1)]:
        for vf in [v,w]:
            if not (ia+vf)%p:
                if verbose: print('pin vanishes')
                out[('pin-zero',ia,vf)]=True
                continue
            gg=Q(pow(ia+vf,-1,p))
            for ni in range(3):
                da=[Z,Z,Z]
                da[ni]=gg*ib
                ix=[j for j in range(3)if j!=ni]
                m0=c0(gg,da)
                da[ix[0]]=O; m1=c0(gg,da)
                da[ix[0]]=Z;da[ix[1]]=O;m2=c0(gg,da)
                da[ix[0]]=O;m3=c0(gg,da)
                A=[(a,b-a,c-a,d-c-b+a)for a,b,c,d in zip(m0,m1,m2,m3)]
                if ni==0:
                    assert all(p[1]==p[2]for p in A)
                    r=[det([[A[j][k]for k in [0,1,3]]for j in ii])for ii in combinations(range(4),3)]
                else:
                    var=2 if ni==1 else 1
                    r=det([[A[j][0],A[j][ix.index(var)+1]]for j in [2,3]])
                out[('pin',ia,vf,ni)]=r
                if verbose:print('pin',ia,vf,ni,[show(a)for a in r]if isinstance(r,list) else show(r))
    return out
def model_t(s,p,f):
    x=f.x
    return Poly(x*x-(s+3)*x+s,x,modulus=p)

def other_seed(s,p,f):
    x=f.x
    return Poly(x*x+(s-9)*x+s*s-9*s+18,x,modulus=p)

def check():
    import sys
    from pathlib import Path
    from importlib import util
    p=Path(__file__).resolve().parent.parent/'real-sdirk9-six-site-three-terminal'/'check.py'
    a=util.spec_from_file_location('six_site',p)
    f=util.module_from_spec(a);a.loader.exec_module(f)

    # Include the foundational tower tests, also available in the six-site replay.
    f.simple(f.seed(31),11,31)
    f.irreducible(f.first_port(11,31),31,2)
    f.simple(f.seed(17),16,17)
    f.simple(f.first_port(16,17),1,17)
    f.irreducible(f.shifted_second(16,1,17),17,3)
    def lift(p,s,v,w):
        f.simple(f.seed(p),s,p)
        f.simple(f.first_port(s,p),v,p)
        f.simple(f.shifted_second(s,v,p),w,p)

    lift(37,8,3,19)
    f.irreducible(model_t(8,37,f),37,2)
    lift(13,9,6,2)
    f.irreducible(other_seed(9,13,f),13,2)
    lift(43,26,16,39)
    f.simple(other_seed(26,43,f),28,43)
    f.irreducible(model_t(28,43,f),43,2)

    data=[];det_values=[]
    for rn,(sr,t) in enumerate([(26,18),(41,2)]):
        if sr!=26:
            f.simple(other_seed(26,43,f),sr,43)
        f.simple(model_t(sr,43,f),t,43)
        tab=scan(43,16,39,sr,t)
        pin=[int((next(v for v in z if not v.is_zero) if isinstance(z,list) else z).as_expr())%43
             for k,z in tab.items()if k[0]=='pin']
        assert len(pin)==12 and all(pin)
        det_values+=pin
        cnt=0
        for key, fam in tab.items():
            if key[0]!='none':continue
            _,i,j=key
            free=next(k for k in range(3)if k not in [i,j])
            if free==0:
                ij,kl,d=(0,3),(1,2),13
            else:
                ij,kl,d=(0,1),(1,2),12
            g,h=fam['polys'][ij],fam['polys'][kl]
            assert g.degree()==h.degree()==d
            U,V,e=g.gcdex(h)
            assert e.as_expr()==1 and U*g+V*h==e
            vec=lambda p:[int(p.nth(k))%43 for k in range(p.degree()+1)]
            data.append((d,vec(g),vec(h),vec(U),vec(V)))
            cnt+=1
        assert cnt==6
        if '--lean-data' not in sys.argv:
            print(f'Reverse root class {rn}: six degree-preserving Bézout pairs and twelve nonzero pinned mixed determinants.')
    if '--lean-data' in sys.argv:
        print('def determinantValues : List Nat :=',det_values)
        print('def allPairs : List Certificate := [')
        for ix,(d,f,g,u,v) in enumerate(data):
            print(f'  ⟨{d}, {f}, {g}, {u}, {v}⟩'+(',' if ix+1<len(data) else ''))
        print(']')
    else:
        print('Both-port placements excluded separately by degree three versus degree at most two.')
if __name__=='__main__':
    check()
