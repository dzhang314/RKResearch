from fractions import Fraction as F
from itertools import combinations, permutations, product
from functools import lru_cache
from math import comb, lcm
from pathlib import Path

B=32768
A6=(-5,0,135,0,-495,0,429)
A7=(0,-35,0,385,0,-1001,0,715)
Q=(tuple([0]+[3*v for v in A7]),tuple([-3*v for v in A7]+[0]),tuple([-5*v for v in A6]+[0,0]))
# Q are the constant, D and lambda coefficient lists of 2145*T_y respectively.

def words():
    for rid in combinations(range(8),4):
        for perm in permutations('uahz'):
            r=iter('1234');dt=iter(perm)
            w=''.join(next(r) if i in rid else next(dt) for i in range(8))
            ps={c:w.index(c) for c in w}
            p=lambda c:sum(j<ps[c] for j in rid)
            if p('u')<2 or p('z')>2:continue
            if ps['a']<ps['u']:
                if not 1<=p('a')<p('u'):continue
            elif not p('u')<p('a'):continue
            if ps['h']>ps['z']:
                if not p('z')<p('h')<=3:continue
            elif not p('h')<p('z'):continue
            yield (w,rid,tuple(ps[c] for c in 'uahz'))

TESTS=list(words())

@lru_cache(8192)
def taylor(x):
    y=2*x-B
    h=[y**i for i in range(9)]
    R=[B**i for i in range(9)]
    return tuple(tuple(sum(a[i]*comb(i,j)*h[i-j]*R[8+j-i] for i in range(j,9))
                       for j in range(9)) for a in Q)

def corners(box):
    sd,si,td,ti=box
    S=1<<sd; T=1<<td
    den=20*S*T
    return den,tuple((-25*(S-s)*t,(15*s-3*S)*T)
                      for s,t in product((si,si+1),(ti,ti+1)))

def taylor_bounds(C,x):
    den,cn=C
    a,b,c=taylor(x)
    ls=[];hs=[]
    for e,d,k in zip(a,b,c):
        es=[den*e+u*d+v*k for u,v in cn]
        ls.append(min(es));hs.append(max(es))
    return ls,hs

def max_var(lo,hi,neg):
    m=-100; p=-100
    for i,(l,h) in enumerate(zip(lo,hi)):
        if l==h==0:continue
        if neg and i%2:l,h=-h,-l
        m,p=((max(0,m,p+1) if l<0 else -100),
             (max(0,p,m+1) if h>0 else -100))
    return max(m,p,0)

def laguerre_negative(C,x,k):
    lo,hi=taylor_bounds(C,x)
    m=8-k
    ab=max(lo[k+1]**2,hi[k+1]**2)
    cd=min(x*y for x,y in product((lo[k],hi[k]),(lo[k+2],hi[k+2])))
    return (m-1)*(k+1)*ab < m*(k+2)*cd

def cage_assert(box,X):
    C=corners(box)
    if any(not 0<=l<=r<=B for l,r in X):return False
    for i,(l,r) in enumerate(X):
        if l and max_var(*taylor_bounds(C,l),True)>i:return False
        if r<B and max_var(*taylor_bounds(C,r),False)>7-i:return False
    return True

@lru_cache(16384)
def bern_coeff(n,e,a,b):
    f=lcm(*(comb(n,k) for k in range(n+1)))
    den=lcm(*(k+e+1 for k in range(n+1)))
    diff=b-a
    return tuple(tuple((den//(i+e+1))*sum(comb(i,k)*a**(i-k)*diff**k*comb(j,k)*(f//comb(n,k))
           for k in range(min(i,j)+1)) for i in range(n+1)) for j in range(n+1))

def poly(R):
    c=[1]
    for r in R:
        c=[-r*c[0]]+[c[i-1]-r*c[i] for i in range(1,len(c))]+[c[-1]]
    return c

def test_margin(e,d,roots):
    # In integer coordinates, integrate t^e times product(d*t-root).
    # Discard a box test unless all Bernstein coefficients, at every root vertex,
    # have the same strict sign. The returned margin divides out the exact scale.
    n=len(roots)
    W=bern_coeff(n,e,*d)
    sg=0
    least=None
    for R in product(*roots):
        q=poly(R)
        for w in W:
            s=sum(u*v for u,v in zip(w,q))
            if s==0:return None
            ss=1 if s>0 else -1
            if sg and ss!=sg:return None
            sg=ss
            least=abs(s) if least is None else min(least,abs(s))
    den=B**n*lcm(*(comb(n,k) for k in range(n+1)))*lcm(*(k+e+1 for k in range(n+1)))
    return F(least,den)


def every_word_has_a_port(X):
    cache={}
    XR=[(B-b,B-a) for a,b in X]
    margin=F(1)
    def getter(rt,d,e,extra=None,ref=False):
        key=(rt,d,e,extra,ref)
        if key not in cache:
            Y=XR if ref else X
            roots=[Y[i] for i in rt]
            if extra is not None:roots.append(Y[extra])
            cache[key]=test_margin(e,Y[d],roots)
        return cache[key]
    for word,rt,(u,a,h,z) in TESTS:
        P=((u,1,None,False),(z,1,None,True),(u,2,None,False),(z,2,None,True),
           (a,1,u,False),(h,1,z,True))
        for d,e,x,ref in P:
            v=getter(rt,d,e,x,ref)
            if v is not None:
                margin=min(margin,v)
                break
        else:
            raise AssertionError((word,X))
    return margin


def ev(P,x):
    out=0
    for a in reversed(P):out=out*x+a
    return out


def derivative(P):
    return tuple(j*P[j] for j in range(1,len(P)))


def check_reference():
    # Centered moments for the weight 1-y^2; common positive factors do not matter.
    m=lambda j:F(0) if j%2 else F(4,(j+1)*(j+3))
    for n,P in ((6,A6),(7,A7)):
        assert len(P)==n+1 and P[-1]>0
        assert all(sum(v*m(i+j) for i,v in enumerate(P))==0 for j in range(n))
    # Ratio of monic x-coordinate norms; scale changes by 2^-2 from y to x.
    norm=lambda P:sum(v*w*m(i+j) for i,v in enumerate(P) for j,w in enumerate(P))/P[-1]**2
    assert norm(A7)/(4*norm(A6))==F(21,340)
    # (1-y^2) A7'(y)+7y A7(y)=7 A6(y), yielding the reference residues.
    c=[0]*9
    for i,v in enumerate(derivative(A7)):
        c[i]+=v;c[i+2]-=v
    for i,v in enumerate(A7):c[i+1]+=7*v
    assert c==[7*v for v in A6]+[0,0]
    p6=F(ev(A6,-1),429*2**6)
    p7=F(ev(A7,-1),715*2**7)
    assert p6==F(1,429) and p7==-F(1,1430)
    assert F(2*ev(derivative(A6),-1),ev(A6,-1))==-27
    assert F(2*ev(derivative(A7),-1),ev(A7,-1))==-35
    assert p6/p7==F(-10,3) and (p6/p7)*(-27+35)==F(-80,3)
    intervals=[(F(1,20),F(1,16)),(F(4,25),F(13,80)),(F(19,60),F(8,25))]
    assert 0<intervals[0][0]<intervals[0][1]<intervals[1][0]<intervals[1][1]<intervals[2][0]<intervals[2][1]<F(1,2)
    assert A7[0]==0 and all(A7[i]==0 for i in range(0,len(A7),2))
    for a,b in intervals:assert ev(A7,2*a-1)*ev(A7,2*b-1)<0
    # Nearest-two lower bounds for sum v_i/(x-gamma_i)^2 in the three left gaps.
    dg=[intervals[i+1][1]-intervals[i][0] for i in (0,1)]+[F(1,2)-intervals[2][0]]
    for (a,_),g in zip(intervals,dg):
        assert 8*F(20,21)*a*(1-a)/g**2>F(80,3)


def check_cover(rows):
    # Each active t interval on every s slice is an exact tiling.
    ds=max(r[0] for r in rows); dt=max(r[2] for r in rows)
    rectangles=[]
    for a,b,c,d,*_ in rows:
        assert 0<=a<=32 and 0<=c<=32 and 0<=b<1<<a and 0<=d<1<<c
        es=1<<(ds-a); et=1<<(dt-c)
        rectangles.append((b*es,(b+1)*es,d*et,(d+1)*et))
    cuts=sorted({0,1<<ds}|{x for a,b,_,_ in rectangles for x in (a,b)})
    for l,h in zip(cuts,cuts[1:]):
        U=sorted((c,d) for a,b,c,d in rectangles if a<=l and h<=b)
        i=0
        for c,d in U:
            assert i==c<d,(l,h,i,c,d)
            i=d
        assert i==1<<dt,(l,h,i)


def main():
    check_reference()
    assert len(TESTS)==141 and len({w for w,_,_ in TESTS})==141
    assert sum(1 for _,_,(u,a,h,z) in TESTS if u<z)==11
    rows=[tuple(map(int,line.split())) for line in Path(__file__).with_name('cells.tsv').read_text().splitlines()]
    assert len(rows)==127 and all(len(r)>=5 for r in rows)
    check_cover(rows)
    cage=lag=0
    cap=F(1)
    for row in rows:
        box=row[:4]
        assert row[4] in (0,2)
        if row[4]==0:
            assert len(row)==21
            X=list(zip(row[5::2],row[6::2]))
            assert len(X)==8 and cage_assert(box,X),row
            cap=min(cap,every_word_has_a_port(X))
            cage+=1
        else:
            assert len(row)==7
            k,x=row[5:7]
            assert 0<=k<=6 and -B<=x<=2*B
            assert laguerre_negative(corners(box),x,k),row
            lag+=1
    assert (cage,lag)==(123,4)
    dec=int(cap*10**9)
    assert dec>0
    print('127 cells tile the whole compact square; 4 fail real-rootedness.')
    print('123 conditional eight-site cages verified.')
    print('141 exact root/mark words in each cage: every word violates a paid port.')
    print('Smallest certified normalized signed bound at least', dec, '/ 1000000000.')


if __name__=='__main__':
    main()
