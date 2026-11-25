from fractions import Fraction as F
from itertools import combinations, permutations, product
from functools import lru_cache
from math import comb, lcm
from pathlib import Path
import json

HERE=Path(__file__).parent
N, DATARO = json.loads((HERE/'determinants.json').read_text())
DAT={int(k): v for k,v in DATARO.items()}
ORDERS=('1z2ah3u','1z2ha3u','h1z2u3a','h1z2a3u','z1a2h3u','z1h2u3a','z1h2a3u','z1ah2u3','z1ha2u3')
FIXED=((0,-1), (0,-1), (1,-1), (4,1), (2,-1), (1,-1), (5,-1), (3,1), (3,1))
# Tests: L1,L2,LA,R1,R2,RH in normalized physical variables
MOMS={
   0: tuple(F(1,i+2) for i in range(6)),
   1: tuple(F(1,i+3) for i in range(6)),
   2: tuple(F(1,i+2) for i in range(6)),
   3: tuple(F(1,(i+1)*(i+2)) for i in range(6)),
   4: tuple(F(2,(i+1)*(i+2)*(i+3)) for i in range(6)),
   5: tuple(F(1,(i+1)*(i+2)) for i in range(6)),
}
SCALE=8192

def mat_det(A):
    # Exact fraction-free Bareiss, with row swaps (used for checking determinant templates).
    A=[r[:] for r in A]; n=len(A); sg=1; den=1
    for k in range(n-1):
        if not A[k][k]:
            for i in range(k+1,n):
                if A[i][k]:
                    A[k],A[i]=A[i],A[k];sg=-sg;break
            else:return 0
        p=A[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                v=A[i][j]*p-A[i][k]*A[k][j]
                q,r=divmod(v,den);assert r==0
                A[i][j]=q
        den=p
    return sg*A[-1][-1]

def polval(k,t,x):
    return sum(d*t**i*x**j for i,j,d in DAT[k])

def check_templates():
    # Degree ≤ n separately in t,x; a product grid of n+1 integers determines it.
    assert N==lcm(*((j+2)*(j+3) for j in range(15)))
    V=[N//((j+2)*(j+3)) for j in range(15)]
    for n in (6,7):
        assert len({(i,j) for i,j,d in DAT[n]})==len(DAT[n])
        assert all(0<=i<=n and 0<=j<=n for i,j,d in DAT[n])
        for t,x in product(range(n+1),repeat=2):
            b=[V[j+1]+t*(V[j]-V[j+1]) for j in range(2*n)]
            A=[[b[i+j+1]-x*b[i+j] for i in range(n)] for j in range(n)]
            assert polval(n,t,x)==mat_det(A)

@lru_cache(None)
def radau(sdepth,sindex):
    t=F(sindex,1<<sdepth)
    d0=-polval(7,t,0)/polval(6,t,0)
    d1=-polval(7,t,1)/polval(6,t,1)
    assert d0<0<d1
    return d0,d1

def delta_range(box):
    sdepth,si,kdepth,ki=box
    S=1<<sdepth; K=1<<kdepth
    j0,j1=F(ki,K),F(ki+1,K)
    dlo0,dlo1=radau(sdepth,si)
    dhi0,dhi1=radau(sdepth,si+1)
    assert dhi0<=dlo0<0<dlo1<=dhi1
    d_lo=(1-j0)*dhi0+j0*dlo1
    d_hi=(1-j1)*dlo0+j1*dhi1
    return d_lo,d_hi

BC=lcm(*(comb(7,k) for k in range(8)))
@lru_cache(4000)
def bern_poly(sdepth,si,xn):
    # Evaluates both bivariate determinant templates at x=xn/SCALE, then
    # changes variables t=(si+Y)/2^sdepth and gives degree-seven Bernstein
    # coefficients of the resulting polynomials, in a common positive scale.
    sd=1<<sdepth
    xp=[xn**j*SCALE**(7-j) for j in range(8)]
    coeff=[]
    for k in (7,6):
        p=[0]*8
        for i,j,d in DAT[k]:p[i]+=d*xp[j]
        q=[sum(p[i]*comb(i,k)*si**(i-k)*sd**(7-i) for i in range(k,8))
           for k in range(8)]
        coeff.append(tuple(sum(q[k]*comb(j,k)*(BC//comb(7,k)) for k in range(j+1))
                      for j in range(8)))
    return coeff

def bracks(box,X):
    slo,si,_,_=box
    if not all(0<=a<b<=SCALE for a,b in X):return False
    if not all(X[i][1]<X[i+1][0] for i in range(6)):return False
    ends=delta_range(box)
    for i,(lo,hi) in enumerate(X):
        for x,sg in ((lo,(-1)**i),(hi,(-1)**(i+1))):
            if x==0 or x==SCALE:continue # actual nodes lie strictly inside
            bs,cs=bern_poly(slo,si,x)
            if not all(sg*(d.denominator*b+d.numerator*c)>0 for d in ends
                       for b,c in zip(bs,cs)):return False
    return True

def test_interval(T,s,R,U,A,H,Z):
    lo,hi=s
    if T in (0,1,2):
        E=A if T==2 else U
        el,eh=E
        if el==0:return None
        gg=lambda t,x:(1-t)*x/(t+(1-t)*x)
        G=(gg(hi,el), gg(lo,eh))
        roots=[(rl/eh,rh/el) for rl,rh in R]
        if T==2:roots.append((U[0]/eh,U[1]/el))
    else:
        E=H if T==5 else Z
        el,eh=E
        if eh==1:return None
        G=((1-hi)*(1-eh),(1-lo)*(1-el))
        roots=[((rl-eh)/(1-eh),(rh-el)/(1-el)) for rl,rh in R]
        if T==5:roots.append(((Z[0]-eh)/(1-eh),(Z[1]-el)/(1-el)))
    return G,roots

def test_num_poly(rs):
    coeff=[1]
    for r in rs:
        new=[-r*coeff[0]]+[coeff[i-1]-r*coeff[i] for i in range(1,len(coeff))]+[coeff[-1]]
        coeff=new
    return coeff

def signed_margin(args,T,sg):
    G,roots=args
    M=MOMS[T]
    out=[]
    for rs in product(*roots):
        P=test_num_poly(rs)
        f=sum(v*M[i] for i,v in enumerate(P))
        g=sum(v*(M[i+1]-M[i]) for i,v in enumerate(P))
        out.extend(sg*(f+gamma*g) for gamma in G)
    return min(out)


def test_box(box,X):
    sd,si,_,_=box
    s=(F(si,1<<sd), F(si+1,1<<sd))
    B=[(F(a,SCALE),F(b,SCALE)) for a,b in X]
    margins=[]
    for w,(t,sg) in zip(ORDERS,FIXED):
        v=dict(zip(w,B)); R=[v[r] for r in '123']
        args=test_interval(t,s,R,*[v[r] for r in 'uahz'])
        assert args is not None
        m=signed_margin(args,t,sg)
        assert m>0,(box,w,t,sg,m)
        margins.append(m)
    return margins


def window_words(k):
    roots=tuple(str(i+1) for i in range(k)); marks='uahz'
    for pos_roots in combinations(range(k+4),k):
        for perm_marks in permutations(marks):
            R=iter(roots); C=iter(perm_marks)
            word=''.join(next(R) if i in pos_roots else next(C) for i in range(k+4))
            p={a:word.index(a) for a in word}
            n=lambda a: sum(p[j]<p[a] for j in roots)
            if n('u')<2 or k-n('z')<2: continue
            if p['a']<p['u']:
                if not 1<=n('a')<n('u'): continue
            elif not n('u')<n('a'): continue
            if p['h']>p['z']:
                if not n('z')<n('h')<=k-1: continue
            elif not n('h')<n('z'): continue
            yield word


def three_change_order_check():
    ws=list(window_words(3))
    counts=[]; kept=[]
    for w in ws:
        p={a:w.index(a) for a in w}
        if sum(p[j]<p['u'] for j in 'ahz')<2: continue
        if sum(p[j]>p['z'] for j in 'uah')<2: continue
        if not any(p[j]<p['a'] for j in 'hz'): continue
        if not any(p[j]>p['h'] for j in 'ua'): continue
        counts.append(w)
        def sign(t,e):
            return (-1)**sum(p[j]>p[t] for j in '123') * (1 if p[t]>p[e] else -1)
        ok=True
        for stop,side_left,erasures in [('u',True,'ahz'),('z',False,'uah'),
                                         ('a',True,'u'),('h',False,'z')]:
            for erasure in erasures:
                if not any(sign(j,erasure)==-sign(stop,erasure)
                           for j in 'uahz' if j not in (stop,erasure)
                           and (p[j]<p[stop])==side_left):
                    ok=False
        if ok: kept.append(w)
    assert (len(ws),len(counts),len(kept))==(29,20,9)
    assert len(set(ORDERS))==len(ORDERS) and set(kept)==set(ORDERS)
    w4=list(window_words(4))
    assert len(w4)==141 and sum(w.index('u')<w.index('z') for w in w4)==11


def check_cover(rows):
    # Sweep all t cuts in a common integer scale and demand the active j
    # intervals exactly tile their whole integer range on every open slice.
    ds=max(row[0] for row in rows); dj=max(row[2] for row in rows)
    rect=[]
    for s,si,j,ji,*_ in rows:
        assert 0<=s<=32 and 0<=j<=32 and 0<=si<1<<s and 0<=ji<1<<j
        u=1<<(ds-s); v=1<<(dj-j)
        rect.append((si*u,(si+1)*u,ji*v,(ji+1)*v))
    cuts=sorted({0,1<<ds}|{s for a,b,_,_ in rect for s in (a,b)})
    for lo,hi in zip(cuts,cuts[1:]):
        J=sorted((c,d) for a,b,c,d in rect if a<=lo and hi<=b)
        x=0
        for c,d in J:
            assert x==c<d,(lo,hi,x,c,d)
            x=d
        assert x==1<<dj,(lo,hi,x,dj)


def main():
    check_templates()
    three_change_order_check()
    rows=[tuple(map(int,line.split())) for line in (HERE/'boxes.tsv').read_text().splitlines()]
    assert len(rows)==1212 and all(len(r)==18 for r in rows)
    check_cover(rows)
    margins=[F(1)]*len(ORDERS)
    for row in rows:
        box=row[:4]; X=list(zip(row[4::2],row[5::2]))
        assert len(X)==7 and bracks(box,X),row
        margins=list(map(min,zip(margins,test_box(box,X))))
    caps=[int(m*10**8) for m in margins]
    assert min(caps)>0
    print('1212 boxes cover both compact parameters; seven ordered roots per box verified.')
    print('Nine orders, signed polynomial lower bounds (denominator 100000000):')
    for w,(t,sg),cap in zip(ORDERS,FIXED,caps):
        print(w,('L1','L2','LA','R1','R2','RH')[t],'+ ' if sg>0 else '- ',cap)


if __name__=='__main__':
    main()
