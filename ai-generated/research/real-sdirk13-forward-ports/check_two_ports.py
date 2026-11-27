"""Standard-library exact interval receipt for the minimum 12-row, two-port forward bank."""
from fractions import Fraction
from functools import total_ordering

B=256
S=1<<B
def up(a,b):return -((-a)//b)
class I:
    """Both closed endpoints are stored as integer multiples of 2^-B."""
    __slots__=("lo","hi")
    def __init__(self,lo,hi):
        assert lo<=hi
        self.lo,self.hi=lo,hi
    @staticmethod
    def val(p):
        if isinstance(p,I):return p
        n=Fraction(p)*S
        return I(n.numerator//n.denominator,up(n.numerator,n.denominator))
    def __neg__(a):return I(-a.hi,-a.lo)
    def __add__(a,b):
        b=I.val(b);return I(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __sub__(a,b):return a+-I.val(b)
    def __rsub__(a,b):return I.val(b)+-a
    def __mul__(a,b):
        b=I.val(b);u=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return I(min(u)//S,up(max(u),S))
    __rmul__=__mul__
    def inv(a):
        assert a.sign()
        v=(-a if a.hi<0 else a)
        r=I(S*S//v.hi,up(S*S,v.lo))
        return -r if a.hi<0 else r
    def __truediv__(a,b):return a*I.val(b).inv()
    def __rtruediv__(a,b):return I.val(b)*a.inv()
    def __pow__(a,n):
        assert n>=0
        r=I.val(1)
        while n:
            if n&1:r=r*a
            a=a*a;n//=2
        return r
    def midpoint(a):return I((a.lo+a.hi)//2,(a.lo+a.hi)//2)
    def sign(a):return 1 if a.lo>0 else -1 if a.hi<0 else 0
    def sup(a):return max(abs(a.lo),abs(a.hi))
    def inf(a):return min(abs(a.lo),abs(a.hi)) if a.sign() else 0
def pow2_bound(s):
    return s.bit_length()-B
def around(c,d):
    c=I.val(c).midpoint();d=I.val(d).hi
    return c,I(c.lo-d,c.hi+d),d

def plus(p,q):
    return [(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0)for i in range(max(len(p),len(q)))]
def sc(z,p):return [z*x for x in p]
def T(p):return plus([I.val(0)]+[v/(j+1) for j,v in enumerate(p)],sc(-1,p))
def der(p):return [j*x for j,x in enumerate(p) if j]
def ev(p,x):
    a=I.val(0)
    for v in p[::-1]:a=a*x+v
    return a
def dot(a,b):
    assert len(a)==len(b)
    return sum((x*y for x,y in zip(a,b)),I.val(0))
def tr(A):return [list(v)for v in zip(*A)]
def det2(A):return A[0][0]*A[1][1]-A[0][1]*A[1][0]
def cross(a,b):
    return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]
def solve(A,B):
    n=len(A);m=len(B[0]);M=[list(a)+list(b)for a,b in zip(A,B)]
    assert len(B)==n and all(len(r)==n+m for r in M)
    for j in range(n):
        k=max(range(j,n),key=lambda i:M[i][j].inf())
        M[j],M[k]=M[k],M[j]
        iv=M[j][j].inv()
        M[j][j:]=[v*iv for v in M[j][j:]]
        M[j][j]=I.val(1)
        for i in range(n):
            if i!=j:
                s=M[i][j]
                M[i][j+1:]=[x-s*y for x,y in zip(M[i][j+1:],M[j][j+1:])]
                M[i][j]=I.val(0)
    return [r[n:]for r in M]

W=[[I.val(1)]]
for n in range(1,6):W.append(sc(n,T(W[-1])))
centers={
  1:["1"],
  2:["0.585786437626904951198311275790301921430328124623051926823320262009267521538",
     "3.41421356237309504880168872420969807856967187537694807317667973799073247846"],
  3:["0.415774556783479083311533873128274473546617412693118465093965954322325019937",
     "2.29428036027904171982205036135959386895986172106028083403520124808403045134",
     "6.28994508293747919686641576551213165749352086624660070087083279759364452873"],
  4:["1.74576110115834657568681671251794702367387451553107250178278266099845605744",
     "4.53662029692112798327928538495713788012578435338680464974805758755582845088"],
  5:["1.41340305910651679221840798018755774953909600438088028055440829790074237759"],
}
def sign_bracket(p,x):
    assert ev(p,I(x.lo,x.lo)).sign()*ev(p,I(x.hi,x.hi)).sign()==-1
    assert ev(der(p),x).sign()
def cert_roots():
    roots={}
    for n,cs in centers.items():
        roots[n]=[]
        for s in cs:
            if n==1:a=I.val(s)
            else:
                _,a,_=around(s,"1e-51");sign_bracket(W[n],a)
            assert not roots[n] or a.lo>roots[n][-1].hi
            roots[n].append(a)
    return roots
def cert_ports(R):
    a,b=R[4];h,=R[5]
    uv=solve([[ev(W[2],x),ev(W[3],x)]for x in [a,b]],[[-ev(W[1],x)]for x in [a,b]])
    Z=plus(W[1],plus(sc(uv[0][0],W[2]),sc(uv[1][0],W[3])))
    U=[W[5],plus(W[3],sc(-ev(W[3],h)/ev(W[4],h),W[4])),
        plus(Z,sc(-ev(Z,h)/ev(W[4],h),W[4]))]
    P=[T(u)for u in U]
    def equations(v,z):
        q0=ev(P[0],v);a0=ev(U[0],z)
        return [q0*ev(U[j],z)-ev(P[j],v)*a0 for j in (1,2)]
    def jac(v,z):
        q0=ev(P[0],v);a0=ev(U[0],z)
        dq=ev(der(P[0]),v);da=ev(der(U[0]),z)
        return [[dq*ev(U[j],z)-ev(der(P[j]),v)*a0,q0*ev(der(U[j]),z)-ev(P[j],v)*da]for j in (1,2)]
    v0,v,rad=around("7.10359430799318097040877091040912372606906514834155005869271834405344060149","1e-27")
    z0,z,rad2=around("0.331687244784675202032815644983006774876215103991165763648671162462251332319","1e-27")
    assert rad==rad2
    J=jac(v,z);assert det2(J).sign()
    P0=[[x.midpoint()for x in row]for row in jac(v0,z0)]
    inv=[[x.midpoint()for x in row]for row in solve(P0,[[I.val(1),I.val(0)],[I.val(0),I.val(1)]])]
    assert det2(inv).sign()
    norm=max(sum((I.val(i==j)-dot(inv[i],col)).sup()for j,col in enumerate(tr(J)))for i in range(2))
    disp=max(dot(row,equations(v0,z0)).sup()for row in inv)
    assert norm<S and disp*S+norm*rad<rad*S
    def E(x):return [ev(p,x)for p in U]
    ez,ey=E(z),E(v);assert ez[0].sign()
    eta=cross(ez,ey)
    if abs(eta[0].inf())>0: idx=(1,2)
    elif abs(eta[1].inf())>0: idx=(0,2)
    else:idx=(0,1)
    _,w,_=around("0.264100403162569895818384865488813079213405327485287908663368281563580616758","1e-19")
    assert 0<w.lo<w.hi<z.lo<z.hi<v.lo
    Q=plus(sc(eta[0],U[0]),plus(sc(eta[1],U[1]),sc(eta[2],U[2])))
    sign_bracket(T(Q),w)
    d=ev(Q,w);assert d.sign()
    lam=ev(P[0],v)/ez[0]
    mw=[ev(p,w)for p in P]
    k=solve([[ez[i],ey[i]]for i in idx],[[mw[i]]for i in idx])
    al,be=k[0][0],k[1][0]
    print("v,z strict contraction: norm < 2^%s, displacement < 2^%s" %
          (pow2_bound(norm),pow2_bound(disp)))
    print("w strict bracket; three evaluation determinant magnitude >= 2^%s" %
          (d.inf().bit_length()-1-B))
    return U,[z,v,w],(lam,al,be)
def eye(n,i):
    return [I.val(i==j)for j in range(n)]
def front_prep(R):
    A=[];Dmode=[]
    for n in range(1,6):
        prev=len(A);H=R[n];h=len(H);tot=prev+h
        zero=[I.val(0)]*h
        A=[r+zero for r in A]
        for i,x in enumerate(H):
            j=[dot([ev(W[k+1],x)/(k+1)for k in range(n-1)],col)
               for col in (tr(Dmode) if prev else [])]
            A.append(j+eye(h,i))
        L=n-h
        low=[r+zero for r in Dmode[:L]]
        rhs=[[u-dot([ev(W[k],x)for k in range(L)],col)
              for u,col in zip(eye(tot,prev+i),tr(low) if L else [[]for _ in range(tot)])]
             for i,x in enumerate(H)]
        hi=solve([[ev(W[k],x)for k in range(L,n)]for x in H],rhs)
        Dmode=low+hi
    E=[[dot([W[k][j] if j<len(W[k]) else I.val(0) for k in range(5)],r)
        for r in tr(Dmode)]for j in range(5)]
    return A,E
def actual_bank(R,U,sites,coef):
    A,D=front_prep(R);z,v,w=sites;lam,al,be=coef
    def dotD(x,T0=False):
        v=[x**j for j in range(5)]
        if T0:v=[x**(j+1)/(j+1)-a for j,a in enumerate(v)]
        return [dot(v,r)for r in tr(D)]
    EZ,EV,EW=map(dotD,sites);SZ,SV,SW=map(lambda x:dotD(x,True),sites)
    A=[r+[I.val(0)]*3 for r in A]
    A.append(SZ+[I.val(1),I.val(0),I.val(0)])
    A.append([v-lam*z for v,z in zip(SV,EZ)]+[lam,I.val(1),I.val(0)])
    A.append([w-al*z-be*v for w,z,v in zip(SW,EZ,EV)]+[al,be,I.val(1)])
    L=solve([[ev(p,x)for p in U]for x in sites],
            [[u-v for u,v in zip(eye(12,j),row+[I.val(0)]*3)]
             for j,row in zip((9,10,11),(EZ,EV,EW))])
    D.append([I.val(0)]*9)
    D=[[(D[k][j] if j<9 else I.val(0))+dot(
        [p[k] if k<len(p) else I.val(0)for p in U],col)for j,col in enumerate(tr(L))]
       for k in range(6)]
    return A,D
def rooted_checks(A,D,R,sites):
    C=[sum(row,I.val(0))for row in A]
    allsites=sum((R[k]for k in range(1,6)),[])+sites
    assert all(not (a-b).sign() for a,b in zip(C,allsites))
    assert all((row[i]-1).sup()==0 and all(x.sup()==0 for x in row[i+1:]) for i,row in enumerate(A))
    trees=[(1,[I.val(1)]*12)];max_err=0
    for n in range(2,8):
        old=tuple(trees)
        def rec(rem,start,fac):
            if rem==0:
                trees.append((n,fac));return
            for i in range(start,len(old)):
                k,t=old[i]
                if k<=rem:rec(rem-k,i,[x*(k*dot(row,t))for x,row in zip(fac,A)])
        rec(n-1,0,[I.val(1)]*12)
    for n,t in trees:
        for i in (10,11):
            e=t[i]-allsites[i]**(n-1)
            assert not e.sign();max_err=max(max_err,e.sup())
        if n<=6:
            for k,row in enumerate(D):
                e=dot(row,t)-I.val(k==n-1)
                assert not e.sign();max_err=max(max_err,e.sup())
    assert len(trees)==85
    print("85 rooted diagnostics at the actual 12 physical rows; worst enclosure < 2^%s" % pow2_bound(max_err))
if __name__=='__main__':
    R=cert_roots(); U,sites,coef=cert_ports(R); A,D=actual_bank(R,U,sites,coef); rooted_checks(A,D,R,sites)
