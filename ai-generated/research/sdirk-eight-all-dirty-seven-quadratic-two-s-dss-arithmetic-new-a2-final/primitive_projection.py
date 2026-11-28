"""Exact swapped resultant up to nonzero rational scalar, via primitive one-step PRS."""
from flint import fmpz_poly as P
from ingress import ingress
def dense(F):
    d={}
    for (h,z,v),a in F.to_dict().items():
        assert not v
        r=d.setdefault(int(h),{})
        r[int(z)]=int(a)
    dd=[]
    for h in range(max(d)+1):
        row=d.get(h,{})
        if not row:dd.append(P());continue
        zz=[0]*(1+max(row))
        for i,v in row.items():zz[i]=v
        dd.append(P(zz))
    return dd
def trim(z):
    while z and not z[-1]:z.pop()
    return z
from time import monotonic

def prim(f):
    if f.degree()<1:return P([1])
    f=f//P([int(f.content())])
    return f if f.leading_coefficient()>0 else -f

class Val:
    def __init__(self):self.parts=[]
    def one_sf(self,q,n):
        z=q
        if not n or z.degree()<1:return
        out=[]
        for p,k in self.parts:
            g=prim(p.gcd(z))
            if g.degree()>0:
                rem=prim(p//g)
                if rem.degree()>0:out.append((rem,k))
                if k+n:out.append((g,k+n))
                z=prim(z//g)
            else:out.append((p,k))
        if z.degree()>0:out.append((z,n))
        self.parts=out
    def add(self,q,k):
        if not k or q.degree()<=0:return
        if len(self.parts)<=2:
            for i,(p,n) in enumerate(self.parts):
                if p==prim(q):
                    self.parts.pop(i)
                    if n+k:self.parts.append((p,n+k))
                    return
        for p,m in prim(q).factor_squarefree()[1]:
            self.one_sf(prim(p),m*k)

def pseudo(A,B):
    d=len(B)-1;head=B[-1];rr=[]
    while len(A)>d:
        n=len(A)-1;z=A[-1];g=z.gcd(head)
        x,y=z//g,head//g
        C=[a*y for a in A[:-1]]
        for j in range(d):C[n-d+j]-=x*B[j]
        trim(C)
        if not C:return C,rr
        c=P()
        for z in reversed(C):
            c=c.gcd(z)
            if c.degree()==0 and abs(c[0])==1:break
        if c.degree()>0 or abs(c[0])!=1:C=[z//c for z in C]
        if y.degree()>0 or c.degree()>0:rr.append((y,c))
        A=C
    return A,rr

def exact_projection(rows,guard,Q,named=None):
    A=dense(Q);B=dense(rows[0]);atoms=Val();t=monotonic()
    origA,origB=A[:],B[:]
    hist=[]
    while len(B)>1:
        m,n=len(A)-1,len(B)-1
        C,sc=pseudo(A,B)
        assert C
        r=len(C)-1
        hist.append((m,n,r,[(y,c) for y,c in sc],B[-1]))
        print('completed step H degrees',m,n,r,'max d degree',max(z.degree() for z in C),
              'elapsed',monotonic()-t,flush=True)
        A,B=B,C
    print('process exact valuation cancellations',flush=True)
    atoms.add(B[0],len(A)-1)
    for m,n,r,sc,head in reversed(hist):
        for y,c in sc:atoms.add(y,-n);atoms.add(c,n)
        atoms.add(head,m-r)
        print('valuation step',m,n,r,'degrees and powers',[(p.degree(),k) for p,k in atoms.parts],
              'elapsed',monotonic()-t,flush=True)
    assert all(k>0 for p,k in atoms.parts)
    assert sum(p.degree()*k for p,k in atoms.parts)==3066
    # Cross-check the tracked valuation polynomial against direct ordinary
    # integer resultants at several degree-preserving integer specializations.
    scale=None;checks=0
    for j in (3,4,5,7,11,13,17,19):
        AA=P([f(j) for f in origA]);BB=P([f(j) for f in origB])
        if AA.degree()!=84 or BB.degree()!=18:continue
        val=P([1])[0]
        for q,e in atoms.parts:val*=q(j)**e
        r0=AA.resultant(BB)
        if not val:
            assert not r0
            continue
        assert r0
        if scale is None:scale=r0,val
        else:assert r0*scale[1]==scale[0]*val
        checks+=1
        if checks==3:break
    assert checks==3
    dguards=[dense(z)[0] for z in guard if not z.degrees()[0] and not z.degrees()[2]]
    fcts=[]
    for p,k in atoms.parts:
        for g in dguards:p=prim(p//p.gcd(g))
        if p.degree()>0:
            print('factor final coprime block degree',p.degree(),k,flush=True)
            for z,n in p.factor()[1]:
                fcts.append((list(map(int,z.coeffs())),n*k))
                print('A2 projected d irreducible degree',z.degree(),n*k,flush=True)
    expect=[(1,192),(3,30),(3,60),(4,1),(8,3),(8,16),
            (16,3),(24,3),(36,8),(48,3),(134,1),(356,1)]
    assert sorted((len(p)-1,k) for p,k in fcts)==expect
    assert sum((len(p)-1)*k for p,k in fcts)==1660
    print('final d-factor table' ,[(len(p)-1,k) for p,k in fcts],flush=True)
    return fcts
if __name__=='__main__':exact_projection(*ingress())
