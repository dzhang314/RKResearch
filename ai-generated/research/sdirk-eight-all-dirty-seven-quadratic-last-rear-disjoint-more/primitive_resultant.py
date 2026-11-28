"""Exact ordinary resultant up to a nonzero rational scalar, over QQ[H]."""
from flint import fmpz_poly as P
def dense(F):
    groups={}
    for (i,j),z in F.to_dict().items():
        groups.setdefault(int(j),{})[int(i)]=int(z)
    rows=[]
    for j in range(max(groups)+1):
        cs=groups.get(j,{})
        row=[0]*(1+max(cs,default=-1))
        for i,v in cs.items():row[i]=v
        rows.append(P(row))
    return rows

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


def resultant(a,b):
    A,B=dense(a),dense(b)
    origA,origB=A,B
    atoms=Val()
    hist=[]
    while len(B)>1:
        m,n=len(A)-1,len(B)-1
        C,sc=pseudo(A,B)
        assert C
        r=len(C)-1
        hist.append((m,n,r,sc,B[-1]))
        A,B=B,C
    atoms.add(B[0],len(A)-1)
    for m,n,r,sc,head in reversed(hist):
        for y,c in sc:atoms.add(y,-n);atoms.add(c,n)
        atoms.add(head,m-r)
    assert all(k>0 for p,k in atoms.parts)
    R=P([1])
    for p,k in atoms.parts:R*=p**k
    scale=None;checks=0
    for h in range(1,30):
        x=P([a(h) for a in origA])
        y=P([a(h) for a in origB])
        if x.degree()!=len(origA)-1 or y.degree()!=len(origB)-1:continue
        s=x.resultant(y);t=R(h)
        if not t:
            assert not s
            continue
        assert s
        if scale is None:scale=(s,t)
        else:assert s*scale[1]==t*scale[0]
        checks+=1
        if checks==3:break
    assert checks==3
    return a.context().from_dict({(i,0):int(x) for i,x in enumerate(R.coeffs()) if x})
