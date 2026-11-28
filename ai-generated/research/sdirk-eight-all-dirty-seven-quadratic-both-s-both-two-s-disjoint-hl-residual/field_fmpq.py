"""Exact Euclidean fibre arithmetic, using FLINT Q[H]/(f) coefficients."""
from flint import fmpq_poly
class Field:
    def __init__(self,minpoly):
        d=minpoly.total_degree()
        assert minpoly.degrees()==(d,0,0) and d>0
        raw=minpoly.to_dict()
        U=fmpq_poly([int(raw.get((i,0,0),0)) for i in range(d+1)])
        self.f=U/U.leading_coefficient()
        self.zero=fmpq_poly()
        self.one=fmpq_poly([1])
    def inv(self,z):
        g,s,t=z.xgcd(self.f)
        assert g.is_one()
        return s
    def from_data(self,raw,n):
        co=[0]*(n+1)
        for l,v in raw.items():co[l]=int(v)
        return fmpq_poly(co)%self.f
    def trans(self,P,var=1,values=None):
        # Interpret a polynomial in var, H occupying the coefficient field.
        # At most one other coordinate may be specialized to a field value.
        h=P.degrees()[0]
        if values is None:
            raw=[{} for _ in range(P.degrees()[var]+1)]
            for t,c in P.to_dict().items():
                assert t[3-var]==0
                raw[t[var]][t[0]]=int(c)
            return self.trim([self.from_data(u,h) for u in raw])
        j,z=values
        assert j+var==3
        pows=[self.one]
        for i in range(P.degrees()[j]):pows.append((pows[-1]*z)%self.f)
        raw=[[{} for _ in pows] for _ in range(P.degrees()[var]+1)]
        for t,c in P.to_dict().items():raw[t[var]][t[j]][t[0]]=int(c)
        out=[]
        for items in raw:
            q=self.zero
            for i,u in enumerate(items):
                if u:q=(q+pows[i]*self.from_data(u,h))%self.f
            out.append(q)
        return self.trim(out)
    @staticmethod
    def trim(a):
        while a and not a[-1]:a.pop()
        return a
    def monic(self,a):
        if not a or a[-1].is_one():return a
        z=self.inv(a[-1])
        return [(c*z)%self.f for c in a]
    def divrem(self,a,b):
        assert b
        if len(a)<len(b):return [],a
        v=self.one if b[-1].is_one() else self.inv(b[-1])
        a=a.copy()
        q=[self.zero]*max(0,len(a)-len(b)+1)
        while a and len(a)>=len(b):
            j=len(a)-len(b);w=(v*a.pop())%self.f
            q[j]=w
            for i,c in enumerate(b[:-1]):
                a[i+j]=(a[i+j]-c*w)%self.f
            self.trim(a)
        return self.trim(q),a
    def gcd(self,a,b):
        if not a:return self.monic(b)
        if not b:return self.monic(a)
        while b:
            a,b=b,self.divrem(a,b)[1]
        return self.monic(a)
    def joint(self,rows):
        g=[]
        for e in sorted((e for e in rows if e),key=len):
            g=self.gcd(g,e)
            if len(g)==1:break
        return g
    def discard(self,base,mask):
        assert base
        if not mask:return [self.one]
        while len(z:=self.gcd(base,mask))>1:
            base,r=self.divrem(base,z)
            assert not r
        return base
