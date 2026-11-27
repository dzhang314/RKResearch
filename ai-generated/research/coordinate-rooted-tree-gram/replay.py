"""Stdlib replay of the coordinate Gram recurrence, with independent plane trees.

Default: both quadratic unit controls. Pass the repository checkout (or the
original LaguerreGauss76Data.lean path) for the 29-coordinate archived witness.
No Lean code is executed or generated.
"""
from fractions import Fraction as Q
from itertools import product
from math import comb, factorial, lcm
from pathlib import Path
import re
import sys


def weight(bits, a, b):
    """Structure constant for e_a*e_b in the square-root product basis."""
    return mul_all(v for i,v in enumerate(bits) if (a&b)>>i&1)


def mul_all(seq):
    p=1
    for x in seq:p*=x
    return p


def mproduct(A,B):
    columns=list(zip(*B))
    return [[sum(x*y for x,y in zip(row,col) if x and y) for col in columns]
            for row in A]


def outer(v):
    return [[x*y for y in v] for x in v]


class Tableau:
    def __init__(self, bits, A, b, D=None):
        self.bits=bits
        self.r=1<<len(bits)
        self.s=len(b)
        self.n=self.s*self.r+1
        self.d=D if D is not None else lcm(*(x.denominator for row in A for z in row for x in z),
                                             *(x.denominator for z in b for x in z))
        assert self.d>0
        assert all((x*self.d).denominator==1 for row in A for z in row for x in z)
        assert all((x*self.d).denominator==1 for z in b for x in z)
        self.M=[[[int(self.d*x) for x in z] for z in row] for row in A]
        self.w=[[int(self.d*x) for x in z] for z in b]
        self.one=[1]+[0]*(self.r-1)
        self.support=[[(j,k,weight(bits,j,k)) for j,k in product(range(self.r),repeat=2)
                      if j^k==a] for a in range(self.r)]
        self.feature=[[ (s*self.r+i,s*self.r+j,c) for i,j,c in self.support[a]]
                      for s in range(self.s) for a in range(self.r)]+[[(self.n-1,self.n-1,1)]]

    def branch(self,k):
        B=[[0]*self.n for _ in range(self.n)]
        B[-1][-1]=self.d
        for i,j in product(range(self.s),repeat=2):
            for a,h in product(range(self.r),repeat=2):
                B[i*self.r+a][j*self.r+h]=k*self.M[i][j][a^h]*weight(self.bits,a^h,h)
        return B

    def output(self,k):
        O=[[0]*self.n for _ in range(self.r)]
        O[0][-1]=-self.d
        for j,a,h in product(range(self.s),range(self.r),range(self.r)):
            O[a][j*self.r+h]=k*self.w[j][a^h]*weight(self.bits,a^h,h)
        return O

    def tensor(self,V,W):
        return [[sum(a*b*V[i][k]*W[j][l] for i,j,a in f for k,l,b in g)
                 for g in self.feature] for f in self.feature]

    def gram(self,p):
        C=[outer(self.one*self.s+[1])]
        for n in range(1,p):
            G=[[0]*self.n for _ in range(self.n)]
            for k in range(1,n+1):
                B=self.branch(k)
                W=mproduct(mproduct(B,C[k-1]),list(zip(*B)))
                T=self.tensor(C[n-k],W); a=comb(n,k)**2
                for r,s in product(range(self.n),repeat=2):G[r][s]+=a*T[r][s]
            C.append(G)
        out=[]
        for n,G in enumerate(C,1):
            O=self.output(n)
            H=mproduct(mproduct(O,G),list(zip(*O)))
            out.append(sum(H[i][i] for i in range(self.r)))
        return out

    def mul(self,v,w):
        return [sum(c*v[i]*w[j] for i,j,c in row) for row in self.support]

    def add(self,vectors):
        return [sum(xs) for xs in zip(*vectors)]

    def direct(self,p):
        # Independent plane-tree evaluation: use raw Butcher weights and
        # tree factorials, not the coordinate covariance or its join rule.
        B=[[ (self.one,)*self.s ]]
        F=[[1]]
        for n in range(2,p+1):
            rs=[];fs=[]
            for k in range(1,n):
                for y,g in zip(B[k-1],F[k-1]):
                    z=[self.add(self.mul(v,w) for v,w in zip(a,y)) for a in self.M]
                    for x,h in zip(B[n-k-1],F[n-k-1]):
                        rs.append([self.mul(i,j) for i,j in zip(x,z)])
                        fs.append(n*h*g//(n-k))
                        assert n*h*g%(n-k)==0
            B.append(rs);F.append(fs)
        ans=[]
        for n in range(1,p+1):
            energy=0
            for state,t in zip(B[n-1],F[n-1]):
                r=self.add(self.mul(w,x) for w,x in zip(self.w,state))
                q=factorial(n)//t
                assert factorial(n)%t==0
                residual=[q*(t*a-self.d**n*b) for a,b in zip(r,self.one)]
                energy+=sum(v*v for v in residual)
            ans.append(energy)
        return ans


def controls():
    G=Tableau((3,),[[[Q(1,4),Q(0)],[Q(1,4),Q(-1,6)]],
                    [[Q(1,4),Q(1,6)],[Q(1,4),Q(0)]]],[[Q(1,2),Q(0)]]*2,12)
    I=Tableau((-1,),[[[Q(0),Q(0)]]*2,[[Q(2,3),Q(1,3)],[Q(0),Q(0)]]],
                     [[Q(2,5),Q(3,10)],[Q(3,5),Q(-3,10)]],30)
    for label,X,p,result in (
        ("Gauss",G,5,[0,0,0,0,116955021312]),
        ("Complex",I,3,[0,0,1458000000])
    ):
        assert X.gram(p)==X.direct(p)==result
        print(f"{label}, dimension {X.n}, scale {X.d}: {result}")


def archived(path):
    if path.is_dir():
        path=path/"ai-generated/lean/RKCert/ReviewedNative/LaguerreGauss76Data.lean"
    text=path.read_text()
    assert "def gamma : Coeff := coeff (1/2) 0 0 0" in text
    A=[[[Q(int(i==j),2),Q(0),Q(0),Q(0)] for j in range(7)] for i in range(7)]
    seen=set()
    for i,j,z in re.findall(r"^\s*\| (\d+), (\d+) => coeff (.+)$",text,re.M):
        i,j=int(i),int(j)
        assert 0<=j<i<7 and (i,j) not in seen
        coeff=[Q(a.strip("()")) for a in z.split()]
        assert len(coeff)==4
        A[i][j]=coeff;seen.add((i,j))
    assert len(seen)==17
    assert "| 4 | 5 => coeff (5/18) 0 0 0" in text
    assert "| 6 => coeff (4/9) 0 0 0" in text
    b=[[w,Q(0),Q(0),Q(0)] for w in [Q(0)]*4+[Q(5,18),Q(5,18),Q(4,9)]]
    X=Tableau((2,15),A,b)
    T=X.gram(7)
    assert T==X.direct(7) and T[:6]==[0]*6 and T[6]>0
    print(f"LaguerreGauss76 (archived 7-stage order 6), dimension {X.n}, scale {X.d}:")
    print(T)


if __name__=="__main__":
    controls()
    if len(sys.argv)>1:archived(Path(sys.argv[1]))
