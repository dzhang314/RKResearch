"""Independent arithmetic audit of the literal five-extra-prime tableau."""
from fractions import Fraction as Q
from math import lcm
from pathlib import Path
import json

def verify(s):
    data=json.loads(Path(__file__).with_name("tableau.json").read_text())
    A=[[Q(z) for z in row] for row in data["A"]]; b=list(map(Q,data["b"]))
    c=list(map(Q,data["c"]))
    assert (data["stages"],data["order"])==(s,10) and len(A)==len(b)==s
    assert list(map(len,A))==list(range(1,s+1)) and list(map(sum,A))==c
    assert len({tuple(row+[0]*(s-len(row))) for row in A})==s
    assert len({row[i] for i,row in enumerate(A) if row[i]})>1
    D=lcm(*(z.denominator for r in A for z in r),*(z.denominator for z in b))
    assert D==14762353142762908220160000000
    assert D==2**14*3**7*5**7*7**2*47**3*83*97*199*647
    N=[tuple((i,int(D*z)) for i,z in enumerate(row) if z) for row in A]
    w=tuple(int(D*z) for z in b)
    a=tuple(sum(z for _,z in row) for row in N)
    def action(v):return tuple(sum(z*v[i] for i,z in row) for row in N)
    all_=[]
    counts=[]
    for n in range(1,11):
        layer=[]
        def gen(rem,start,v,factorial):
            if not rem:
                assert factorial*sum(x*y for x,y in zip(w,v))==D**n
                layer.append((n,factorial,action(v)))
                return
            for i in range(start,len(all_)):
                m,f,u=all_[i]
                if m>rem:break
                gen(rem-m,i,tuple(x*y for x,y in zip(v,u)),factorial*f)
        gen(n-1,0,(1,)*s,n)
        counts.append(len(layer)); all_.extend(layer)
    assert counts==[1,1,2,4,9,20,48,115,286,719]
    rs=Q(11*sum(z*x**10 for z,x in zip(w,a))-D**11,D**11)
    rm=Q(88*sum(z*x*x*y for z,x,y in zip(w,a,action([x**7 for x in a])))-D**11,D**11)
    assert rs==Q(-1207,5184000)==11*Q(data["eleventh_bush_defect"])
    assert rm==Q(2711,3888000)
    assert all(D**2%r.denominator==0 for r in (rs,rm))
    assert 1141*rs.numerator+508*rm.numerator==1
    print(s,"distinct lower triangular rows with unequal nonzero diagonals;",
      len(all_),"integer order checks",counts)
    print("D=",D,"; five extras 47,83,97,199,647; eleventh normalized defects",rs,rm)
    print("both cleared numerator exactness: 1141*(-1207) + 508*2711 = 1")
verify(12)
