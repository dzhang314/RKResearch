"""Scalar receipts for the proved donor-bank continuation. Does not construct or check higher physical matrices."""
from fractions import Fraction as Q
from math import prod

def hull(nodes):
    P=[Q(1)]
    for y in nodes:
        out=[Q(0)]*(len(P)+1)
        for k,a in enumerate(P):out[k]-=y*a;out[k+1]+=a
        P=out
    return P
def integ(P,j):return sum(v/(i+j+1) for i,v in enumerate(P))
def gate(known,p):
    H=hull(known);z=integ(H,1)/integ(H,0);xs=known+[z]
    assert len(xs)==p-1==len(set(xs))
    w=[integ(hull([x for x in xs if x!=y]),0)/prod(y-x for x in xs if x!=y) for y in xs]
    assert all(w) and all(sum(a*x**j for x,a in zip(xs,w))==Q(1,j+1) for j in range(p))
    defect=(p+1)*sum(a*x**p for x,a in zip(xs,w))-1;assert defect
    return z,defect
def main():
    bank=[Q(-9),Q(-11),Q(251647454237400205,337389807870474227)];s=26
    for p in range(13,20,2):
        q=(p-1)//2
        assert sum(x<0 for x in bank)>=2
        fresh=[-Q(100*p+2*j+1) for j in range(q-len(bank)-1)]
        pins=[Q(2-2*i) for i in reversed(range(1,q+1))]
        z,delta=gate(bank+fresh+pins,p)
        s+=p-1-len(bank)
        print(f'order {p}: old merges {len(bank)}, physical stages {s}, new protected clocks {fresh+[z]}, next-bush sign {(delta>0)-(delta<0)}')
        bank=fresh+[z]
if __name__=='__main__':main()
