"""Try exact finite-field literal construction for every fully distinct residue survivor.

This is a separate F29 existence experiment, not a lifting or necessity test
for rational stages with coefficient poles. stdin is census29 --regular.
Pass the path of the fixed-q spectrum directory as first CLI argument.
"""
import sys
import json
from collections import Counter
from fractions import Fraction

sys.path.insert(0,sys.argv[1])
import spectrum
import literal

class FP:
    __slots__=("v",)
    p=29
    def __init__(self,x=0,y=1):
        if isinstance(x,FP):
            x=x.v
        if isinstance(x,Fraction):
            x=x.numerator*pow(x.denominator,-1,29)
        if isinstance(y,FP): y=y.v
        self.v=int(x)*pow(int(y),-1,29)%29 if int(y)==1 or int(y)%29 else self.bad()
    @staticmethod
    def bad():
        raise ZeroDivisionError("nonunit denominator")
    def __add__(self,o): return FP(self.v+FP(o).v)
    __radd__=__add__
    def __sub__(self,o): return FP(self.v-FP(o).v)
    def __rsub__(self,o): return FP(FP(o).v-self.v)
    def __mul__(self,o): return FP(self.v*FP(o).v)
    __rmul__=__mul__
    def __truediv__(self,o): return FP(self.v,FP(o).v)
    def __rtruediv__(self,o): return FP(FP(o).v,self.v)
    def __pow__(self,n): return FP(pow(self.v,n,29))
    def __neg__(self): return FP(-self.v)
    def __eq__(self,o): return self.v==FP(o).v
    def __hash__(self): return hash(self.v)
    def __bool__(self): return bool(self.v)
    def __int__(self): return self.v
    def __str__(self): return str(self.v)
    __repr__=__str__
F=FP
spectrum.F=literal.F=F

def jpack(A,w,clocks):
    return dict(field=29, A=[[int(x) for x in row]for row in A],
                b=list(map(int,w)), c=list(map(int,clocks)))

def main():
    counts=Counter()
    seen=set()
    witness=None
    for line in sys.stdin:
        if witness is not None and "--first" in sys.argv: continue
        if not line.startswith("CANDIDATE "): continue
        raw=list(map(int,line.split()[1:]))
        if tuple(raw) in seen: continue
        seen.add(tuple(raw)); counts["distinct_projective_spectrum"]+=1
        ci,gi,ri,hi,fi,t,amin,amax,dmin,dmax,ge,ori,rr=raw
        for a,b in [(amin,amax),(amax,amin)]:
            for d,e in [(dmin,dmax),(dmax,dmin)]:
                for origin in (False,True):
                    if (origin and not ori) or (not origin and not ge):continue
                    counts["ordered_branch_trials"]+=1
                    ce,gg,RR,dd,aa,bb=map(F,[ci,gi,ri,d,a,b])
                    try:
                        im=spectrum.late(ce,dd,gg,RR)
                        if tuple(map(int,im[:3]))!=(e,fi,hi):
                            raise ArithmeticError("late reconstruction disagreement")
                        s=spectrum.head(ce,dd,gg,RR,aa,bb,im,origin)
                        counts["head_success"]+=1
                        z=spectrum.nonlinear(s)
                        counts["nonlinear_success"]+=1
                        A,w,clocks=literal.full(s,z,F(1,8))
                        counts["literal_built"]+=1
                        err,ct=literal.rooted(A,clocks,w,10)
                        assert sum(ct.values())==1205
                        if err is not None:
                            print("unexpected rooted failure",raw,err,flush=True)
                            continue
                        counts["literal_order_ten"]+=1
                        if witness is None:
                            wx,_=literal.rooted(A,clocks,w,11)
                            witness=jpack(A,w,clocks)
                            witness.update(dict(spectrum=list(map(int,z["ys"])),
                                                A1zero=origin, defect=list(map(int,wx)) if wx else None))
                            if len(sys.argv)>2:
                                with open(sys.argv[2],"w") as f: json.dump(witness,f,indent=2)
                            print("first literal",row_description(witness),flush=True)
                    except spectrum.Reject as ex: counts["reject_"+str(ex)]+=1
                    except ZeroDivisionError: counts["reject_nonunit"]+=1
    for k,n in sorted(counts.items()): print(k,n)

def row_description(w):
    return "reverse clocks "+str(w["spectrum"])+" defect "+str(w["defect"])

if __name__=="__main__":main()
