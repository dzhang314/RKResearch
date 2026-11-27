"""Coefficient-domain gamma projection from one literal extra zero."""
from variable_atlas import *
JJ,G=ring("g",K)
W,w,g=ring("z g",K)
Lf=lambda X:70*X**4-140*X**3+90*X*X-20*X+1
def toW(p):
 return W.from_dict({(i,0):v for (i,),v in p.items()})
def mon(p):return p.monic()
def defs(front):
 a,b,ha,hb,sg,L,A,B,C,D=phases(front)
 assert L.gcd(B).degree()==0
 print('fifth h numerator degree',(-A%L).degree(),(-A%L).as_expr(),'B', (B%L).as_expr(),flush=True)
 l=toW(L)
 n=toW(B)*((b-a)*ha*hb)*Lf(g*w)+toW(A)*((b-w)*hb*Lf(g*a)+(w-a)*ha*Lf(g*b))
 n=n%l
 if not n:raise ArithmeticError('gamma identity at s fiber')
 F=JJ(l.resultant(n))
 F=F.exquo(F.gcd(G**20))
 F=F.exquo(F.gcd(F.diff(G))).monic()
 # Initial line Q at physical X, scaled by (b-a)ha hb.
 Q0=JJ.from_dict({(i,):v for (i,),v in (b*hb*Lf(G*a)-a*ha*Lf(G*b)).items()})*G
 Q1=ha*Lf(G*b)-hb*Lf(G*a)
 Qres=70*Q0**4+140*Q0**3*Q1+90*Q0**2*Q1**2+20*Q0*Q1**3+Q1**4
 print(front,'gamma approx deg',F.degree(),'constant',F.gcd(Q1).degree(),'shared',F.gcd(Qres).degree(),'Gauss',F.gcd(Lf(G)).degree(),flush=True)
 factors=F.factor_list()[1]
 assert [(x.degree(),m) for x,m in factors]==[(4 if front else 12,1)]
 assert F.gcd(Q1*Qres*Lf(G)).degree()==0
 print('gamma factors',[(x.degree(),m) for x,m in factors],flush=True)
 return F,Q0,Q1,Qres,L,A,B
if __name__=='__main__':
 for q in (True,False):defs(q)
