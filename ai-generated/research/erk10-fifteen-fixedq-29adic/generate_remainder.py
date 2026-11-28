#!/usr/bin/env python3
"""Untrusted normalized coordinates for the exact guarded fixed-q chart."""
from argparse import ArgumentParser
from fractions import Fraction as F
from math import lcm
from pathlib import Path
import sys
import sympy as S

P_LIST=[8840760201800,-253467892079060,3137934176909504,-22147907712268517,99189988063653812,-295624157281470449,595327896073372740,-801391965499578390,691140376781707950,-345177595434956400,75851682979590000]
W=[2082753,9449717,-11271304,16002320,-17283646,13510082,-7394032,2687864,-583435,57281]
D=7257600
ns='RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear'

def certificate(out,remainder=False):
 x=S.Symbol('x')
 P=sum(a*x**i for i,a in enumerate(P_LIST))
 K=S.QQ.algebraic_field(S.CRootOf(P,0))
 c=K.unit;one=K.one;zero=K.zero;k=K.convert
 g,R,d=map(k,(6,15,26))
 I=lambda fn:sum((k(w)*fn(k(i)) for i,w in enumerate(W)),zero)/k(D)
 info={}
 budgets={}
 def save(name,q):
    cs=[F(int(v.numerator),int(v.denominator)) for v in reversed(q.to_list())]
    den=lcm(*(v.denominator for v in cs))
    num=[int(v*den) for v in cs]
    assert den%29 and len(num)<=10
    info[name]=num,den
    return q
 def pay(name,output,refs,degree):
    ps=[info[r][1] if r!='avg' else D for r in refs.split()]
    dd=lcm(*ps)
    assert dd%29
    budgets[name]=dd,9*degree+3,output
 HN=6686-22450*c+21150*c**2;HD=8980-31725*c+32120*c**2
 FN=1051235*c-4965464*c**2+5011025*c**3
 FD=2102470-14896392*c+42748688*c**2-61086000*c**3+36040380*c**4
 h=save('H',HN/HD);f=save('F',FN/FD)
 om=210*c**3-336*c*c+168*c-28
 e=save('E',c*(c-d)/(c+c*om*d))
 pay('H','Zero','H',3);pay('F','Zero','F',5);pay('E','Zero','E',5)
 T3=lambda y:(y-f)*(y-g)*(y-h)
 kc=save('K',I(lambda y:y*(y-one)*(y-c)**2*(y-R)*T3(y)))
 qc=save('QC',e*d*kc)
 B=lambda y:(y-c)*(y-d)*(y-e)*T3(y)
 E0=save('E0',I(lambda y:y*(y-one)*B(y)));E1=save('E1',I(lambda y:y*y*(y-one)*B(y)))
 v=[75*c**3-108*c*c+45*c-5, -3*(175*c**3-244*c*c+97*c-10), 3*(350*c**3-476*c*c+183*c-18), -15*(42*c**3-56*c*c+21*c-2)]
 V=lambda y:sum((a*y**i for i,a in enumerate(v)),zero)
 beta=save('Beta',V(zero)/T3(zero))
 Phi=lambda y:(y-one)*(y-c)*(y-d)*(y-e)*(V(y)-beta*T3(y))
 uu=save('UU',-I(lambda y:y*Phi(y)));vv=save('VV',I(Phi));ww=save('WW',I(lambda y:y*y*Phi(y)))
 u=save('U',E0*R*c*c-2*qc*c)
 v1=save('V',-E0*R*c-E0*c*c+E1*c+2*qc+qc*c)
 w=save('W',-E1*R*c*c+qc*c*c)
 delta=save('Det',u*vv-v1*uu)
 s=save('S',(v1*ww-w*vv)/delta);q=save('Q',(w*uu-u*ww)/delta)
 for name,refs,n in [('K','F H avg',5),('QC','E K',2),('E0','E F H avg',5),('E1','E F H avg',5),
      ('Beta','Beta F H',3),('UU','E F H Beta avg',6),('VV','E F H Beta avg',6),('WW','E F H Beta avg',6),
      ('U','E0 QC',3),('V','E0 E1 QC',3),('W','E1 QC',3),('Det','U V UU VV',2),
      ('S','S Det V WW W VV',2),('Q','Q Det W UU U WW',2)]:
    pay(name,'Zero' if name in {'Beta','S','Q'} else name,refs,n)
 y=S.Symbol('y'); KR=K.poly_ring(y);Y=KR.gens[0];cc=KR.ring.ground_new
 D7=(Y*Y-cc(s)*Y+cc(q))*(Y-cc(d))*(Y-cc(e))*(Y-cc(f))*(Y-cc(g))*(Y-cc(h))
 head_end=len(info)
 for i in range(8):
    name=f'D{i}';save(name,D7.get((i,),zero));pay(name,name,'E F H S Q',4)
 p3=lambda y:y*(y-one)*(y-c)
 mp=[save(f'M{i}',I(lambda y,i=i:p3(y)*y**i)) for i in range(7)]
 for i in range(7):pay(f'M{i}',f'M{i}','avg',2)
 mu=[]
 for i in range(7):
    name=f'Mu{i}'
    mu.append(save(name,sum((D7.get((j,),zero)*mp[j-1-i] for j in range(i+1,8)),zero)))
    pay(name,name,' '.join([f'D{j}' for j in range(i+1,8)]+[f'M{j-1-i}' for j in range(i+1,8)]),2)
 ev=lambda a,y:sum((b*y**i for i,b in enumerate(a)),zero)
 Cnu=save('CNu',(one-R)*V(R));pay('CNu','CNu','',3)
 phase=[]
 for name,z,root in [('PhaseF',f,'F'),('PhaseG',g,''),('PhaseH',h,'H')]:
    phase.append(save(name,-ev(mu,z)*V(z)/(z*Cnu)))
    pay(name,'Zero',' '.join([root,'CNu',name]+[f'Mu{i}' for i in range(7)]),14)
 assert (phase[2]-phase[0])*(g-f)==(phase[1]-phase[0])*(h-f)
 pay('Aligned','Zero','PhaseF PhaseG PhaseH F H',2)
 def module(name,base,lines):
    (out/(name+'.lean')).write_text(
      'module\n\npublic import RKCert.ReviewedNative.'+base+
      '\n\n@[expose] public section\n\nnamespace '+ns+
      '\nopen Packed\n\n'+'\n'.join(lines)+'\n\nend '+ns+'\n')
 def lean_int(n):return str(n) if n>=0 else f'({n})'
 def rep(name,data):
    a,b=data
    return f'def rep{name} : Rep := ⟨[{", ".join(map(lean_int,a))}], {b}⟩'
 entries=list(info.items())
 lines=[rep('Zero',([],1))]+[rep(name,data) for name,data in entries[:head_end]]
 lines+=['']
 head_budgets=list(budgets.items())[:head_end]
 lines += [f'abbrev den{name} : ℕ := {den}\nabbrev digits{name} : ℕ := {cnt}' for name,(den,cnt,_) in head_budgets]
 module('ERK10FixedQ29AdicHeadData','ERK10FixedQ29AdicPacked',lines)
 lines=[rep(name,data) for name,data in entries[head_end:]]+['']
 lines += [f'abbrev den{name} : ℕ := {den}\nabbrev digits{name} : ℕ := {cnt}' for name,(den,cnt,_) in list(budgets.items())[head_end:]]
 module('ERK10FixedQ29AdicPhaseData','ERK10FixedQ29AdicHeadData',lines)
 if remainder:
    M=sum((cc(q)*Y**i for i,q in enumerate(mu)),KR.zero)
    VP=sum((cc(q)*Y**i for i,q in enumerate(v)),KR.zero)
    T4=(Y-cc(R))*(Y-cc(f))*(Y-cc(g))*(Y-cc(h))
    gap=g-f
    q1n=cc(gap*phase[0])+cc(phase[1]-phase[0])*(Y-cc(f))
    U0=(Y-1)*VP/cc(Cnu)
    E=(M*U0-Y*(1-Y)*q1n/cc(gap))%D7
    B=M*T4%D7
    sigma=-E[(0,)]/B[(0,)]
    gamma=save('Gamma',gap*Cnu*sigma)
    lhs=M*(cc(gap)*(Y-1)*VP+cc(gamma)*T4)-cc(Cnu)*Y*(1-Y)*q1n
    quo,rem=lhs.div(D7)
    assert not rem and quo.degree()<=3
    for i in range(4):
       save(f'Quot{i}',quo.get((i,),zero))
    den=lcm(*(info[n][1]for n in ['Gamma','F','H','PhaseF','PhaseG','CNu']
         +[f'D{i}'for i in range(8)]+[f'Mu{i}'for i in range(7)]+[f'Quot{i}'for i in range(4)]))
    assert den%29
    l=[rep(n,info[n])for n in ['Gamma']+[f'Quot{i}'for i in range(4)]]
    l+=[f'abbrev denRemainder : ℕ := {den}', 'abbrev digitsRemainder : ℕ := 57']
    module('ERK10FixedQ29AdicRemainderData','ERK10FixedQ29AdicPhaseData',l)
    def r29(v):
       vals=[F(int(q.numerator),int(q.denominator)) for q in reversed(v.to_list())]
       return sum(q.numerator*pow(q.denominator,-1,29)*2**i for i,q in enumerate(vals))%29
    qb,remb=(M*T4).div(D7)
    assert r29(remb[(0,)])==4 and r29(sigma)==3
    print('Remainder gamma',r29(gamma),'sigma',r29(sigma),'quotient', [r29(quo.get((i,),zero)) for i in range(4)])
    print('B quotient mod29',[r29(qb.get((i,),zero))for i in range(4)],
        'B mod29',[r29(remb.get((i,),zero))for i in range(7)])
 for name,(a,d) in entries:
    residue=sum(n*2**i for i,n in enumerate(a))*pow(d,-1,29)%29
    print(name, 'residue', residue, 'digits',len(str(d)))
 print('All coordinate denominators are 29-units. Generated',len(entries),'normalized scalars and',len(budgets),'exact checks.')
 return budgets

if __name__=='__main__':
 p=ArgumentParser()
 p.add_argument('--emit',type=Path,required=True)
 p.add_argument('--remainder',action='store_true')
 q=p.parse_args()
 certificate(q.emit,q.remainder)
