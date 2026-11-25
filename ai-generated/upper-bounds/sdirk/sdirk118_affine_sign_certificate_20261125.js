// Fixed SDIRK(11,8) scalar existence: standalone Node.js, exact BigInt intervals.
// Checks fixed rational seed/node brackets and only the two calibration endpoints.
// No root search, approximate seed output, calibrated d, tableau, or tree replay.

// Interval represented by integer outward endpoints divided by K.
const K=1n<<64n;
const floor=(a,b)=>b<0n?floor(-a,-b):a>=0n?a/b:-((-a+b-1n)/b);
const ceil=(a,b)=>-floor(-a,b);
const rat=(a,b=1n)=>[floor(BigInt(a)*K,BigInt(b)),ceil(BigInt(a)*K,BigInt(b))];
const take=(lo,hi)=>[lo[0],hi[1]];
const plus=([a,b],[c,d])=>[a+c,b+d];
const minus=([a,b],[c,d])=>[a-d,b-c];
const mul=([a,b],[c,d])=>{
 const xs=[a*c,a*d,b*c,b*d];
 return [floor(xs.reduce((x,y)=>x<y?x:y),K),ceil(xs.reduce((x,y)=>x>y?x:y),K)];
};
const div=([a,b],[c,d])=>{
 if(c<=0n&&d>=0n)throw Error("zero interval divisor");
 const ls=[floor(a*K,c),floor(a*K,d),floor(b*K,c),floor(b*K,d)];
 const hs=[ceil(a*K,c),ceil(a*K,d),ceil(b*K,c),ceil(b*K,d)];
 return [ls.reduce((x,y)=>x<y?x:y),hs.reduce((x,y)=>x>y?x:y)];
};
const sc=(x,c,k=1n)=>mul(x,rat(c,k));
const sq=x=>mul(x,x);
const zero=rat(0),one=rat(1);
const sign=([l,h])=>l>0n?1:h<0n?-1:0;
function prod(A,B){
 const C=Array.from({length:A.length+B.length-1},()=>zero);
 for(let i=0;i<A.length;i++)for(let j=0;j<B.length;j++)C[i+j]=plus(C[i+j],mul(A[i],B[j]));
 return C;
}
function roots(xs){return xs.reduce((P,x)=>prod(P,[minus(zero,x),one]),[one]);}
function get(P,k){return P[k]??zero;}
function subPoly(P,Q){return Array.from({length:Math.max(P.length,Q.length)},(_,k)=>minus(get(P,k),get(Q,k)));}
function exactNormAvg(z,P,j){
 let out=zero,p=one;
 for(let k=0;k<j;k++)p=mul(p,z);
 for(let k=0;k<P.length;k++){out=plus(out,div(mul(P[k],p),rat(k+j+1)));p=mul(p,z);}
 return out;
}
const Fs=(x)=>minus(mul(x,plus(mul(x,minus(x,rat(9))),rat(18))),rat(6));
const qs=(s,t)=>plus(minus(sq(t),sc(t,3)),mul(minus(one,t),s));
function polys(s,t){
 const a=sc(plus(one,s),1,2),z=plus(a,s);
 const Z=roots([one,a,s,t]);
 const mu=Array.from({length:4},(_,j)=>exactNormAvg(z,Z,j));
 const D=minus(mul(mu[0],mu[2]),sq(mu[1]));
 const n1=minus(mul(mu[1],mu[2]),mul(mu[0],mu[3]));
 const n0=minus(mul(mu[1],mu[3]),sq(mu[2]));
 const NB=x=>plus(plus(mul(D,sq(x)),mul(n1,x)),n0);
 return {a,z,D,NB};
}
function response(s,t,c,a,z,d){
 const r=sc(s,1,3),Bs=mul(minus(one,s),minus(rat(3),s));
 const eta=div(plus(rat(3),s),sc(minus(rat(3),s),4));
 const L=minus(mul(minus(Bs,one),minus(d,one)),
   mul(eta,minus(plus(d,one),sc(s,2))));
 const M=minus(mul(eta,Bs),sc(minus(minus(Bs,one),eta),3));
 const J=roots([s,t,one]);
 const IJ=[zero,...J.map((p,i)=>div(p,rat(i+1)))];
 const U=prod(roots([a,c]),subPoly(IJ,J));
 const ell0=exactNormAvg(z,U,0),ell1=exactNormAvg(z,U,1);
 const j=x=>mul(plus(minus(x,z),c),minus(mul(ell0,minus(z,x)),ell1));
 const i1=div(j(one),minus(one,r)),ia=div(j(a),minus(a,r));
 const ij=div(minus(mul(minus(d,a),i1),mul(minus(d,one),ia)),minus(one,a));
 const affine=minus(div(mul(L,j(r)),mul(minus(one,r),minus(a,r))),sc(mul(M,ij),1,3));
 // Independent divided-difference cross-check: the direct cleared response.
 const h=x=>mul(mul(minus(x,s),plus(minus(x,z),c)),minus(mul(ell0,minus(z,x)),ell1));
 const fac=div(mul(eta,mul(minus(d,s),qs(s,d))),sc(minus(a,one),2));
 const v1=sc(mul(minus(d,a),h(one)),2);
 const va=div(sc(mul(minus(d,one),h(a)),2),eta);
 const cleared=plus(mul(L,h(d)),mul(fac,minus(v1,va)));
 return {affine,cleared};
}

function check(name, x, expect){
 if(sign(x)!==expect)throw Error("inconclusive: "+name+" "+x.map(String).join(" "));
 console.log([name, ...x].map(String).join(" "));
}
console.log("common-scale "+K);
const den=1n<<40n, denC=1n<<20n;
const sl=rat(457148959716n,den), sh=rat(457148959717n,den);
const tl=rat(138977439915n,den), th=rat(138977439916n,den);
const cl=rat(1270550n,denC), ch=rat(1270551n,denC);
const s=take(sl,sh),t=take(tl,th),c=take(cl,ch);
if(sl[0]<=rat(13,32)[1]||sh[1]>=rat(14,32)[0]||
   tl[0]<=rat(1,8)[1]||th[1]>=rat(13,100)[0]||
   th[1]>=div(sl,rat(3))[0])throw Error("outside authorized branch");
check("seed-cubic-lower", Fs(sl), -1);
check("seed-cubic-upper", Fs(sh), 1);
check("reverse-quadratic-lower", qs(s,tl), 1);
check("reverse-quadratic-upper", qs(s,th), -1);
const {a,z,D,NB}=polys(s,t);
check("moment-determinant", D, 1);
check("larger-node-lower-minus-z", minus(cl,z), 1);
check("quadratic-at-zero", NB(zero), -1);
check("larger-node-polynomial-lower", NB(cl), -1);
check("larger-node-polynomial-upper", NB(ch), 1);
for(const [label,d,expect] of [["15/4",rat(15,4),-1],["4",rat(4),1]]) {
 const v=response(s,t,c,a,z,d);
 check("affine-"+label, v.affine, expect);
 check("direct-cleared-"+label, v.cleared, expect);
}
