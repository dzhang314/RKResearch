# Exact replay: grade-nine primitive identity and saturated ranks for p18/p19

The following is complete standalone JavaScript (standard BigInt; run with Node or any JS engine providing console.log). I ran it independently of the text derivation. It normalizes the nonzero first pivot to 1, checks the full differentiated identity and the four rational moment zeros, certifies the only additional root 5/6 is simple, and enumerates unobserved intersection dimensions without choosing generic clock values.

For ranks, H is the last saturated ordinary grade, e is the indicator of g≠0, and cap bounds f_(H+1). The program uses only the strict-growth ceilings/floors, f₆≥f₃+4, the K⊂U containments and elementary Hermite consequences. Intersections F_j∩U are themselves invariant when their dimensions plateau across one step, because they are nested and C maps the old into the new. The last one-dimensional K/F₄ test is separately justified by the two physical prefix primitive evaluations. The output tuple is (f₄,f₅,f₆,f₇,f₉,k). The final mathematical one-head/quartic arguments are not replaced by enumeration.

```javascript
const add=(a,b)=>{const c=Array(Math.max(a.length,b.length)).fill(0n);for(let i=0;i<c.length;i++)c[i]=(a[i]||0n)+(b[i]||0n);while(c.length>1&&c[c.length-1]===0n)c.pop();return c};
const mul=(a,b)=>{let o=Array(a.length+b.length-1).fill(0n);for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)o[i+j]+=a[i]*b[j];return o};
const scale=(a,s)=>a.map(z=>s*z), x=[0n,1n], h=[-1n,1n];
function pow(a,n){let z=[1n];while(n--)z=mul(z,a);return z}
function deriv(a,k=1){while(k--)a=a.slice(1).map((z,i)=>BigInt(i+1)*z);return a}
const eq=(a,b)=>a.length===b.length&&a.every((v,i)=>v===b[i]);
const check=(t)=>{if(!t)throw Error("failed check")};
const F=mul(pow(x,5),pow(h,4)), f=deriv(F,4), G=add(mul(h,deriv(F)),scale(F,-3n));
check(eq(G,mul(mul(pow(x,4),pow(h,4)),[-5n,6n])));check(eq(deriv(G,3),mul(h,f)));
function atScaled(a,num,den){let D=a.length-1;return a.reduce((s,c,i)=>s+c*num**BigInt(i)*den**BigInt(D-i),0n)}
check(atScaled(G,5n,6n)===0n);check(atScaled(deriv(G),5n,6n)!==0n);
for(let j=0;j<4;j++)check(f.reduce((s,c,i)=>s+c*(27720n/BigInt(i+j+1)),0n)===0n);
function patterns(H,e,cap){
  const out=new Set();
  function ranks(j,fs){if(j<=H){for(let t=j-2+e;t<=j-1+e;t++){if(j>3&&t<=fs[j-1])continue;if(j===6&&t<fs[3]+4)continue;if(j===H&&t!==H-1+e)continue;fs[j]=t;ranks(j+1,fs)}return}
    for(let k=fs[4];k<=cap-Math.floor(H/2);k++){
      function intersections(j,aa){if(j>H){
        // If F4 -> F5 is one gain, F4 escapes by two-detector Hermite. Its C-extension is in K; hence F5=K=U at rank k=f5. The two independent physical detectors exclude this.
        if(fs[5]===fs[4]+1 && fs[5]===k) return;
        out.add([fs[4],fs[5],fs[6],fs[7],fs[9],k].join(","));return;}
        for(let a=0;a<=Math.min(fs[j],k);a++){
          if(j<=4&&a!==fs[j])continue;if(j===H&&a!==k)continue;
          if(j>3){const b=aa[j-1],q=fs[j-1]-b,prev=j-1;if(a<b)continue;
            if(q>0 && fs[j]-a<=q)continue;
            // If the intersection plateaus, it is C-invariant since C(F_i intersection U) is in the next intersection.
            if(a===b && a>0 && fs[j]<a+Math.floor(prev/2))continue;}
          aa[j]=a;intersections(j+1,aa);
        }
      }
      intersections(3,[]);
    }
  }
  ranks(3,[]);return [...out].sort();
}
const cases=[[9,0,10],[9,1,11],[10,0,11],[9,0,10]];
for(const [H,e,cap] of cases){const ans=patterns(H,e,cap);const want=[2+e,4+e,5+e,6+e,8+e].join(",");check(ans.join(";")===[want+","+(2+e),want+","+(3+e)].join(";"));console.log(H,e,cap,ans.join(";"))}
console.log("F",F.join(","),"G",G.join(","),"G'(5/6) numerator",atScaled(deriv(G),5n,6n).toString());
```

Actual output:

```
9 0 10 2,4,5,6,8,2;2,4,5,6,8,3
9 1 11 3,5,6,7,9,3;3,5,6,7,9,4
10 0 11 2,4,5,6,8,2;2,4,5,6,8,3
9 0 10 2,4,5,6,8,2;2,4,5,6,8,3
F 0,0,0,0,0,1,-4,6,-4,1 G 0,0,0,0,-5,26,-54,56,-29,6 G'(5/6) numerator 3750
```

The symbolic argument before this check proves the universal nonexistence of the quartic obstruction, not only the 5/6 sample: its exact factorization lists all potentially offending second pivots. The weighted fifth-debut complement theorem is separate.
