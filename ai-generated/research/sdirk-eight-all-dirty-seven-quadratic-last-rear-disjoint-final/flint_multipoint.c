#include <stdint.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long ul;
typedef long sl;
typedef struct {ul n,ninv,norm;} mod_t;
typedef struct {ul *coeffs; sl alloc,length; mod_t mod;} P;
extern void nmod_poly_init(P*,ul);
extern void nmod_poly_clear(P*);
extern void nmod_poly_fit_length(P*,sl);
extern ul nmod_poly_resultant(const P*,const P*);
extern void nmod_poly_evaluate_nmod_vec_fast(ul *,const P*,const ul *,sl);
extern void nmod_poly_interpolate_nmod_vec_fast(P*,const ul *,const ul *,sl);
static ul ev(const ul *a,sl lim,ul h,ul p){
    ul y=0;
    while(lim--)y=((__uint128_t)y*h+a[lim])%p;
    return y;
}
static void assign(P *s,const ul *a,sl n){
    nmod_poly_fit_length(s,n);
    if(n)memcpy(s->coeffs,a,n*sizeof(ul));
    while(n && !a[n-1])n--;
    s->length=n;
}
int rk_mp(ul *out,const ul *aa,sl wa,sl da,const ul *bb,sl wb,sl db,
          ul p,sl ways){
    if(ways<=0 || (ul)ways>=p || wa<=0 || wb<=0)return 1;
    ul *pts=malloc((size_t)ways*sizeof(ul));
    ul *res=malloc((size_t)ways*sizeof(ul));
    ul *la=malloc((size_t)ways*(da+1)*sizeof(ul));
    ul *lb=malloc((size_t)ways*(db+1)*sizeof(ul));
    if(!pts||!res||!la||!lb){free(pts);free(res);free(la);free(lb);return 2;}
    sl n=0;
    for(ul h=0;n<ways && h<p;h++)
        if(ev(aa+wa*da,wa,h,p)&&ev(bb+wb*db,wb,h,p))pts[n++]=h;
    if(n!=ways){free(pts);free(res);free(la);free(lb);return 3;}
    P s,a,b,R;
    nmod_poly_init(&s,p); nmod_poly_init(&a,p); nmod_poly_init(&b,p);
    nmod_poly_init(&R,p);
    for(sl j=0;j<=da;j++){
        assign(&s,aa+wa*j,wa);
        nmod_poly_evaluate_nmod_vec_fast(la+ways*j,&s,pts,ways);
    }
    for(sl j=0;j<=db;j++){
        assign(&s,bb+wb*j,wb);
        nmod_poly_evaluate_nmod_vec_fast(lb+ways*j,&s,pts,ways);
    }
    nmod_poly_fit_length(&a,da+1);
    nmod_poly_fit_length(&b,db+1);
    a.length=da+1;b.length=db+1;
    for(sl i=0;i<ways;i++){
        for(sl j=0;j<=da;j++)a.coeffs[j]=la[ways*j+i];
        for(sl j=0;j<=db;j++)b.coeffs[j]=lb[ways*j+i];
        res[i]=nmod_poly_resultant(&a,&b);
    }
    nmod_poly_interpolate_nmod_vec_fast(&R,pts,res,ways);
    memset(out,0,ways*sizeof(ul));
    memcpy(out,R.coeffs,R.length*sizeof(ul));
    nmod_poly_clear(&R);nmod_poly_clear(&b);nmod_poly_clear(&a);nmod_poly_clear(&s);
    free(pts);free(res);free(la);free(lb);
    return 0;
}
