// Mirror of the kernel-checked search in the accepted proof of L-meta-8718 (k-sandhu), used here
// only to predict its answer and its cost before a proof file is written.
// Input: n, then the input words (hex), one per variable: bit i (i < 32) is the variable's value
// at the i-th true point, bit 32+i its value at the i-th false point.
// Output: "true"/"false" (whether a derivation with at most n binary steps reaches the goal or
// its complement on the samples) and the number of calls made.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t W;
static const W GOAL=0xFFFFFFFF00000000ULL;
static unsigned long long calls;
static inline uint32_t sep(W x){ return (uint32_t)((x>>32)^x); }
static uint32_t cuts(const W*ws,int n){ uint32_t v=0; for(int i=0;i<n;i++) v|=sep(ws[i]); return v; }
static int optimized(int k,int extra,const W*ws,int len);
static int dispatch(int k,int extra,W a,W b,const W*r,int rl){
  uint32_t base=cuts(r,rl); W ops[4]={a&b,a|b,a&~b,b&~a}; W nw[16];
  for(int t=0;t<4;t++){ W w=ops[t]; uint32_t v=sep(w)|base; calls++;
    if(v==0xFFFFFFFFu){ nw[0]=w; for(int i=0;i<rl;i++) nw[1+i]=r[i]; if(optimized(k,extra,nw,rl+1)) return 1; }
    if(extra!=0){
      if((v|sep(a))==0xFFFFFFFFu){ nw[0]=w; nw[1]=a; for(int i=0;i<rl;i++) nw[2+i]=r[i]; if(optimized(k,extra-1,nw,rl+2)) return 1; }
      if((v|sep(b))==0xFFFFFFFFu){ nw[0]=w; nw[1]=b; for(int i=0;i<rl;i++) nw[2+i]=r[i]; if(optimized(k,extra-1,nw,rl+2)) return 1; }
    }
    if(extra>=2 && (v|sep(a)|sep(b))==0xFFFFFFFFu){ nw[0]=w; nw[1]=a; nw[2]=b; for(int i=0;i<rl;i++) nw[3+i]=r[i]; if(optimized(k,extra-2,nw,rl+3)) return 1; }
  }
  return 0;
}
static int optimized(int k,int extra,const W*ws,int len){
  calls++;
  if(len==1 && (ws[0]==GOAL || ws[0]==~GOAL)) return 1;
  if(k==0) return 0;
  W r[16];
  for(int i=0;i<len;i++) for(int j=i+1;j<len;j++){
    int rl=0; for(int t=0;t<len;t++) if(t!=i&&t!=j) r[rl++]=ws[t];
    if(dispatch(k-1,extra,ws[i],ws[j],r,rl)) return 1;
  }
  return 0;
}
int main(int argc,char**argv){
  int n=atoi(argv[1]); int m=argc-2; W in[16]; for(int i=0;i<m;i++) in[i]=strtoull(argv[2+i],0,16);
  int found=0;
  for(int mask=0;mask<(1<<m)&&!found;mask++){
    W ws[16]; int len=0; for(int i=0;i<m;i++) if(mask>>i&1) ws[len++]=in[i];
    if(len>n+1) continue; calls++;
    if(cuts(ws,len)!=0xFFFFFFFFu) continue;
    if(optimized(n,n+1-len,ws,len)) found=1;
  }
  printf("%s %llu\n",found?"true":"false",calls); return 0;
}
