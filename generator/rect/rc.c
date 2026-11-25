// Simulated annealing: cover the zeros of a 0/1 matrix by K all-zero rectangles.
// A rectangle is a set S of rows together with every column that is zero on all of S.
// Usage: rc <matrix file> K seed iterations T0 T1 restarts
// Matrix file: R C, then R row masks (bit j of row i is the entry in column j). C at most 63.
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
typedef unsigned long long u64;
static u64 rs;
static inline u64 rnd(){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static int R,C,K; static u64 rowmask[64],S[256],Q[256],ALLC; static int cnt[64][64]; static int unc;
static u64 qof(u64 s){u64 q=ALLC; for(int i=0;i<R;i++) if(s>>i&1) q&=~rowmask[i]; return s?q:0;}
static void addrect(u64 s,u64 q,int d){ for(int i=0;i<R;i++) if(s>>i&1) for(int j=0;j<C;j++) if(q>>j&1){ if(d>0){ if(cnt[i][j]==0) unc--; cnt[i][j]++; } else { cnt[i][j]--; if(cnt[i][j]==0) unc++; } } }
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); if(!f||fscanf(f,"%d %d",&R,&C)!=2||R>64||C>63) return 2;
  for(int i=0;i<R;i++) if(fscanf(f,"%llu",&rowmask[i])!=1) return 2;
  ALLC=(1ULL<<C)-1;
  K=atoi(argv[2]); rs=strtoull(argv[3],0,10)*2654435761ULL+88172645463325252ULL; long iters=atol(argv[4]); double T0=atof(argv[5]),T1=atof(argv[6]); int maxr=atoi(argv[7]);
  int best=1<<30;
  for(int rst=0;rst<maxr;rst++){
    memset(cnt,0,sizeof cnt); unc=0; for(int i=0;i<R;i++) for(int j=0;j<C;j++) if(!(rowmask[i]>>j&1)) unc++;
    for(int k=0;k<K;k++){ S[k]=0; for(int t=0;t<3;t++) S[k]|=1ULL<<(rnd()%R); Q[k]=qof(S[k]); addrect(S[k],Q[k],1); }
    int cur=unc;
    for(long it=0;it<iters&&cur;it++){
      double T=T0*pow(T1/T0,(double)it/iters);
      int k=rnd()%K; u64 ns=S[k]^(1ULL<<(rnd()%R)); if(rnd()%4==0) ns^=1ULL<<(rnd()%R);
      u64 nq=qof(ns); u64 os=S[k],oq=Q[k];
      addrect(os,oq,-1); addrect(ns,nq,1);
      if(unc<=cur || (double)(rnd()>>11)/9007199254740992.0<exp((cur-unc)/T)){ cur=unc; S[k]=ns; Q[k]=nq; }
      else { addrect(ns,nq,-1); addrect(os,oq,1); }
    }
    if(cur<best) best=cur;
    if(cur==0){ printf("FOUND K=%d restart %d\n",K,rst); for(int k=0;k<K;k++) printf("%llu %llu\n",S[k],Q[k]); return 0; }
    fprintf(stderr,"K=%d restart %d uncovered %d (best %d)\n",K,rst,cur,best);
  }
  printf("GIVEUP K=%d best uncovered %d\n",K,best); return 1;
}
