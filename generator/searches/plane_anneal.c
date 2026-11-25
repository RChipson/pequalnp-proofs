// simulated annealing for a fan-in-two AND/OR circuit on the decisive rows of the order-3 plane
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
typedef unsigned long long u64;
#include "rows.h"
#define MAXG 80
static int N; static int ty[MAXG],ga[MAXG],gb[MAXG]; static u64 val[NI+MAXG][W];
static u64 rs;
static inline u64 rnd(){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static inline int evalfrom(int s){
  for(int i=s;i<N;i++){u64*a=val[ga[i]],*b=val[gb[i]],*o=val[NI+i]; if(ty[i]) for(int w=0;w<W;w++)o[w]=a[w]&b[w]; else for(int w=0;w<W;w++)o[w]=a[w]|b[w];}
  int c=0; u64*o=val[NI+N-1]; for(int w=0;w<W;w++)c+=__builtin_popcountll(o[w]^target[w]); return c;
}
int main(int argc,char**argv){
  N=atoi(argv[1]); rs=strtoull(argv[2],0,10)*2654435761ULL+88172645463325252ULL; long iters=atol(argv[3]);
  double T0=atof(argv[4]), T1=atof(argv[5]); int maxr=atoi(argv[6]);
  for(int i=0;i<NI;i++)memcpy(val[i],cols[i],sizeof(val[i]));
  int restarts=0, gbest=1<<30;
  while(1){
    for(int i=0;i<N;i++){ty[i]=rnd()&1;ga[i]=rnd()%(NI+i);gb[i]=rnd()%(NI+i);}
    int c=evalfrom(0); int best=c;
    for(long it=0;it<iters;it++){
      double T=T0*pow(T1/T0,(double)it/iters);
      int i=rnd()%N; int ot=ty[i],oa=ga[i],ob=gb[i];
      int r=rnd()%5;
      if(r==0)ty[i]^=1; else if(r<3)ga[i]=rnd()%(NI+i); else gb[i]=rnd()%(NI+i);
      int c2=evalfrom(i);
      if(c2<=c || (double)(rnd()>>11)/9007199254740992.0<exp((c-c2)/T)){c=c2; if(c<best)best=c; if(c==0)break;}
      else {ty[i]=ot;ga[i]=oa;gb[i]=ob; evalfrom(i);}
    }
    restarts++; if(best<gbest)gbest=best;
    if(c==0){ printf("FOUND N=%d restarts=%d\n",N,restarts); for(int i=0;i<N;i++)printf("%d %s %d %d\n",NI+i,ty[i]?"AND":"OR",ga[i],gb[i]); fflush(stdout); return 0;}
    fprintf(stderr,"N=%d restart %d: best wrong rows %d (overall %d)\n",N,restarts,best,gbest);
    if(restarts>=maxr){printf("GIVEUP N=%d best wrong rows %d\n",N,gbest);return 1;}
  }
}
