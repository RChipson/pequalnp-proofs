// greedy weighted cover from candidate blocks. usage: pick3 n table.txt cands.txt  (rows as hex words)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static int pc(u128 x){return __builtin_popcountll((unsigned long long)x)+__builtin_popcountll((unsigned long long)(x>>64));}
static u128 rd(FILE*f){unsigned long long hi,lo; if(fscanf(f,"%llx %llx",&hi,&lo)!=2) exit(3); return ((u128)hi<<64)|lo;}
int n; u128 R[128],left_[128];
int main(int argc,char**argv){
  n=atoi(argv[1]); FILE*f=fopen(argv[2],"r"); for(int i=0;i<n;i++) R[i]=rd(f); fclose(f);
  f=fopen(argv[3],"r"); int m; if(fscanf(f,"%d",&m)!=1) return 3;
  u128*S=malloc(sizeof(u128)*m),*T=malloc(sizeof(u128)*m);
  for(int i=0;i<m;i++){S[i]=rd(f);T[i]=rd(f);} fclose(f);
  memcpy(left_,R,sizeof R);
  double*ub=malloc(sizeof(double)*m); for(int i=0;i<m;i++) ub[i]=1e9;
  long W=0; int nb=0;
  for(;;){
    int any=0; for(int i=0;i<n;i++) if(left_[i]) any=1; if(!any) break;
    double best=-1; int bi=-1; u128 bS=0,bT=0;
    for(int c=0;c<m;c++){
      if(ub[c]<=best) continue;   // lazy: gains only decrease
      u128 Sn=0,Tn=0; int nw=0;
      for(int i=0;i<n;i++) if(S[c]>>i&1){ u128 x=left_[i]&T[c]; if(x){Sn|=(u128)1<<i;Tn|=x;nw+=pc(x);} }
      double g= nw? (double)nw/(pc(Sn)+pc(Tn)) : 0;
      ub[c]=g;
      if(g>best){best=g;bi=c;bS=Sn;bT=Tn;}
    }
    for(int i=0;i<n;i++) if(bS>>i&1) left_[i]&=~bT;
    W+=pc(bS)+pc(bT); nb++;
    printf("B %016llx %016llx %016llx %016llx %.2f\n",(unsigned long long)(bS>>64),(unsigned long long)bS,(unsigned long long)(bT>>64),(unsigned long long)bT,best);
  }
  fprintf(stderr,"blocks %d weight %ld\n",nb,W);
}
