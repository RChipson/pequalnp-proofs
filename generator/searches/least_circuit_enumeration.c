#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u64;
int n, S; u64 FULL;
// targets
#define MAXT 40000
u64 Tt[MAXT]; int Tedges[MAXT]; int Tmask[MAXT]; int L[MAXT]; unsigned junkSeen[MAXT]; int nT=0;
// example circuits
int exA[MAXT][8][12], exB[MAXT][8][12], exO[MAXT][8][12]; 
#define HS (1<<18)
int H[HS];
static inline unsigned hh(u64 x){ uint64_t y=(uint64_t)x ^ ((uint64_t)(x>>64)*0xC2B2AE3D27D4EB4FULL); y*=0x9E3779B97F4A7C15ULL; return (unsigned)(y>>46); }
int look(u64 t){ unsigned h=hh(t)&(HS-1); while(H[h]>=0){ if(Tt[H[h]]==t) return H[h]; h=(h+1)&(HS-1);} return -1; }
void ins(int i){ unsigned h=hh(Tt[i])&(HS-1); while(H[h]>=0) h=(h+1)&(HS-1); H[h]=i; }
u64 tt[32]; int fo[32]; int ga[32], gb[32], gop[32];
int s; long long nodes=0;
void leaf(){
  u64 f=tt[n+s-1]; int t=look(f); if(t<0) return;
  if(L[t]<s) return; L[t]=s;
  int jc=0; for(int j=0;j<s;j++) if(gop[j]==0 && (tt[n+j]&~f)) jc++;
  if(!(junkSeen[t]&(1u<<jc))){ junkSeen[t]|=1u<<jc; if(jc<8) for(int j=0;j<s;j++){exA[t][jc][j]=ga[j];exB[t][jc][j]=gb[j];exO[t][jc][j]=gop[j];} }
}
void dfs(int j,int unused){
  nodes++;
  if(j==s){ leaf(); return; }
  int r=s-1-j; int W=n+j;
  for(int b=1;b<W;b++) for(int a=0;a<b;a++){
    int nu=unused-(fo[a]==0)-(fo[b]==0)+1;
    if(nu>r+1) continue;
    int usesPrev = (j>0 && b==W-1);
    for(int op=0;op<2;op++){
      if(j>0 && !usesPrev){ // key must exceed prev key
        int pb=gb[j-1], pa=ga[j-1], po=gop[j-1];
        if(b<pb) continue; if(b==pb){ if(a<pa) continue; if(a==pa && op<=po) continue; }
      }
      u64 t = op==0 ? (tt[a]&tt[b]) : (tt[a]|tt[b]);
      int dup=0; for(int w=0;w<W;w++) if(tt[w]==t){dup=1;break;}
      if(dup) continue;
      tt[W]=t; ga[j]=a; gb[j]=b; gop[j]=op; fo[a]++; fo[b]++; fo[W]=0;
      dfs(j+1,nu);
      fo[a]--; fo[b]--;
    }
  }
}
int main(int argc,char**argv){
  n=atoi(argv[1]); S=atoi(argv[2]); int N=1<<n; FULL=0;
  memset(H,-1,sizeof H);
  int pairs[32][2], np=0; for(int u=0;u<n;u++) for(int v=u+1;v<n;v++){pairs[np][0]=u;pairs[np][1]=v;np++;}
  for(int m=1;m<(1<<np);m++){
    int adj[8]={0}; int ne=0;
    for(int p=0;p<np;p++) if(m>>p&1){adj[pairs[p][0]]|=1<<pairs[p][1]; adj[pairs[p][1]]|=1<<pairs[p][0]; ne++;}
    int ok=1; for(int u=0;u<n;u++) if(!adj[u]) ok=0; if(!ok) continue;
    // C4-free
    for(int u=0;u<n&&ok;u++) for(int v=u+1;v<n;v++) if(__builtin_popcount(adj[u]&adj[v])>=2){ok=0;break;}
    if(!ok) continue;
    // bipartite: 2-colour
    int col[8]; for(int i=0;i<n;i++) col[i]=-1;
    for(int st=0;st<n&&ok;st++){ if(col[st]>=0) continue; col[st]=0; int stack[8],sp=0; stack[sp++]=st;
      while(sp&&ok){int u=stack[--sp]; for(int v=0;v<n;v++) if(adj[u]>>v&1){ if(col[v]<0){col[v]=1-col[u];stack[sp++]=v;} else if(col[v]==col[u]) ok=0; }}}
    if(!ok) continue;
    u64 f=0; for(int x=0;x<N;x++){ int val=0; for(int u=0;u<n;u++) if((x>>u&1)&&(adj[u]&x)) val=1; if(val) f|=((u64)1)<<x; }
    Tt[nT]=f; Tedges[nT]=ne; Tmask[nT]=m; L[nT]=99; junkSeen[nT]=0; ins(nT); nT++;
  }
  fprintf(stderr,"targets %d\n",nT);
  for(int i=0;i<n;i++){ u64 t=0; for(int x=0;x<N;x++) if(x>>i&1) t|=((u64)1)<<x; tt[i]=t; fo[i]=0; }
  for(s=1;s<=S;s++){ nodes=0; dfs(0,n); fprintf(stderr,"size %d nodes %lld\n",s,nodes); 
    int found=0; for(int t=0;t<nT;t++) if(L[t]==s) found++; fprintf(stderr," targets with L=%d: %d\n",s,found); }
  int unk=0; unsigned agg[16]={0};
  for(int t=0;t<nT;t++){ if(L[t]==99){unk++;continue;} agg[L[t]]|=junkSeen[t];
    if(junkSeen[t]!=1){ printf("graph mask %d edges %d L %d junkSeen %x\n",Tmask[t],Tedges[t],L[t],junkSeen[t]);
      for(int jc=1;jc<8;jc++) if(junkSeen[t]>>jc&1){ printf("  junk=%d:",jc); for(int j=0;j<L[t];j++) printf(" %s(%d,%d)",exO[t][jc][j]?"OR":"AND",exA[t][jc][j],exB[t][jc][j]); printf("\n"); } } }

  { int np2=0,pr[32][2]; for(int u=0;u<n;u++) for(int v=u+1;v<n;v++){pr[np2][0]=u;pr[np2][1]=v;np2++;}
    int below=0,equal=0,above=0,known=0;
    for(int t=0;t<nT;t++){ if(L[t]==99) continue; known++;
      int best=0; int m=Tmask[t];
      for(int sub=m; ; sub=(sub-1)&m){ int used=0,ok=1,c=0; for(int p=0;p<np2&&ok;p++) if(sub>>p&1){ int bm=(1<<pr[p][0])|(1<<pr[p][1]); if(used&bm) ok=0; used|=bm; c++; } if(ok&&c>best) best=c; if(sub==0) break; }
      int bound=Tedges[t]+best-1;
      if(L[t]<bound){ below++; printf("COUNTEREXAMPLE graph mask %d edges %d matching %d least size %d\n",Tmask[t],Tedges[t],best,L[t]); }
      else if(L[t]==bound) equal++; else above++; }
    printf("known %d: least size below edges+matching-1: %d, equal: %d, above: %d\n",known,below,equal,above); }
  printf("n=%d unknown(L>%d): %d\n",n,S,unk); for(int k=1;k<=S;k++) printf(" L=%d junk-count set %x\n",k,agg[k]);
  return 0;
}
