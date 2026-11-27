// Joint annealing of a block cover and a pairing of its blocks, on the true cost of the mixed-OR circuit:
//   cost = OR gates of a greedy sharing (Paar: repeatedly make a gate of the most frequent pair) of the mixed sets
//          + one AND per term + the ORs joining the terms.
// A term is a pair of blocks (S_i, T_i), (S_j, T_j) with no common row and no common column, giving the mixed sets
// S_i u T_j and S_j u T_i, or a single block (sets S_i and T_i).
// Moves: re-pair two terms; add a row/column to a block (the block stays all-ones and disjoint from its partner);
// remove a row/column from a block (every cell stays covered).
// usage: jointsa n table.txt cover.txt out.txt seed seconds t0 t1
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
typedef unsigned __int128 u128;
#define MAXB 320
#define MAXL 96
#define MAXI 4200
static unsigned long long rs=88172645463325252ULL;
static inline unsigned long long rnd(){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static inline double rnd01(){return (rnd()>>11)*(1.0/9007199254740992.0);}
static int pc(u128 x){return __builtin_popcountll((unsigned long long)x)+__builtin_popcountll((unsigned long long)(x>>64));}
int n; u128 R[128],C[128]; u128 S[MAXB],T[MAXB]; int p[MAXB]; int nb; int cov[128][128];
static u128 rdw(const char*a,const char*b){return ((u128)strtoull(a,0,16)<<64)|strtoull(b,0,16);}
static unsigned short cnt[MAXI][MAXI];
static int sets[2*MAXB][MAXL], len[2*MAXB];
// greedy sharing with a heap of candidate pairs (stale entries are checked against the counts when popped)
static unsigned long long *heap; static long hn=0,hcap=0;
static inline void hpush(unsigned long long k){ if(hn>=hcap){hcap=hcap?hcap*2:1<<16; heap=realloc(heap,hcap*sizeof *heap);} long i=hn++; heap[i]=k; while(i>0){ long q=(i-1)/2; if(heap[q]>=heap[i]) break; unsigned long long t=heap[q];heap[q]=heap[i];heap[i]=t;i=q; } }
static inline unsigned long long hpop(void){ unsigned long long top=heap[0]; heap[0]=heap[--hn]; long i=0; for(;;){ long l=2*i+1,r=l+1,m=i; if(l<hn&&heap[l]>heap[m]) m=l; if(r<hn&&heap[r]>heap[m]) m=r; if(m==i) break; unsigned long long t=heap[m];heap[m]=heap[i];heap[i]=t;i=m; } return top; }
static int *touched; static long tn=0,tcap=0;
static inline void touch(int a,int b){ if(tn+2>tcap){tcap=tcap?tcap*2:1<<16; touched=realloc(touched,tcap*sizeof *touched);} touched[tn++]=a; touched[tn++]=b; }
#define KEY(c,a,b) (((unsigned long long)(c)<<40)|((unsigned long long)(a)<<20)|(unsigned long long)(b))
static int paar_cost(void){
  int ns=0,terms=0;
  for(int i=0;i<nb;i++){
    if(S[i]==0) continue;
    if(p[i]==i){ int l=0; for(int u=0;u<n;u++) if(S[i]>>u&1) sets[ns][l++]=u; len[ns++]=l; l=0; for(int v=0;v<n;v++) if(T[i]>>v&1) sets[ns][l++]=n+v; len[ns++]=l; terms++; }
    else if(i<p[i]){ int j=p[i]; int l=0; for(int u=0;u<n;u++) if(S[i]>>u&1) sets[ns][l++]=u; for(int v=0;v<n;v++) if(T[j]>>v&1) sets[ns][l++]=n+v; len[ns++]=l;
      l=0; for(int u=0;u<n;u++) if(S[j]>>u&1) sets[ns][l++]=u; for(int v=0;v<n;v++) if(T[i]>>v&1) sets[ns][l++]=n+v; len[ns++]=l; terms++; }
  }
  int ni=2*n; hn=0; tn=0;
  for(int s=0;s<ns;s++) for(int i=0;i<len[s];i++) for(int j=i+1;j<len[s];j++){ int a=sets[s][i],b=sets[s][j]; if(a>b){int t=a;a=b;b=t;} if(cnt[a][b]==0) touch(a,b); cnt[a][b]++; }
  for(long q=0;q<tn;q+=2){ int a=touched[q],b=touched[q+1]; if(cnt[a][b]>=2) hpush(KEY(cnt[a][b],a,b)); }
  int defs=0;
  while(hn>0){
    unsigned long long k=hpop(); int c=(int)(k>>40),ba=(int)((k>>20)&0xFFFFF),bb=(int)(k&0xFFFFF);
    int cc=cnt[ba][bb];
    if(cc!=c){ if(cc>=2) hpush(KEY(cc,ba,bb)); continue; }
    if(ni>=MAXI-1) break;
    int z=ni++; defs++;
    for(int s=0;s<ns;s++){
      int ia=-1,ib=-1; for(int i=0;i<len[s];i++){ if(sets[s][i]==ba) ia=i; else if(sets[s][i]==bb) ib=i; }
      if(ia<0||ib<0) continue;
      for(int i=0;i<len[s];i++){ int x=sets[s][i]; if(x==ba||x==bb) continue;
        int a=ba<x?ba:x,b=ba<x?x:ba; cnt[a][b]--; a=bb<x?bb:x; b=bb<x?x:bb; cnt[a][b]--;
        if(cnt[x][z]==0) touch(x,z); cnt[x][z]++; if(cnt[x][z]>=2) hpush(KEY(cnt[x][z],x,z)); }
      cnt[ba][bb]--;
      int l=0; for(int i=0;i<len[s];i++){ int x=sets[s][i]; if(x!=ba&&x!=bb) sets[s][l++]=x; } sets[s][l++]=z; len[s]=l;
    }
  }
  for(long q=0;q<tn;q+=2) cnt[touched[q]][touched[q+1]]=0;
  int c=defs; for(int s=0;s<ns;s++) c+=len[s]-1;
  return c+terms+terms-1;
}
static int valid_pair(int i,int j){ return (S[i]&S[j])==0 && (T[i]&T[j])==0; }
int main(int argc,char**argv){
  n=atoi(argv[1]); FILE*f=fopen(argv[2],"r"); char a[64],b[64],c[64],d[64],line[512];
  for(int i=0;i<n;i++){ if(fscanf(f,"%s %s",a,b)!=2) return 3; R[i]=rdw(a,b);} fclose(f);
  for(int v=0;v<n;v++){C[v]=0; for(int u=0;u<n;u++) if(R[u]>>v&1) C[v]|=(u128)1<<u;}
  f=fopen(argv[3],"r"); nb=0;
  while(fgets(line,sizeof line,f)){ if(line[0]!='B') continue; int pp=-1; int k=sscanf(line+1,"%s %s %s %s %d",a,b,c,d,&pp); if(k<4) continue; S[nb]=rdw(a,b);T[nb]=rdw(c,d);p[nb]=(k==5&&pp>=0)?pp:nb;nb++; }
  fclose(f);
  rs^=strtoull(argv[5],0,10)*0x9E3779B97F4A7C15ULL; for(int i=0;i<20;i++) rnd();
  double secs=atof(argv[6]),t0=atof(argv[7]),t1=atof(argv[8]);
  memset(cov,0,sizeof cov);
  for(int j=0;j<nb;j++) for(int u=0;u<n;u++) if(S[j]>>u&1) for(int v=0;v<n;v++) if(T[j]>>v&1){ if(!(R[u]>>v&1)){fprintf(stderr,"bad block\n");return 4;} cov[u][v]++; }
  for(int u=0;u<n;u++) for(int v=0;v<n;v++) if((R[u]>>v&1)&&!cov[u][v]){fprintf(stderr,"uncovered\n");return 4;}
  // pairing given in the file is kept if valid, otherwise a random greedy one
  int given=0; for(int i=0;i<nb;i++) if(p[i]!=i) given=1;
  if(given){ for(int i=0;i<nb;i++){ int j=p[i]; if(j<0||j>=nb||p[j]!=i||(j!=i&&!valid_pair(i,j))) { p[i]=i; if(j>=0&&j<nb&&p[j]==i) p[j]=j; } } }
  else for(int i=0;i<nb;i++){ if(p[i]!=i) continue; int st=rnd()%nb; for(int k=0;k<nb;k++){ int j=(st+k)%nb; if(j!=i&&p[j]==j&&valid_pair(i,j)){p[i]=j;p[j]=i;break;} } }
  int cur=paar_cost(), best=cur; static u128 bS[MAXB],bT[MAXB]; static int bp[MAXB];
  memcpy(bS,S,sizeof S);memcpy(bT,T,sizeof T);memcpy(bp,p,sizeof p);
  struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); double start=ts.tv_sec+ts.tv_nsec*1e-9, now=start; long it=0,acc=0;
  fprintf(stderr,"start cost %d (blocks %d)\n",cur,nb);
  while(now-start<secs){
    it++; if((it&15)==0){ clock_gettime(CLOCK_MONOTONIC,&ts); now=ts.tv_sec+ts.tv_nsec*1e-9; }
    double temp=t0*pow(t1/t0,(now-start)/secs);
    u128 oS[4],oT[4]; int op[4],ix[4],nx=0;
    #define SAVE(i) { ix[nx]=i; oS[nx]=S[i]; oT[nx]=T[i]; op[nx]=p[i]; nx++; }
    int mv=rnd()%10; int ok=0;
    if(mv<5){ // re-pair
      int i=rnd()%nb,k=rnd()%nb; if(i==k||p[i]==k) continue; int j=p[i],l=p[k];
      SAVE(i); if(j!=i) SAVE(j); SAVE(k); if(l!=k) SAVE(l);
      p[i]=i;p[j]=j;p[k]=k;p[l]=l;
      int a1,b1,a2,b2; if(rnd()&1){a1=i;b1=k;a2=j;b2=l;} else {a1=i;b1=l;a2=j;b2=k;}
      ok=1;
      if(a1!=b1){ if(p[a1]==a1&&p[b1]==b1&&valid_pair(a1,b1)){p[a1]=b1;p[b1]=a1;} else ok=0; }
      if(ok&&a2!=b2&&a2!=a1&&a2!=b1&&b2!=a1&&b2!=b1){ if(p[a2]==a2&&p[b2]==b2&&valid_pair(a2,b2)){p[a2]=b2;p[b2]=a2;} /* else they stay single */ }
    } else {
      int i=rnd()%nb; int side=rnd()&1; int x=rnd()%n; int j=p[i];
      SAVE(i);
      if(side==0){
        if(S[i]>>x&1){ // remove row x
          if(pc(S[i])<=1) ok=0; else { ok=1; for(int v=0;v<n&&ok;v++) if((T[i]>>v&1)&&cov[x][v]<2) ok=0;
            if(ok){ for(int v=0;v<n;v++) if(T[i]>>v&1) cov[x][v]--; S[i]&=~((u128)1<<x); } }
        } else { // add row x
          if((T[i]&~R[x])==0 && (j==i || !(S[j]>>x&1))){ ok=1; for(int v=0;v<n;v++) if(T[i]>>v&1) cov[x][v]++; S[i]|=(u128)1<<x; }
        }
      } else {
        if(T[i]>>x&1){
          if(pc(T[i])<=1) ok=0; else { ok=1; for(int u=0;u<n&&ok;u++) if((S[i]>>u&1)&&cov[u][x]<2) ok=0;
            if(ok){ for(int u=0;u<n;u++) if(S[i]>>u&1) cov[u][x]--; T[i]&=~((u128)1<<x); } }
        } else {
          if((S[i]&~C[x])==0 && (j==i || !(T[j]>>x&1))){ ok=1; for(int u=0;u<n;u++) if(S[i]>>u&1) cov[u][x]++; T[i]|=(u128)1<<x; }
        }
      }
    }
    if(!ok){ for(int q=nx-1;q>=0;q--){S[ix[q]]=oS[q];T[ix[q]]=oT[q];p[ix[q]]=op[q];} continue; }
    int c2=paar_cost();
    if(c2<=cur || rnd01()<exp((cur-c2)/temp)){ cur=c2; acc++;
      if(cur<best){best=cur;memcpy(bS,S,sizeof S);memcpy(bT,T,sizeof T);memcpy(bp,p,sizeof p); fprintf(stderr,"%.0f s: %d\n",now-start,best);} }
    else { // undo (cover counts too)
      if(mv>=5){ int i=ix[0];
        for(int u=0;u<n;u++) if(S[i]>>u&1) for(int v=0;v<n;v++) if(T[i]>>v&1) cov[u][v]--;
        S[i]=oS[0];T[i]=oT[0];
        for(int u=0;u<n;u++) if(S[i]>>u&1) for(int v=0;v<n;v++) if(T[i]>>v&1) cov[u][v]++;
      }
      for(int q=nx-1;q>=0;q--){S[ix[q]]=oS[q];T[ix[q]]=oT[q];p[ix[q]]=op[q];}
    }
  }
  f=fopen(argv[4],"w");
  for(int j=0;j<nb;j++) fprintf(f,"B %016llx %016llx %016llx %016llx %d\n",(unsigned long long)(bS[j]>>64),(unsigned long long)bS[j],(unsigned long long)(bT[j]>>64),(unsigned long long)bT[j],bp[j]);
  fclose(f);
  printf("best cost %d after %ld moves (%ld accepted)\n",best,it,acc);
}
