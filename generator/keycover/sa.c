// Simulated annealing on a cover of the ones of an n by n table by all-ones blocks, minimising
// sum(|S|+|T|) + 2*(number of blocks).  usage: sa n table.txt cover.txt out.txt seed moves(millions) t0 t1
// cover.txt lines: "B Shi Slo Thi Tlo ..."
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
typedef unsigned __int128 u128;
#define MAXB 1200
static int pc(u128 x){return __builtin_popcountll((unsigned long long)x)+__builtin_popcountll((unsigned long long)(x>>64));}
static unsigned long long rs=88172645463325252ULL;
static inline unsigned long long rnd(){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static inline double rnd01(){return (rnd()>>11)*(1.0/9007199254740992.0);}
int n; u128 R[128],C[128]; u128 S[MAXB],T[MAXB]; int alive[MAXB]; int nb=0; int cnt[128][128];
long cost(){long c=0; for(int j=0;j<nb;j++) if(alive[j]) c+=pc(S[j])+pc(T[j])+2; return c;}
static u128 rdw(const char*a,const char*b){return ((u128)strtoull(a,0,16)<<64)|strtoull(b,0,16);}
int main(int argc,char**argv){
  n=atoi(argv[1]); FILE*f=fopen(argv[2],"r"); char a[64],b[64],c[64],d[64],line[512];
  for(int i=0;i<n;i++){ if(fscanf(f,"%s %s",a,b)!=2) return 3; R[i]=rdw(a,b);} fclose(f);
  for(int v=0;v<n;v++){C[v]=0; for(int u=0;u<n;u++) if(R[u]>>v&1) C[v]|=(u128)1<<u;}
  f=fopen(argv[3],"r");
  while(fgets(line,sizeof line,f)){ if(line[0]!='B') continue; if(sscanf(line+1,"%s %s %s %s",a,b,c,d)!=4) continue; S[nb]=rdw(a,b);T[nb]=rdw(c,d);alive[nb]=1;nb++; }
  fclose(f);
  rs^=strtoull(argv[5],0,10)*0x9E3779B97F4A7C15ULL; for(int i=0;i<20;i++) rnd();
  double M=atof(argv[6])*1e6, t0=atof(argv[7]), t1=atof(argv[8]);
  memset(cnt,0,sizeof cnt);
  for(int j=0;j<nb;j++) for(int u=0;u<n;u++) if(S[j]>>u&1) for(int v=0;v<n;v++) if(T[j]>>v&1){ if(!(R[u]>>v&1)){fprintf(stderr,"bad block\n");return 4;} cnt[u][v]++; }
  for(int u=0;u<n;u++) for(int v=0;v<n;v++) if((R[u]>>v&1)&&!cnt[u][v]){fprintf(stderr,"uncovered\n");return 4;}
  long cur=cost(), best=cur; static u128 bS[MAXB],bT[MAXB]; static int bal[MAXB]; int bnb=nb;
  memcpy(bS,S,sizeof S);memcpy(bT,T,sizeof T);memcpy(bal,alive,sizeof alive);
  // list of one-cells for block creation
  static int ones[16384][2]; int no=0; for(int u=0;u<n;u++) for(int v=0;v<n;v++) if(R[u]>>v&1){ones[no][0]=u;ones[no][1]=v;no++;}
  for(double it=0;it<M;it++){
    double temp=t0*pow(t1/t0,it/M);
    double padd=exp(-1.0/temp);
    unsigned long long r=rnd();
    if((r&1023)==0){ // create a 1x1 block at a random one-cell
      if(rnd01()<exp(-4.0/temp)){
        int j=-1; for(int k=0;k<nb;k++) if(!alive[k]){j=k;break;} if(j<0){ if(nb>=MAXB) continue; j=nb++; }
        int k=rnd()%no; S[j]=(u128)1<<ones[k][0]; T[j]=(u128)1<<ones[k][1]; alive[j]=1; cnt[ones[k][0]][ones[k][1]]++; cur+=4;
      }
      continue;
    }
    int j=(r>>10)%nb; if(!alive[j]) continue;
    int side=(r>>30)&1; int i=(r>>32)%n;
    if(side==0){
      if(S[j]>>i&1){ // remove row i
        int ok=1; for(int v=0;v<n&&ok;v++) if((T[j]>>v&1)&&cnt[i][v]<2) ok=0;
        if(!ok) continue;
        for(int v=0;v<n;v++) if(T[j]>>v&1) cnt[i][v]--;
        S[j]&=~((u128)1<<i); cur--;
        if(S[j]==0){ cur-=pc(T[j])+2; alive[j]=0; T[j]=0; }
      } else { // add row i
        if(T[j]&~R[i]) continue;
        if(rnd01()>=padd) continue;
        for(int v=0;v<n;v++) if(T[j]>>v&1) cnt[i][v]++;
        S[j]|=(u128)1<<i; cur++;
      }
    } else {
      if(T[j]>>i&1){
        int ok=1; for(int u=0;u<n&&ok;u++) if((S[j]>>u&1)&&cnt[u][i]<2) ok=0;
        if(!ok) continue;
        for(int u=0;u<n;u++) if(S[j]>>u&1) cnt[u][i]--;
        T[j]&=~((u128)1<<i); cur--;
        if(T[j]==0){ cur-=pc(S[j])+2; alive[j]=0; S[j]=0; }
      } else {
        if(S[j]&~C[i]) continue;
        if(rnd01()>=padd) continue;
        for(int u=0;u<n;u++) if(S[j]>>u&1) cnt[u][i]++;
        T[j]|=(u128)1<<i; cur++;
      }
    }
    if(cur<best){best=cur;memcpy(bS,S,sizeof S);memcpy(bT,T,sizeof T);memcpy(bal,alive,sizeof alive);bnb=nb;}
  }
  f=fopen(argv[4],"w"); int m=0; long W=0;
  for(int j=0;j<bnb;j++) if(bal[j]){ fprintf(f,"B %016llx %016llx %016llx %016llx\n",(unsigned long long)(bS[j]>>64),(unsigned long long)bS[j],(unsigned long long)(bT[j]>>64),(unsigned long long)bT[j]); m++; W+=pc(bS[j])+pc(bT[j]); }
  fclose(f);
  printf("best cost %ld blocks %d weight %ld\n",best,m,W);
}
