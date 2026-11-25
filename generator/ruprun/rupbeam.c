// Short clause-learning (RUP) runs for the pigeonhole formula, by beam search.
// State: the clauses learned so far.  Candidates: every clause with at most S literals that is
// RUP now and has no proper subclause that is RUP now.  A state is scored by how many unit,
// binary (and ternary) clauses are RUP over it; the search stops when the empty clause is RUP.
// Usage: rupbeam <pigeons> <holes> <S> <beam width> <max length> <seed> [sample per state] [score: 0 counts, 1 search-tree size]
// RESULTS (25 Nov 2026): 4 pigeons 3 holes: 5 clauses.  5 pigeons 4 holes: 16 (the project reports 13).
// 6 pigeons 5 holes: nowhere near 40.  No step was proved with this.
// Output: the run found (one clause per line as literal numbers: variable = pigeon*holes+hole+1,
// negative = negated), then the empty clause.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
#define MAXC 512
static int M,H,NV,NL; static u64 rs;
static inline u64 rnd(){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
static inline u64 negm(u64 a){ return ((a&0x5555555555555555ULL)<<1)|((a>>1)&0x5555555555555555ULL); }
// literal index: 2*v for v true, 2*v+1 for v false
static int up(const u64*db,int n,u64 A){
  if(A&negm(A)) return 1;
  for(;;){ int ch=0; u64 nA=negm(A);
    for(int i=0;i<n;i++){ u64 c=db[i]; if(c&A) continue; u64 u=c&~nA; if(!u) return 1; if(!(u&(u-1))){ A|=u; nA=negm(A); ch=1; } }
    if(!ch) return 0; }
}
static inline int isrup(const u64*db,int n,u64 c){ return up(db,n,negm(c)); }
typedef struct { u64 db[MAXC]; int n; int nl; u64 lem[128]; double score; } St;
static int SCOREMODE=0; static long budget;
static u64 upA(const u64*db,int n,u64 A,int*conf){
  *conf=0; if(A&negm(A)){ *conf=1; return A; }
  for(;;){ int ch=0; u64 nA=negm(A);
    for(int i=0;i<n;i++){ u64 c=db[i]; if(c&A) continue; u64 u=c&~nA; if(!u){ *conf=1; return A; } if(!(u&(u-1))){ A|=u; nA=negm(A); ch=1; } }
    if(!ch) return A; }
}
// size of the plain search tree (no learning): branch on the literals of a shortest clause not yet satisfied
static long tree(const u64*db,int n,u64 A){
  int conf; A=upA(db,n,A,&conf); if(conf) return 1; if(--budget<0) return 1000000;
  u64 nA=negm(A); u64 best=0; int bl=99;
  for(int i=0;i<n;i++){ u64 c=db[i]; if(c&A) continue; u64 u=c&~nA; int l=__builtin_popcountll(u); if(l<bl){ bl=l; best=u; if(l==2) break; } }
  if(!best) return 1000000; // satisfiable branch: cannot happen for an unsatisfiable formula
  long s=1; u64 acc=A;
  while(best){ u64 l=best&-best; best^=l; s+=tree(db,n,acc|l); acc|=negm(l); if(s>=1000000) return 1000000; }
  return s;
}
static double score(const u64*db,int n){
  if(up(db,n,0)) return 1e18;
  if(SCOREMODE==1){ budget=3000000; return -(double)tree(db,n,0); }
  double s=0; int units=0,bins=0,ter=0;
  static char ur[64]; for(int a=0;a<NL;a++){ ur[a]=isrup(db,n,1ULL<<a); units+=ur[a]; }
  for(int a=0;a<NL;a++) if(!ur[a]) for(int b=a+1;b<NL;b++) if(!ur[b] && (a>>1)!=(b>>1)){ if(isrup(db,n,(1ULL<<a)|(1ULL<<b))) bins++; }
  s=units*1000.0+bins; (void)ter; return s;
}
static int cmp(const void*a,const void*b){ double x=((const St*)a)->score,y=((const St*)b)->score; return x<y?1:x>y?-1:0; }
int main(int argc,char**argv){
  M=atoi(argv[1]); H=atoi(argv[2]); int S=atoi(argv[3]); int BW=atoi(argv[4]); int maxlen=atoi(argv[5]); rs=strtoull(argv[6],0,10)*2654435761ULL+12345; int sample=argc>7?atoi(argv[7]):0; SCOREMODE=argc>8?atoi(argv[8]):0;
  NV=M*H; NL=2*NV; if(NL>64) return 2;
  St*beam=calloc(BW,sizeof(St)); St*next=calloc(BW*64+64,sizeof(St)); int nb=1;
  St*b0=&beam[0]; b0->n=0; b0->nl=0;
  for(int i=0;i<M;i++){ u64 c=0; for(int j=0;j<H;j++) c|=1ULL<<(2*(i*H+j)); b0->db[b0->n++]=c; }
  for(int j=0;j<H;j++) for(int a=0;a<M;a++) for(int b=a+1;b<M;b++) b0->db[b0->n++]=(1ULL<<(2*(a*H+j)+1))|(1ULL<<(2*(b*H+j)+1));
  static u64 cand[2000000];
  for(int step=1;step<=maxlen;step++){
    int nn=0; int perstate=64;
    for(int bi=0;bi<nb;bi++){ St*st=&beam[bi];
      // candidates: minimal RUP clauses with at most S literals
      int nc=0; static char ur[64]; static char br[64][64];
      for(int a=0;a<NL;a++){ ur[a]=isrup(st->db,st->n,1ULL<<a); if(ur[a]) cand[nc++]=1ULL<<a; }
      if(S>=2) for(int a=0;a<NL;a++) for(int b=a+1;b<NL;b++){ br[a][b]=0; if(ur[a]||ur[b]||(a>>1)==(b>>1)) continue; if(isrup(st->db,st->n,(1ULL<<a)|(1ULL<<b))){ br[a][b]=1; cand[nc++]=(1ULL<<a)|(1ULL<<b); } }
      if(S>=3) for(int a=0;a<NL;a++) if(!ur[a]) for(int b=a+1;b<NL;b++) if(!ur[b]&&!br[a][b]&&(a>>1)!=(b>>1)) for(int c=b+1;c<NL;c++) if(!ur[c]&&!br[a][c]&&!br[b][c]&&(a>>1)!=(c>>1)&&(b>>1)!=(c>>1)){
        u64 cl=(1ULL<<a)|(1ULL<<b)|(1ULL<<c); if(isrup(st->db,st->n,cl)) cand[nc++]=cl; }
      if(S>=4) for(int a=0;a<NL;a++) if(!ur[a]) for(int b=a+1;b<NL;b++) if(!ur[b]&&!br[a][b]&&(a>>1)!=(b>>1)) for(int c=b+1;c<NL;c++) if(!ur[c]&&!br[a][c]&&!br[b][c]&&(a>>1)!=(c>>1)&&(b>>1)!=(c>>1)) for(int d=c+1;d<NL;d++) if(!ur[d]&&!br[a][d]&&!br[b][d]&&!br[c][d]&&(a>>1)!=(d>>1)&&(b>>1)!=(d>>1)&&(c>>1)!=(d>>1)){
        u64 cl=(1ULL<<a)|(1ULL<<b)|(1ULL<<c)|(1ULL<<d);
        if(isrup(st->db,st->n,cl) && !isrup(st->db,st->n,cl&~(1ULL<<a)) && !isrup(st->db,st->n,cl&~(1ULL<<b)) && !isrup(st->db,st->n,cl&~(1ULL<<c)) && !isrup(st->db,st->n,cl&~(1ULL<<d))) cand[nc++]=cl; }
      // drop non-minimal ternaries (a binary subclause RUP was excluded above; units too)
      if(sample && nc>sample){ for(int i=0;i<sample;i++){ int j=i+rnd()%(nc-i); u64 t=cand[i]; cand[i]=cand[j]; cand[j]=t; } nc=sample; }
      // score each candidate; keep the best `perstate` of this state
      St*loc=&next[nn]; int nloc=0; double worst=-1; int wi=-1;
      for(int i=0;i<nc;i++){
        st->db[st->n]=cand[i]; double sc=score(st->db,st->n+1)+ (double)(rnd()%1000)/2000.0*(SCOREMODE==1?0.001:1);
        if(nloc<perstate){ St*t=&loc[nloc++]; memcpy(t->db,st->db,sizeof(u64)*(st->n+1)); t->n=st->n+1; memcpy(t->lem,st->lem,sizeof(u64)*st->nl); t->lem[st->nl]=cand[i]; t->nl=st->nl+1; t->score=sc; }
        else { if(wi<0){ worst=1e30; for(int k=0;k<nloc;k++) if(loc[k].score<worst){ worst=loc[k].score; wi=k; } }
          if(sc>worst){ St*t=&loc[wi]; memcpy(t->db,st->db,sizeof(u64)*(st->n+1)); t->n=st->n+1; memcpy(t->lem,st->lem,sizeof(u64)*st->nl); t->lem[st->nl]=cand[i]; t->nl=st->nl+1; t->score=sc; wi=-1; } }
      }
      nn+=nloc;
    }
    if(nn==0){ printf("STUCK at step %d\n",step); return 1; }
    qsort(next,nn,sizeof(St),cmp);
    // remove duplicate states (same set of lemmas)
    nb=0; for(int i=0;i<nn&&nb<BW;i++){ int dup=0; for(int k=0;k<nb&&!dup;k++){ if(beam[k].nl!=next[i].nl) continue; int same=1; for(int x=0;x<next[i].nl&&same;x++){ int f=0; for(int y=0;y<beam[k].nl;y++) if(beam[k].lem[y]==next[i].lem[x]) f=1; same=f; } dup=same; } if(!dup) beam[nb++]=next[i]; }
    fprintf(stderr,"step %d: states %d best score %.1f\n",step,nb,beam[0].score);
    if(beam[0].score>=1e17){ St*st=&beam[0]; printf("FOUND length %d (with the empty clause)\n",st->nl+1);
      for(int i=0;i<st->nl;i++){ for(int l=0;l<NL;l++) if(st->lem[i]>>l&1) printf("%d ",(l&1)?-(l/2+1):(l/2+1)); printf("0\n"); }
      printf("0\n"); return 0; }
  }
  printf("NOTFOUND within %d\n",maxlen); return 1;
}
