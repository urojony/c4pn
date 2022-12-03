#include<vector>
#include<bitset>
#include<set>
#include<unordered_set>
#include<unordered_map>
#include<algorithm>
#include<cstdio>
#include<string>
#include<map>
using namespace std;
///Tmax - number of considered games
///T2max - number of considered starting positions in each game
const int Tmax=12,T2max=6;
///Parameters of considered games - the T-th game
///is played on V[T] vertices, the goal for the builder is to build
///a red C4 or a blue path of length N[T] in E[T] moves
///N should be sorted in nondescending order for faster performance
const int V[]={4,5,6,7,8,8,9,10,11,12,13,14},
E[]={6,8,9,11,13,12,14,16,18,20,22,24},N[]={3,4,5,6,7,7,8,9,10,11,12,13};
///Vmax has to be the biggest number in V[0],V[1],...,V[Vmax-1]
///If it's not V[Tmax-1], change manually
const int Vmax=V[Tmax-1],Vmax2=Vmax*Vmax;
int T=0,T2=0;
///will be treated as Vmax*Vmax matrix (usually representing a graph)
typedef bitset<Vmax2> matrix;
///list of starting positions: j-th position is stored in rededges[j]
///and blueedges[j], each edge is stored as two consecutive numbers
///so e.g. {0,1,2,3} means two edges: 0-1 and 2-3;
///if a position is not possible in a given game, it will be ignored
///for example if V[0]=4 (so the set of vertices={0,1,2,3}) then all
///positions in the 0-th game which contains a vertex 4 will be ignored
vector<int> rededges[] {{},{},{1,2},{1,2,2,3},{1,2},{1,2,2,3}},
blueedges[] {{},{0,1},{0,1},{0,1},{0,1,2,3},{0,1,3,4}};
struct Graph{
   matrix m;
   int e;
   void addedge(int i,int j){
      m[i*Vmax+j]=m[j*Vmax+i]=1;
      ++e;
   }
   void removeedge(int i,int j){
      m[i*Vmax+j]=m[j*Vmax+i]=0;
      --e;
   }
   void clear(){
      m.reset();
      e=0;
   }
};

#define ST first
#define ND second
///macros for iterating a bitset for intervals [0,end) or [beg,end)
#define FOR2(i,bset,end)\
for(int i=(bset)._Find_first();i<(end);i=(bset)._Find_next(i))
#define FOR3(i,bset,beg,end)\
for(int i=(bset)._Find_next((beg)-1);i<end;i=(bset)._Find_next(i))
#define ALL(c) (c).begin(),(c).end()
///map of all analysed positions with builder to move
///key=position
///value=0 if builder has no winning move or (v1<<8)+v2 if (v1,v2) is winning
unordered_map<matrix,int> pos[Tmax];
matrix masklower() {
///lower triangular mask (without the diagonal)
   matrix low;
   for(int i=1;i<Vmax;++i)
      for(int j=0;j<i;++j)
         low[i*Vmax+j]=1;
   return low;
}
const matrix maskl=masklower();
matrix maskupper(){
///upper triangular mask
   matrix upp;
   for(int i=0;i<Vmax;++i)
      for(int j=i+1;j<Vmax;++j)
         upp[i*Vmax+j]=1;
   return upp;
}
const matrix masku=maskupper();
array<matrix,Vmax> maskvertice(){
///masks for each row of a matrix
   array<matrix,Vmax> ver;
   int i=0;
   for(i=0;i<Vmax;++i)
      ver[0][i]=1;
   for(i=1;i<Vmax;++i)
      ver[i]=ver[i-1]<<Vmax;
   return ver;
}
const array<matrix,Vmax> maskrow=maskvertice();
void reorder(matrix &graph,int iorder[]){
///reorders vertices in a graph - useful for decreasing
///the number of unique positions in the game
   matrix res;
   FOR2(i,graph,Vmax2)
      res[iorder[i/Vmax]*Vmax+iorder[i%Vmax]]=1;
   graph=res;
}
int degree(matrix &graph,int i){
   return (graph&maskrow[i]).count();
}
matrix srtedpos
(matrix blueG,matrix redG,int v,int iorder[],pair<int,int> order[]){
///sorts vertices of matrices by blue degree, then by red degree
///after that it merges two matrices into one
///it sends back the merged matrix and the order of sorting
   int i;
   for(i=0;i<v;++i)
      order[i]={-degree(blueG,i)*4194304-degree(redG,i)*65536,i};
   sort(order,order+v);
   for(i=0;i<v;++i)
      iorder[order[i].ND]=i;
   reorder(blueG,iorder);
   reorder(redG,iorder);
   return (blueG&maskl) | (redG&masku);
}
bool path(matrix graph){
///if there is an exactly one path of length Nt[T] and
///no other edges, returns 1,
///if there is no such path, returns 0,
///otherwise it can return any value
   //return 1; ///if Vt[T]==Nt[T]+1, it should always return 1 when invoked
   int i,j,k,len=0;
   for(i=0;i<V[T];++i)
      if(degree(graph,i)==1)
         break;
   if(i==V[T])
      return 0;
   for(j=i;;){
      k=graph._Find_next(j*Vmax-1)-j*Vmax;
      if(k>=Vmax)
         break;
      graph[j*Vmax+k]=graph[k*Vmax+j]=0;
      ++len;
      j=k;
   }
   return len+1==N[T];
}
bool c4(Graph& graph,int i,int j){
///checks if graph has a C4 cycle which contains i-j edge
   if(graph.e<3)
      return 0;
   auto graph2=graph.m&maskrow[i];
   FOR3(k,graph.m,j*Vmax,j*Vmax+i){
      if(((graph2>>((i-k+j*Vmax)*Vmax))&graph.m).count()>1)
         return 1;
   }
   FOR3(k,graph.m,j*Vmax+i+1,j*Vmax+Vmax){
      if(((graph2<<((k-j*Vmax-i)*Vmax))&graph.m).count()>1)
         return 1;
   }
   return 0;
}
bool onlypaths(matrix graph,int v1,int v2){
///assuming graph contains only paths, check if
///the edge v1-v2 doesn't destroy this property
   int j,k;
   const int d1=degree(graph,v1),d2=degree(graph,v2);
   if(d1>1 || d2>1)
      return 0;
   if(d1==0 || d2==0){
      return 1;
   }
   for(j=v1;;){
      k=graph._Find_next(j*Vmax-1)-j*Vmax;
      if(k>=Vmax)
         break;
      graph[j*Vmax+k]=graph[k*Vmax+j]=0;
      j=k;
   }
   return j!=v2;
}
int uniq_pos=0,all_pos=0;
bool colour(Graph blueG,Graph redG,int v,int i,int j);
bool construct(Graph blueG,Graph redG,int v){
///returns 1 iff builder has a winning move
   if(blueG.e>=N[T] || redG.e>E[T]-N[T]+1)
      return 0;
   int iorder[v+3];
   pair<int,int> order[v+3];
   auto spos=srtedpos(blueG.m,redG.m,v,iorder,order);
   ++all_pos;
   if(pos[T].count(spos))
      return pos[T][spos];
   ++uniq_pos;
   if((uniq_pos&((1<<23)-1))==0)
      printf("Unique positions analysed so far: %d\n",uniq_pos);
   if(blueG.e+redG.e==E[T])
      return 0;
   order[v].ND=v;
   order[v+1].ND=v+1;
   matrix checked=blueG.m|redG.m;
   if(T>0 && pos[T-1].count(spos) && pos[T-1][spos]){
   ///checks if in the previous game this position was reached
      int mv=pos[T-1][spos];
      int v1=order[mv>>8].ND,v2=order[mv&255].ND;
      if(colour(blueG,redG,max({v,v1+1,v2+1}),v1,v2)){
      ///try to play the same move
         pos[T][spos]=mv;
         return 1;
      }
      else
         checked[v1*Vmax+v2]=checked[v2*Vmax+v1]=1;
   }
   ///try moves with vertices that already have edges
   for(int i=v-1;i>=0;--i)
      if(degree(blueG.m,i)<=1)
         for(int j=v-1;j>i;--j)
            if(!checked[i*Vmax+j] && degree(blueG.m,j)<=1  ){
               if(colour(blueG,redG,v,i,j)){
                  pos[T][spos]=(iorder[i]<<8)+iorder[j];
                  return 1;
               }
               else
                  checked[i*Vmax+j]=checked[j*Vmax+i]=1;
            }
   ///try moves with an unused vertice
   if(v<V[T])
      for(int i=0;i<v;++i){
         if(degree(blueG.m,i)<=1&& !checked[i*Vmax+v]
         && colour(blueG,redG,v+1,i,v)){
            pos[T][spos]=(iorder[i]<<8)+v;
            return 1;
         }
      }
   ///the first move has two unused vertices
   if(v==0 && colour(blueG,redG,v+2,v,v+1)){
      pos[T][spos]=(v<<8)+v+1;
      return 1;
   }
   pos[T][spos]=0;
   return 0;
}
void print(const matrix& mergedG,int mv){
   printf("r: ");
   int i,j;
   for(i=0;i<Vmax;++i)
      for(j=i+1;j<Vmax;++j)
         if(mergedG[i*Vmax+j])
            printf("%X%X ",i,j);
   printf("b: ");
   for(i=1;i<Vmax;++i)
      for(j=0;j<i;++j)
         if(mergedG[i*Vmax+j])
            printf("%X%X ",i,j);
   printf("m: %X%X\n",mv>>8,mv&255);
}
FILE *fp;
void print(const matrix& blueG,const matrix& redG,int mv,bool nl=1){
   fprintf(fp,"r: ");
   int i,j;
   for(i=0;i<Vmax;++i)
      for(j=i+1;j<Vmax;++j)
         if(redG[i*Vmax+j])
            fprintf(fp,"%X%X ",i,j);
   fprintf(fp,"b: ");
   for(i=0;i<Vmax;++i)
      for(j=i+1;j<Vmax;++j)
         if(blueG[i*Vmax+j])
            fprintf(fp,"%X%X ",i,j);
   fprintf(fp,"m: %X%X",mv>>8,mv&255);
   if(nl)
      fprintf(fp,"\n");
}
bool colour(Graph blueG,Graph redG,int v,int i,int j){
///returns 0 iff painter has a winning move
   if(!onlypaths(blueG.m,i,j))
      return 0;
   blueG.addedge(i,j);
   int mindeg=1;
   for(int i=V[T]-1;i>=0;--i)
      if(degree(blueG.m,i)==0){
         mindeg=0;
         break;
      }
   if(mindeg) ///if all vertices have blue edges,
      return 0; ///then at least one edge will be wasted
   ///paint i-j red and check who's winning
   blueG.removeedge(i,j);
   redG.addedge(i,j);
   if(!c4(redG,i,j) && !construct(blueG,redG,v)){
      return 0;
   }
   ///paint i-j blue and check who's winning
   redG.removeedge(i,j);
   blueG.addedge(i,j);
   if((blueG.e+2<N[T] || !path(blueG.m))&& !construct(blueG,redG,v)){
      return 0;
   }
   return 1;
}
unordered_map<matrix,int> bookpos;
int num;
void printbook(Graph blueG,Graph redG,int v,int e){
   int iorder[v+3];
   pair<int,int> order[v+3];
   auto spos=srtedpos(blueG.m,redG.m,v,iorder,order);
   order[v].ND=v;
   order[v+1].ND=v+1;
   if(!pos[T].count(spos)){
      construct(blueG,redG,v);
   }

   int i,j,mv;
   mv=pos[T][spos];
   if(mv==0){
      print(blueG.m,redG.m,0);
      ++num;
      if(N[T]>=8)
         exit(0);
      else
         return;
   }
   i=mv/256;
   j=mv%256;
   i=order[i].ND;
   j=order[j].ND;
   for(int h=0;h<e;++h)
      fprintf(fp," ");
   print(blueG.m,redG.m,i*256+j,0);
   if(bookpos.count(spos)){
      fprintf(fp," l: %d\n",bookpos[spos]);
      ++num;
      return;
   }
   else{
      fprintf(fp,"\n");
      bookpos[spos]=++num;
   }
   blueG.addedge(i,j);
   if(!path(blueG.m))
      printbook(blueG,redG,max({v,i+1,j+1}),e+1);
   blueG.removeedge(i,j);
   redG.addedge(i,j);
   if(!c4(redG,i,j))
      printbook(blueG,redG,max({v,i+1,j+1}),e+1);
}
int fillgraph(Graph& blueG,Graph& redG){
   blueG.clear();
   redG.clear();
   for(int i=1;i<(int)blueedges[T2].size();i+=2)
      blueG.addedge(blueedges[T2][i],blueedges[T2][i-1]);
   for(int i=1;i<(int)rededges[T2].size();i+=2)
      redG.addedge(rededges[T2][i],rededges[T2][i-1]);
   int m=-1;
   for(int i:blueedges[T2])
      m=max(i,m);
   for(int i:rededges[T2])
      m=max(i,m);
   return m;
}
int main(){
   Graph blueG,redG;
   for(T=0;T<Tmax;++T){
      bookpos.clear();
      num=0;
      char filename[100];
      char names[6][20]={"empty","b-path","br-path",
      "brr-path","brb-path","brrb-path"};
      sprintf(filename,"C4P%d_in_%d_moves_%d_verts.txt",N[T],E[T],V[T]);
      fp=fopen(filename,"w");
      for(T2=0;T2<T2max;++T2){
         int m=fillgraph(blueG,redG);
         if(m>=V[T])
            continue;
         int result=construct(blueG,redG,m+1);
         fprintf(fp,"rc(C4,P%d,%s,%d,%d)=%d\n",N[T],names[T2],V[T],E[T],result);
         printf("rc(C4,P%d,%s,%d,%d)=%d\n",N[T],names[T2],V[T],E[T],result);
         printf("unique/total positions analysed: %d %d\n",uniq_pos,all_pos);
         ++num;
         printbook(blueG,redG,m+1,blueedges[T2].size()/2+rededges[T2].size()/2);
      }
      fclose(fp);
   }
}
