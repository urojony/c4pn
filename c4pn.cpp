#include<vector>
#include<array>
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
constexpr int T_MAX=12,T2_MAX=6;
///Parameters of considered games - the T-th game
///is played on V[T] vertices, the goal for the builder is to build
///a red C4 or a blue path of length N[T] in E[T] moves.
///N should be sorted in nondescending order for faster performance
///For any T, V[T]>N[T] (otherwise Painter wins trivially or easy)
constexpr int V[]={4,5,6,7,8,8,9,10,11,12,13,14},
E[]={6,8,9,11,13,12,14,16,18,20,22,24},N[]={3,4,5,6,7,7,8,9,10,11,12,13};
///Vmax has to be the biggest number in V[0],V[1],...,V[Vmax-1]
///If it's not V[Tmax-1], change manually
constexpr int V_MAX=V[T_MAX-1],V_MAX_SQ=V_MAX*V_MAX;
int T=0;
///will be treated as Vmax*Vmax matrix (usually representing a graph)
typedef bitset<V_MAX_SQ> matrix;
///list of starting positions: j-th position is stored in RED_EDGES[j]
///and BLUE_EDGES[j], each edge is stored as two consecutive numbers
///so e.g. {0,1,2,3} means two edges: 0-1 and 2-3;
///if a position is not possible in a given game, it will be ignored
///for example if V[0]=4 (so the set of vertices={0,1,2,3}) then all
///positions in the 0-th game which contains a vertex 4 will be ignored
const vector<int> RED_EDGES[] {{},{},{1,2},{1,2,2,3},{1,2},{1,2,2,3}},
BLUE_EDGES[] {{},{0,1},{0,1},{0,1},{0,1,2,3},{0,1,3,4}};
#define ST first
#define ND second

///map of all analysed positions with builder to move
///key=position
///value=0 if builder has no winning move or (v1<<8)+v2 if (v1,v2) is winning
unordered_map<matrix,int> ANAL_POS[T_MAX];
matrix strictlyLowerTriangularMask() {
   matrix low;
   for(int i=1;i<V_MAX;++i)
      for(int j=0;j<i;++j)
         low[i*V_MAX+j]=1;
   return low;
}
const matrix LOWER_MASK=strictlyLowerTriangularMask();
matrix strictlyUpperTriangularMask(){
   matrix upp;
   for(int i=0;i<V_MAX;++i)
      for(int j=i+1;j<V_MAX;++j)
         upp[i*V_MAX+j]=1;
   return upp;
}
const matrix UPPER_MASK=strictlyUpperTriangularMask();
const array<matrix,V_MAX> verticesMasks(){
///masks for each row of a matrix
   array<matrix,V_MAX> ver;
   int i=0;
   for(i=0;i<V_MAX;++i)
      ver[0][i]=1;
   for(i=1;i<V_MAX;++i)
      ver[i]=ver[i-1]<<V_MAX;
   return ver;
}
const array<matrix,V_MAX> ROW_MASKS=verticesMasks();
int degree(matrix& graph,int v){
   return (graph&ROW_MASKS[v]).count();
}
struct Graph{
   matrix m; ///adjacency matrix
   int e=0; ///number of edges
   void addEdge(int v1,int v2){
      m[v1*V_MAX+v2]=m[v2*V_MAX+v1]=1;
      ++e;
   }
   void removeEdge(int v1,int v2){
      m[v1*V_MAX+v2]=m[v2*V_MAX+v1]=0;
      --e;
   }
   void clear(){
      m.reset();
      e=0;
   }
   int degree(int v){
      return ::degree(m,v);
   }
};

void reorder(matrix &graph,int invOrder[]){
///reorders vertices in a graph - useful for decreasing
///the number of unique positions in the game
   matrix res;
   for(int i=graph._Find_first();i<V_MAX_SQ;i=graph._Find_next(i))
      res[invOrder[i/V_MAX]*V_MAX+invOrder[i%V_MAX]]=1;
   graph=res;
}
matrix sortAndMerge
(matrix blueG,matrix redG,int v,int invOrder[],pair<int,int> order[]){
///sorts vertices of matrices by blue degree, then by red degree
///after that it merges two matrices into one
///it sends back the merged matrix and the order of sorting
   int i;
   for(i=0;i<v;++i)
      order[i]={-degree(blueG,i)*4194304-degree(redG,i)*65536,i};
   sort(order,order+v);
   for(i=0;i<v;++i)
      invOrder[order[i].ND]=i;
   reorder(blueG,invOrder);
   reorder(redG,invOrder);
   return (blueG&LOWER_MASK) | (redG&UPPER_MASK);
}
bool isPnPath(matrix graph){
///if there is an exactly one path of length Nt[T] and
///no other edges, returns 1,
///if there is no path of length Nt[T], returns 0,
///otherwise it can return any value
   //return 1; ///if Vt[T]==Nt[T]+1, it should always return 1 when invoked
   int i,j,k,len=0;
   for(i=0;i<V[T];++i)
      if(degree(graph,i)==1)
         break;
   if(i==V[T])
      return 0;
   for(j=i;;){
      k=graph._Find_next(j*V_MAX-1)-j*V_MAX;
      if(k>=V_MAX)
         break;
      graph[j*V_MAX+k]=graph[k*V_MAX+j]=0;
      ++len;
      j=k;
   }
   return len+1==N[T];
}
bool hasC4(Graph& graph,int i,int j){
///checks if graph has a C4 cycle which contains i-j edge
   if(graph.e<3)
      return 0;
   auto graph2=graph.m&ROW_MASKS[i];
   ///macro for iterating a bitset over interval [beg,end)
   #define FOR_BS(i,bset,beg,end)\
   for(int i=(bset)._Find_next((beg)-1);i<end;i=(bset)._Find_next(i))
   FOR_BS(k,graph.m,j*V_MAX,j*V_MAX+i){
      if(((graph2>>((i-k+j*V_MAX)*V_MAX))&graph.m).count()>1)
         return 1;
   }
   FOR_BS(k,graph.m,j*V_MAX+i+1,j*V_MAX+V_MAX){
      if(((graph2<<((k-j*V_MAX-i)*V_MAX))&graph.m).count()>1)
         return 1;
   }
   return 0;
}
bool hasOnlyPaths(matrix graph,int v1,int v2){
///assuming graph contains only disjoint paths, check if
///the edge v1-v2 doesn't destroy this property
   int j,k;
   const int d1=degree(graph,v1),d2=degree(graph,v2);
   if(d1>1 || d2>1)
      return 0;
   if(d1==0 || d2==0){
      return 1;
   }
   for(j=v1;;){
      k=graph._Find_next(j*V_MAX-1)-j*V_MAX;
      if(k>=V_MAX)
         break;
      graph[j*V_MAX+k]=graph[k*V_MAX+j]=0;
      j=k;
   }
   return j!=v2;
}
int NUM_OF_UNIQ_POS=0,NUM_OF_ALL_POS=0;
bool colour(Graph blueG,Graph redG,int v,int i,int j);
bool construct(Graph blueG,Graph redG,int v){
///returns 1 iff builder has a winning move
   if(blueG.e>=N[T] || redG.e>E[T]-N[T]+1)
      return 0;
   int invOrder[v+3];
   pair<int,int> order[v+3];
   auto sPos=sortAndMerge(blueG.m,redG.m,v,invOrder,order);
   ++NUM_OF_ALL_POS;
   if(ANAL_POS[T].count(sPos))
      return ANAL_POS[T][sPos];
   ++NUM_OF_UNIQ_POS;
   if((NUM_OF_UNIQ_POS&((1<<23)-1))==0)
      printf("Unique positions analysed so far: %d\n",NUM_OF_UNIQ_POS);
   if(blueG.e+redG.e==E[T])
      return 0;
   order[v].ND=v;
   order[v+1].ND=v+1;
   matrix checked=blueG.m|redG.m;
   if(T>0 && ANAL_POS[T-1].count(sPos) && ANAL_POS[T-1][sPos]){
   ///checks if in the previous game this position was reached
      int moove=ANAL_POS[T-1][sPos];
      int v1=order[moove>>8].ND,v2=order[moove&255].ND;
      if(colour(blueG,redG,max({v,v1+1,v2+1}),v1,v2)){
      ///try to play the same move
         ANAL_POS[T][sPos]=moove;
         return 1;
      }
      else
         checked[v1*V_MAX+v2]=checked[v2*V_MAX+v1]=1;
   }
   ///try moves with vertices that already have edges
   for(int i=v-1;i>=0;--i)
      if(blueG.degree(i)<=1)
         for(int j=v-1;j>i;--j)
            if(!checked[i*V_MAX+j] && blueG.degree(j)<=1){
               if(colour(blueG,redG,v,i,j)){
                  ANAL_POS[T][sPos]=(invOrder[i]<<8)+invOrder[j];
                  return 1;
               }
               else
                  checked[i*V_MAX+j]=checked[j*V_MAX+i]=1;
            }
   ///try moves with an unused vertice
   if(v<V[T])
      for(int i=0;i<v;++i){
         if(blueG.degree(i)<=1&& !checked[i*V_MAX+v]
         && colour(blueG,redG,v+1,i,v)){
            ANAL_POS[T][sPos]=(invOrder[i]<<8)+v;
            return 1;
         }
      }
   ///the first move has two unused vertices
   if(v==0 && colour(blueG,redG,v+2,v,v+1)){
      ANAL_POS[T][sPos]=(v<<8)+v+1;
      return 1;
   }
   ANAL_POS[T][sPos]=0;
   return 0;
}
void print(const matrix& mergedG,int moove){
   printf("r: ");
   int i,j;
   for(i=0;i<V_MAX;++i)
      for(j=i+1;j<V_MAX;++j)
         if(mergedG[i*V_MAX+j])
            printf("%X%X ",i,j);
   printf("b: ");
   for(i=1;i<V_MAX;++i)
      for(j=0;j<i;++j)
         if(mergedG[i*V_MAX+j])
            printf("%X%X ",i,j);
   printf("m: %X%X\n",moove>>8,moove&255);
}
void print(const matrix& blueG,const matrix& redG,
            int moove,FILE *fp,bool newline=1){
   fprintf(fp,"r: ");
   int i,j;
   for(i=0;i<V_MAX;++i)
      for(j=i+1;j<V_MAX;++j)
         if(redG[i*V_MAX+j])
            fprintf(fp,"%X%X ",i,j);
   fprintf(fp,"b: ");
   for(i=0;i<V_MAX;++i)
      for(j=i+1;j<V_MAX;++j)
         if(blueG[i*V_MAX+j])
            fprintf(fp,"%X%X ",i,j);
   fprintf(fp,"m: %X%X",moove>>8,moove&255);
   if(newline)
      fprintf(fp,"\n");
}
bool colour(Graph blueG,Graph redG,int v,int i,int j){
///returns 0 iff painter has a winning move
   if(!hasOnlyPaths(blueG.m,i,j))
      return 0;
   blueG.addEdge(i,j);
   bool isVertexWithoutBlueEdges=0;
   for(int i=V[T]-1;i>=0;--i)
      if(blueG.degree(i)==0){
         isVertexWithoutBlueEdges=1;
         break;
      }
   if(!isVertexWithoutBlueEdges) ///if all vertices have blue edges,
      return 0; ///then at least one edge will be wasted
   ///paint i-j red and check who's winning
   blueG.removeEdge(i,j);
   redG.addEdge(i,j);
   if(!hasC4(redG,i,j) && !construct(blueG,redG,v)){
      return 0;
   }
   ///paint i-j blue and check who's winning
   redG.removeEdge(i,j);
   blueG.addEdge(i,j);
   if((blueG.e+2<N[T] || !isPnPath(blueG.m))&& !construct(blueG,redG,v)){
      return 0;
   }
   return 1;
}
unordered_map<matrix,int> BOOK_POS;
int LINE_NUMBER;
void printBook(Graph blueG,Graph redG,int v,int e,FILE *fp){
   int invOrder[v+3];
   pair<int,int> order[v+3];
   auto sPos=sortAndMerge(blueG.m,redG.m,v,invOrder,order);
   order[v].ND=v;
   order[v+1].ND=v+1;
   if(!ANAL_POS[T].count(sPos)){
      construct(blueG,redG,v);
   }
   int i,j,moove;
   moove=ANAL_POS[T][sPos];
   if(moove==0){
      printf("Can't find winning strategy for Builder\n");
      exit(2137); ///this shouldn't happen
   }
   i=moove/256;
   j=moove%256;
   i=order[i].ND;
   j=order[j].ND;
   for(int h=0;h<e;++h)
      fprintf(fp," ");
   print(blueG.m,redG.m,i*256+j,fp,0);
   if(BOOK_POS.count(sPos)){
      fprintf(fp," l: %d\n",BOOK_POS[sPos]);
      ++LINE_NUMBER;
      return;
   }
   else{
      fprintf(fp,"\n");
      BOOK_POS[sPos]=++LINE_NUMBER;
   }
   blueG.addEdge(i,j);
   if(!isPnPath(blueG.m))
      printBook(blueG,redG,max({v,i+1,j+1}),e+1,fp);
   blueG.removeEdge(i,j);
   redG.addEdge(i,j);
   if(!hasC4(redG,i,j))
      printBook(blueG,redG,max({v,i+1,j+1}),e+1,fp);
}
int fillGraph(Graph& blueG,Graph& redG,const int t2){
   blueG.clear();
   redG.clear();
   for(int i=1;i<(int)BLUE_EDGES[t2].size();i+=2)
      blueG.addEdge(BLUE_EDGES[t2][i],BLUE_EDGES[t2][i-1]);
   for(int i=1;i<(int)RED_EDGES[t2].size();i+=2)
      redG.addEdge(RED_EDGES[t2][i],RED_EDGES[t2][i-1]);
   int mxVertexIndex=-1;
   for(int i:BLUE_EDGES[t2])
      mxVertexIndex=max(i,mxVertexIndex);
   for(int i:RED_EDGES[t2])
      mxVertexIndex=max(i,mxVertexIndex);
   return mxVertexIndex;
}
int main(){
   Graph blueG,redG;
   FILE *fp;
   for(T=0;T<T_MAX;++T){
      BOOK_POS.clear();
      LINE_NUMBER=0;
      char filename[100];
      char names[6][20]={"empty","b-path","br-path",
      "brr-path","brb-path","brrb-path"};
      sprintf(filename,"C4P%d_in_%d_moves_%d_verts.txt",N[T],E[T],V[T]);
      fp=fopen(filename,"w");
      for(int t2=0;t2<T2_MAX;++t2){
         int mxVertexIndex=fillGraph(blueG,redG,t2);
         if(mxVertexIndex>=V[T])
            continue;
         int result=construct(blueG,redG,mxVertexIndex+1);
         fprintf(fp,"rc(C4,P%d,%s,%d,%d)=%d\n",N[T],names[t2],V[T],E[T],result);
         printf("rc(C4,P%d,%s,%d,%d)=%d\n",N[T],names[t2],V[T],E[T],result);
         printf("unique/total positions analysed: ");
         printf("%d %d\n",NUM_OF_UNIQ_POS,NUM_OF_ALL_POS);
         ++LINE_NUMBER;
         if(result)
            printBook(blueG,redG,mxVertexIndex+1,
               BLUE_EDGES[t2].size()/2+RED_EDGES[t2].size()/2,fp);
      }
      fclose(fp);
   }
}
