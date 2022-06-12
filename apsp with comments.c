/*************************************************************************************/
/** This program contains the followings:                                           **/
/**  1) Random graph generator                                                      **/
/**  2) Dijkstra's alg. for APSP problem                                            **/
/**  3) Johnson's alg. for APSP problem                                             **/
/**  4) Floyd-Warshall alg. for APSP problem                                        **/
/**  5) Improved FW alg. for APSP problem                                           **/
/**  The same graphs are used as input to all algs.                                 **/
/**  NO INPUT                                                                       **/
/** The followings can be changed                                                   **/
/**  #define MAXN 4097   // max number of vertices                                  **/
/** #define INF 9999        // infinite                                             **/ 
/**  N=1024;  // number of vertices in the graph                                    **/
/**  OUTPUT: Execution times & # operations                                         **/
/** Algorithms are implemented to satisfy complexities                              **/
/** Implementation structure is not optimized                                       **/
/** Dijkstra's alg has 2 implementations (one for Johnson's alg)                    **/
/** Memory usage is not optimized                                                   **/
/** Different adj matrices are allocated for different algs                         **/
/**                                                                                 **/
/** Written by: Ismail Hakki Toroslu  (June 2022)                                   **/
/*************************************************************************************/

#include <time.h>
#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#define MAXN 4097   // max number of vertices is 4098
#define INF 9999        // infinite is represented by 9999

clock_t start_s, stop_s; // to determine start and end times

// adjacency matrix of graph
int G[MAXN][MAXN];  

// to create a linked list for adjacency list representation 
// neighbour: linked list element; v: vertex id, w: edge weight
struct neighbour { int v; int w; struct neighbour* n; };
// adjacency list of a vertex with pointers to the first and the last element
struct vertex { int odegree; struct neighbour *first, *last;};
// array of adjaceny lists
struct vertex Graph [MAXN];

// vertex with min distance val and its id
struct min_vertex {int val, id;};

// swap fun
void swap(int *a, int *b){int t=*a; *a=*b; *b=t;}

/************** DIJKSTRA'S ALG. *****************/

// distance and parent arrays
int distance[MAXN],  parent[MAXN];
// APSP distances are stored
int APSPD[MAXN][MAXN];
// to count the number of operations
long long int count_dijkstra=0;

// heap implementation: index 0 is not used
// heap values, positions in the position array, position of keys of index 1 to N in heap
int heap_val[MAXN], heap_pos[MAXN], position[MAXN];

// decrease the value at postion i to a new value
void decreasekey_heap(int i, int new_value)
{
    int k1;
    int k=position[i]; // position in a heap
    heap_val[k]=new_value;
    while (k>1)
    {
        count_dijkstra++; // each comparision is counted
        k1=k / 2; //parent
        if (heap_val[k1]>heap_val[k])
        {
            swap(&position[heap_pos[k1]],&position[heap_pos[k]]);
            swap(&heap_val[k1],&heap_val[k]);
            swap(&heap_pos[k1],&heap_pos[k]);
        }
        else break;
        k=k1;
    }
}

// add a new value to a heap
void addkey_heap(int i, int new_value, int *heap_size)
{
    (*heap_size)++;
    int k=*heap_size;
    position[i]=k;
    heap_val[k]=new_value;
    heap_pos[k]=i;
    decreasekey_heap(i,new_value);
}

// delete the root of the heap and return the structure with its value and id
struct min_vertex deletemin_heap(int *heap_size)
{
    int k1, k2, k=1;
    struct min_vertex r;
    r.val=heap_val[k];
    r.id=heap_pos[k];
    heap_val[k]=heap_val[*heap_size];
    heap_pos[k]=heap_pos[*heap_size];
    position[heap_pos[k]]=k;


    (*heap_size)--;
    while (k<*heap_size)
    {
        count_dijkstra++;  // each comparision is counted
        k1=2*k; k2=2*k+1; //children
        if (k1>*heap_size) break;
        if (k2<=*heap_size)
            if (heap_val[k2]<heap_val[k1]) k1=k2;
        if (heap_val[k1]<heap_val[k])
        {
            swap(&position[heap_pos[k1]],&position[heap_pos[k]]);
            swap(&heap_val[k1],&heap_val[k]);
            swap(&heap_pos[k1],&heap_pos[k]);
        }
        else break;
        k=k1;
    }
    return r;
}

// copy the results of Dijkstra's alg (from S to all vertices) into APSP array
void apspd( int V, int S)
{
    int i ;
    for ( i = 1 ; i <= V ; i++ )
        APSPD[S][i]=distance[i];
}

// the main function of Dijkstra's alg.
// determine SP from S to all vertices (V: number of vertices)
void dijkstra ( int S , int V )
{
    int u;
    struct min_vertex r;
    int N=V;
    while( N >0 )
    {
        r=deletemin_heap(&N);
        u=r.id;
        distance[u]=r.val;
        for (struct neighbour *t=Graph[u].first; t!=NULL;t=t->n)
        {
                if ((distance[u]!=INF)&&( distance[u] + t->w < distance[t->v]))
                    decreasekey_heap(t->v,distance[u] + t->w ), distance[t->v]=distance[u]+t->w, parent[t->v] = u ;
        }
    }
    apspd(V,S);
}

// in order to apply Dijkstra's alg.
// initialize heap, then call it for the vertex S
void  main_Dijkstra(int V, int S)
{
    int i;
    int N=0;

    for ( i = 1 ; i <= V ; i++ )
        addkey_heap(i,INF,&N), distance[i] = INF , parent[i] = -1 ;

    decreasekey_heap(S,0);
    distance[S] = 0 ;
    dijkstra (S, V) ;

}

/*******  JOHNSON'S ALG *****************/

// distance and parent arrays for Dijkstra's alg, h array of Johnson's alg.
int jdistance[MAXN],  jparent[MAXN], h[MAXN] ;
// APSP array for Dijkstra's alg, used in Johnson's alg and APSP array for Johnson's alg.
int jAPSPD[MAXN][MAXN], APSPJ[MAXN][MAXN];

// to count the number of operations (Dijkstra part, Bellman-Ford subpart and whole Johnson's alg.)
long long int jcount_dijkstra=0, count_bf=0, count_johnson=0;

/*** DIJKSTRA'S ALG. IMPLEMENTATION IS REPEATED WITH ONLY NAME CHANGE (starting with j) ***/

// heap implementation: index 0 is not used
// heap values, positions in the position array, position of keys of index 1 to N in heap
int jheap_val[MAXN], jheap_pos[MAXN], jposition[MAXN];

// decrease the value at postion i to a new value
void jdecreasekey_heap(int i, int new_value)
{
    int k1;
    int k=jposition[i]; // position in a heap
    jheap_val[k]=new_value;
    while (k>1)
    {
        jcount_dijkstra++; // each comparision is counted
        count_johnson++; // each comparision is counted
        k1=k / 2; //parent
        if (jheap_val[k1]>jheap_val[k])
        {
            swap(&jposition[jheap_pos[k1]],&jposition[jheap_pos[k]]);
            swap(&jheap_val[k1],&jheap_val[k]);
            swap(&jheap_pos[k1],&jheap_pos[k]);
        }
        else break;
        k=k1;
    }
}

// add a new value to a heap
void jaddkey_heap(int i, int new_value, int *heap_size)
{
    (*heap_size)++;
    int k=*heap_size;
    jposition[i]=k;
    jheap_val[k]=new_value;
    jheap_pos[k]=i;
    jdecreasekey_heap(i,new_value);
}

// delete the root of the heap and return the structure with its value and id
struct min_vertex jdeletemin_heap(int *heap_size)
{
    int k1, k2, k=1;
    struct min_vertex r;
    r.val=jheap_val[k];
    r.id=jheap_pos[k];
    jheap_val[k]=jheap_val[*heap_size];
    jheap_pos[k]=jheap_pos[*heap_size];
    jposition[jheap_pos[k]]=k;


    (*heap_size)--;
    while (k<*heap_size)
    {
        jcount_dijkstra++; // each comparision is counted
        count_johnson++; // each comparision is counted
        k1=2*k; k2=2*k+1; //children
        if (k1>*heap_size) break;
        if (k2<=*heap_size)
            if (jheap_val[k2]<jheap_val[k1]) k1=k2;
        if (jheap_val[k1]<jheap_val[k])
        {
            swap(&jposition[jheap_pos[k1]],&jposition[jheap_pos[k]]);
            swap(&jheap_val[k1],&jheap_val[k]);
            swap(&jheap_pos[k1],&jheap_pos[k]);
        }
        else break;
        k=k1;
    }
    return r;
}

// copy the results of Dijkstra's alg (from S to all vertices) into APSP array
void japspd( int V, int S)
{
    int i ;
    for ( i = 1 ; i <= V ; i++ )
        jAPSPD[S][i]=jdistance[i];
}

// the main function of Dijkstra's alg.
// determine SP from S to all vertices (V: number of vertices)
void jdijkstra ( int S , int V )
{
    int u;
    struct min_vertex r;
    int N=V;
    while( N >0 )
    {
        r=jdeletemin_heap(&N);
        u=r.id;
        jdistance[u]=r.val;
        for (struct neighbour *t=Graph[u].first; t!=NULL;t=t->n)
        {
                if ((jdistance[u]!=INF)&&( jdistance[u] + t->w < jdistance[t->v]))
                    jdecreasekey_heap(t->v,jdistance[u] + t->w ), jdistance[t->v]=jdistance[u]+t->w, jparent[t->v] = u ;
        }
    }
    japspd(V,S);
}

// in order to apply Dijkstra's alg.
// initialize heap, then call it for the vertex S
void  jmain_Dijkstra(int V, int S)
{
    int i;
    int N=0;

    for ( i = 1 ; i <= V ; i++ )
        jaddkey_heap(i,INF,&N), jdistance[i] = INF , jparent[i] = -1 ;

    jdecreasekey_heap(S,0);
    jdistance[S] = 0 ;
    jdijkstra (S, V) ;

}

// Bellman-Ford algorithm using adjacency list representation of graph
int Bellman_Ford0(int V,  int S)
{
    int i,u,flag=1; 
    for(i=0;i<=V;i++)
        jdistance[i] = INF , jparent[i] = -1 ;

    jdistance[S]=0 ;
    for(i=0;i<=V-1;i++)
    {
        for (u=0;u<=V;u++) 
            for (struct neighbour *t=Graph[u].first; t!=NULL;t=t->n)
            {
                count_johnson++; //count the number of iterations
                count_bf++;            // count the number of iterations
                if((jdistance[u]!=INF)&&( jdistance[u] + t->w < jdistance[t->v]))
                   jdistance[t->v]=jdistance[u]+t->w, jparent[t->v] = u ;
            }
    }

        for (u=0;u<=V;u++)
            for (struct neighbour *t=Graph[u].first; t!=NULL;t=t->n)
            {
                count_johnson++;
                count_bf++;
                if((jdistance[u]!=INF)&&( jdistance[u] + t->w < jdistance[t->v]))
                   flag=0;
            }

        return flag;
}

// add vertex 0, then find SP from vertex 0 using the BF alg.
void main_Bellman_Ford0(int V)  
{
    struct neighbour *t;
    int i;
    Graph[0].odegree=V;
    Graph[0].first=(struct neighbour *)malloc(sizeof (struct neighbour));
    for ( i=1,t=Graph[0].first;i<=V;i++)
    {
        t->v=i;
        t->w=0;
        if (i<V) {t->n=(struct neighbour *)malloc(sizeof (struct neighbour)); t=t->n;}
        else t=NULL;
    }

    if(Bellman_Ford0(V,0))
        ;  // No negative weight cycle
    else printf("\nNegative weight cycle exists\n");
}

// recalculate weights procedure for BF alg.
void recalculate_weights(int V)
{
    int u;
    for (u=0;u<=V;u++)
        for (struct neighbour *t=Graph[u].first; t!=NULL;t=t->n)
        {
            count_johnson++;
            t->w=t->w+h[u]-h[t->v];
        }
}

// the main Johnson's alg.
void johnson(int V)
{
    int i,j,S;
    printf("Johnson's Algorithm\n");
    main_Bellman_Ford0(V);

    for (i=0;i<=V;i++)
    {
        h[i]=jdistance[i];
    }
    recalculate_weights(V);
    for (S=1;S<=V;S++)
        jmain_Dijkstra(V, S);

    //    APSP Johnson
    for (i=1;i<=V;i++)
        for (j=1;j<=V;j++)
            if (jAPSPD[i][j] !=INF) APSPJ[i][j]=jAPSPD[i][j]+h[j]-h[i];
            else APSPJ[i][j]=jAPSPD[i][j];
}


/*************** FW VERSIONS ************/

long long int count_fw=0, count_fwi=0, count_nfw=0;

// adjacency matrix representation for 3 versions of FW alg
// original, efficient, improved (our new)
int A[MAXN][MAXN], Ai[MAXN][MAXN], An[MAXN][MAXN];

// original FW alg.
void fw(int N)
{
    int i,j,k;

    printf("Floyd-Warshall Algorithm\n");
    start_s=clock();
       for (k=0;k<N;k++)
         for (i=0;i<N;i++)
            for (j=0;j<N;j++)
            {
                count_fw++;
                if ((A[i][k]<INF) && (A[k][j]<INF)&& ((A[i][k]+A[k][j])<A[i][j]))
                   A[i][j]=A[i][k]+A[k][j];
            }
    stop_s=clock();
    printf("Execution time: %f\n",(double)(stop_s - start_s));
}

// efficient FW alg.
void fwi(int N)
{
    int i,j,k;

    printf("Floyd-Warshall Algorithm standard \n");
    start_s=clock();
    for (k=0;k<N;k++)
         for (i=0;i<N;i++)
            if (Ai[i][k]<INF)
               for (j=0;j<N;j++)
                  if (Ai[k][j]<INF)
                 {
                     count_fwi++;
                     if ((Ai[i][k]<INF) && (Ai[k][j]<INF)&& ((Ai[i][k]+Ai[k][j])<Ai[i][j]))
                        Ai[i][j]=Ai[i][k]+Ai[k][j];
                  }
    stop_s=clock();
    printf("Execution time: %f\n",(double)(stop_s - start_s));
}

// our new improved FW alg.
void new_fw(int N)
{
    static int inc[MAXN],outc[MAXN];
    static int inlist[MAXN][MAXN], outlist[MAXN][MAXN];
    int i,j,k,kk;
    static int select_k[MAXN],mininxout,mink;

    printf("New/Improved Floyd Warshall Algorithm\n");

    for (i=0;i<N;i++)
        inc[i]=0,outc[i]=0,select_k[i]=0;
    start_s=clock();
    for (i=0;i<N;i++)
       for (j=0;j<N;j++)
       {
         count_nfw++;  // initial calculations 
         if ((An[i][j]!=0) && (An[i][j]<INF))
         { inc[j]++;outc[i]++;inlist[j][inc[j]-1]=i;outlist[i][outc[i]-1]=j;}
       }


    for (kk=0;kk<N;kk++)
    {
        mink=-1;
        mininxout=2*N*N;
        for (k=0;k<N;k++)
        {
           count_nfw++;  // for each k: find min
           if ((select_k[k]==0) &&(inc[k]*outc[k]<mininxout))
           {
              mink=k;
              mininxout=inc[k]*outc[k];
           }
       }
       k=mink;
       select_k[k]=1;
       for (i=0;i<inc[k];i++)
            for (j=0;j<outc[k];j++)
            {
                count_nfw++;
                if ((An[inlist[k][i]][k]+An[k][outlist[k][j]])<An[inlist[k][i]][outlist[k][j]])
                {
                   if (An[inlist[k][i]][outlist[k][j]]==INF) //NO NEGATIVE CYCLE ASSUMED
                   {
                      outc[inlist[k][i]]++; outlist[inlist[k][i]][outc[inlist[k][i]]-1]=outlist[k][j];
                      inc[outlist[k][j]]++; inlist[outlist[k][j]][inc[outlist[k][j]]-1]=inlist[k][i];
                   }
                   An[inlist[k][i]][outlist[k][j]]=An[inlist[k][i]][k]+An[k][outlist[k][j]];
               }
           }
    }
    stop_s=clock();
    printf("Execution time: %f\n",(double)(stop_s - start_s));
}

/********* MAIN FUNCTION *********/

int main()
{
    int N, i, j, S;

    /* input from user */
    /***
    scanf("%d",&N);
    for(i=0;i<N;i++)
        for(j=0;j<N;j++)
           scanf("%d",&A[i][j]),G[i][j]=Ai[i][j]=A[i][j];
    ***/
    

     /* random input */

    N=1024;  // number of vertices in the graph
    int lgN=log(N)/log(2);
    printf("Clocks per sec %d\n",CLOCKS_PER_SEC);
    // densities (use 4N) - N/4, N/2, N, 2N, 4N, NlgN, 2NlgN, N/lgN, N/2 
    int TESTS[]={1,2,4,8,16,4*lgN,8*lgN,4*N/lgN,2*N};   
    // 9 different densities (x); 10 random input (y); repeat each input 5 times (z)
    for (int x=0;x<9;x++) for (int y=0;y<10;y++) for (int z=0;z<5;z++)
    {
       srand(x+y+1); // random seed
       count_fw= count_fwi= count_dijkstra=count_johnson=count_nfw=0; // correct counts
       // initialize the adj matrix to INF and its diagonal to 0
       for (i=0;i<N;i++)
          for (j=0;j<N;j++)
              if (i==j) G[i][j]=An[i][j]=Ai[i][j]=A[i][j]=0;
              else G[i][j]=An[i][j]=Ai[i][j]=A[i][j]=INF;
       int c=0;
       // randomly select entries to make an edge (using 9 different densities)
       for (i=0;i<N;i++)
           for (j=0;j<N;j++)
               if ((i!=j)&&(rand()%(4*N)>=(4*N-TESTS[x]))) A[i][j]=Ai[i][j]=An[i][j]=G[i][j]=1,c++;
       printf("\nNumber of Edges: %d\n",c);

       // constuct adj list from adj matrix
       for ( i=1 ; i<=N ; i++ )
       {
          Graph[i].odegree=0;
          Graph[i].first=NULL;
          Graph[i].last=NULL;
          for( j = 1 ; j <= N ; j++ )
          {
             if ((G[i-1][j-1]!=INF) && (G[i-1][j-1] != 0)) 
             {   // to be able to handle negative wights
                 Graph[i].odegree++;
                 if (Graph[i].odegree==1)
                 {
                     Graph[i].first=(struct neighbour *)malloc(sizeof (struct neighbour));
                     Graph[i].last=Graph[i].first;
                 }
                 else
                 {
                     Graph[i].last->n=(struct neighbour *)malloc(sizeof (struct neighbour));
                     Graph[i].last=Graph[i].last->n;
                 }
                 Graph[i].last->v=j;
                 Graph[i].last->w=G[i-1][j-1];
                 Graph[i].last->n=NULL;
              }
          }
      }

      // determine execution times of algorithms after adj list, adj matrix are constructed
      // execute FW and new FW
      fwi(N); 
      new_fw(N);
        
      // execute Dijkstra's alg. for each vertex as root
      printf("Dijkstra's Algorithm\n");
      start_s=clock();
      for (S=1;S<=N;S++)
         main_Dijkstra(N, S);
      stop_s=clock();
      printf("Dijkstra's Execution time: %f\n",(double)(stop_s - start_s));
     
      // execute Johnson's alg.
      start_s=clock();
      johnson(N);  
      stop_s=clock();
      printf("Johnson's Execution time: %f\n",(double)(stop_s - start_s));

      // verify that all outputs are the same 
      for (i=1;i<=N;i++)
        for (j=1;j<=N;j++)
          if ((Ai[i-1][j-1] != APSPJ[i][j]) || (Ai[i-1][j-1] != APSPD[i][j]) || (Ai[i-1][j-1] != An[i-1][j-1]))
              printf("%d %d\n",i,j);

     // print the number of operations for each alg.
     printf("Dij %ld John %ld FWi %ld FWn %ld\n",count_dijkstra,count_johnson,count_fwi,count_nfw);    
   }
   return 0;
}


/*
5
0 6 9999 5 9999
2 0 3 -1 2
-2 9999 0 2 9999
-1 1 2 0 -1
1 9999 9999 9999 0
*/
