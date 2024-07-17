import networkx as nx
import numpy as np
def hasC4cycle(Gr):
   #checks if any two vertices have more than one common neighbour
   #by checking if any number outside the diagonal of A**2 is bigger than 1
   #where A is adjacency matrix
   A=nx.adjacency_matrix(Gr).todense()
   A=np.dot(A,A)
   np.fill_diagonal(A,0)
   return (A>1).any()
def text2graphs(x):
   #converts a line in the input file to two graphs:
   #red is stored in G['r'] and blue in G['b']
   #moreover, G['m'] contains a winning move for Builder
   #and G['l'] contains a line number of an isomorphic graph
   #if there is one
   G={'r':nx.Graph(),'b':nx.Graph()}
   y=x.split()
   for i in y:
      if len(i)>1 and i[1]==':':
         k=i[0]
      else:
         if k in 'br':
            G[k].add_edge(i[0],i[1])
         else:
            G[k]=i
   return G
def isPnPath(G,n):
   return nx.is_tree(G) and max([x[1] for x in G.degree])<=2 and len(G.nodes)==n
def sumgraphs(G1,G2):
   #merges two graphs into one multigraph, 
   #where edges of G1 are red and of G2 are blue
   G=nx.MultiGraph()
   G.add_edges_from(G1.edges,color='red')
   G.add_edges_from(G2.edges,color='blue')
   return G
def colourCheck(multiedge1,multiedge2):
   #check if two multiedges are isomorphic to each other
   #this function is used only in multigraphs, where every multiedge
   #may have at most one blue edge and one red
   if len(multiedge1)!= len(multiedge2): 
      #if one multiedge has different number of edges than the other
      return False
   if len(multiedge1)!=1 or multiedge1[0]['color']==multiedge2[0]['color']:
      return True
def validateStrategy(G1):
   #checks validity of the strategy in the file
   #for the starting position G1 (pair of red and blue graphs)
   result=True
   numberOfEdges=G1['r'].number_of_edges()+G1['b'].number_of_edges()
   if numberOfEdges>=E:
      print('Error: too many moves done by Builder')
      return False
   if len(G1['r'].nodes | G1['b'].nodes)>V:
      print('Error: too many vertices used by Builder')
   global lineNum
   global fileLines #content of strategy file converted to list of lines
   lineNum+=1
   G2=text2graphs(fileLines[lineNum])
   if G1['r'].adj!=G2['r'].adj or G1['b'].adj!=G2['b'].adj:
      print(f'Error: the graph in the line {lineNum+1}'+
      ' does not match the expected graph')
      print(lineNum)
      print(G1['r'].adj,G2['r'].adj,G1['b'].adj,G2['b'].adj,sep='\n')
      return False
   if not(set(G2['m'])  & (G1['r'].nodes | G1['b'].nodes)) and numberOfEdges>0:
      print("Error: the winning move is breaking the connectivity rule.")
      return False 
   if 'l' in G2:
      H2=sumgraphs(G2['r'],G2['b'])
      G3=text2graphs(fileLines[int(G2['l'])-1])
      H3=sumgraphs(G3['r'],G3['b'])
      if nx.is_isomorphic(H2,H3,edge_match=colourCheck):
         return True
      else:
         print(H2.adj)
         print(H3.adj)
         print("Error: isomorphism between graphs does not exist")
         return False
   G4={'r':nx.Graph(G1['r']),'b':nx.Graph(G1['b'])}
   G1['b'].add_edge(*G2['m'])
   G4['r'].add_edge(*G2['m'])
   #we assume here that all positions in the file are stored
   #in pre-order way, where the left child corresponds to blue edge
   #and the right child to the red edge
   if not isPnPath(G1['b'],N):
      result &= validateStrategy(G1)
   if not hasC4cycle(G4['r']):
      result &= validateStrategy(G4)
   return result
def edgesToPairOfGraphs(list1,list2):
   return {'r':nx.from_edgelist(list1),'b':nx.from_edgelist(list2)}
Gdict={
   'empty':edgesToPairOfGraphs([],[]),
   'b-path':edgesToPairOfGraphs([],['01']),
   'br-path':edgesToPairOfGraphs(['12'],['01']),
   'brr-path':edgesToPairOfGraphs(['12','23'],['01']),
   'brb-path':edgesToPairOfGraphs(['12'],['01','23']),
   'd-multipath':edgesToPairOfGraphs(['01'],['01']),
   'dr-multipath':edgesToPairOfGraphs(['01','12'],['01']),
   'drr-multipath':edgesToPairOfGraphs(['01','12','23'],['01']),
   'drb-multipath':edgesToPairOfGraphs(['01','12'],['01','23'])
}
def validateFile():
   #checks validity of the strategy for all of the starting 
   #positions in the file for which Builder has a winning strategy
   f=open(f'C4P{N}_in_{E}_moves_{V}_verts.txt','r')
   global fileLines 
   fileLines=list(f)
   global lineNum
   lineNum=0
   while lineNum<len(fileLines):
      #if Builder has a winning strategy for a given
      if fileLines[lineNum][:2]=='rc' and fileLines[lineNum][-2]=='1':
         line=fileLines[lineNum]
         lineSplitted=line.split(',')
         #lineSplitted[2] is a name of starting position
         G={'r':nx.Graph(Gdict[lineSplitted[2]]['r']),
         'b':nx.Graph(Gdict[lineSplitted[2]]['b'])}
         if validateStrategy(G):
            print(line[:-1],'validated')
         else:
            file.close()
            return False
      lineNum+=1
   f.close()
   return True
Vlist=[4,5,6,7,8,8,9,10,11,12,13,14]
Nlist=[3,4,5,6,7,7,8,9,10,11,12,13]
Elist=[6,8,9,11,13,12,14,16,18,20,22,24]
result=True
for V,N,E in zip(Vlist,Nlist,Elist):
   result&=validateFile()
if result:
   print('All files validated')
