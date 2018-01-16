Module testgraph

use graph.word

use seq.arc.word

use set.arc.word

use set.word

use stdlib

Function n1 word {"1"_1 }

Function n2 word {"2"_1 }

Function n3 word {"3"_1 }

Function n4 word {"4"_1 }

Function n5 word {"5"_1 }

Function n6 word {"6"_1 }

Function n7 word {"7"_1 }

Function n8 word {"8"_1 }

Function testgraph seq.word 
 let g = newgraph.[ arc(n1, n2), arc(n3, n2), arc(n2, n4), arc(n1, n4), arc(n5, n6), arc(n6, n7), arc(n7, n5), arc(n6, n8), arc(n5, n1)]
  let r = print.g +"transversal"+ sinksfirst.g +"Suc"+ toseq.successors(g, n2)+"sinks"+ sinks(g, asset.[ n4], n2)
  {(if r ="GRAPH:(1 2)(1 4)(2 4)(3 2)(6 8)(6 7)(5 1)(5 6)(7 5)transversal 4 8 2 1 3 Suc 4 sinks 2"
   then"PASS testgraph"
   else"FAIL testgraph")+ let g2 = newgraph.[ arc(n1, n2), arc(n3, n2), arc(n2, n4)]
   let closure = [ arc(n1, n2), arc(n1, n4), arc(n2, n4), arc(n3, n2), arc(n3, n4)]
   @(+, print,"", toseq.arcs.transitiveClosure.g2)}

@(+, print,"", toseq.arcs.g)

Function testgraph2 boolean 
 let g = newgraph.[ arc(n1, n2), arc(n3, n2), arc(n2, n4)]
  let closure = [ arc(n1, n2), arc(n1, n4), arc(n2, n4), arc(n3, n2), arc(n3, n4)]
  closure = toseq.arcs.transitiveClosure.g

Function print(g:graph.word)seq.word 
 {"GRAPH:"+ @(+, print,"", toseq.arcs.g)}

Function print(a:arc.word)seq.word {"("+ tail.a + head.a +")"}

