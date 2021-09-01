#!/usr/local/bin/tau ; use tools; testprofile."solardataall"

/run profile dumpprofileinfo

run tools testprofile

Module profile

Problems:Junk at top of graph

Max space seems to be on node with head and tail blank!

use displaytextgraph

 
use libraryModule


use standard

use words

use otherseq.alphaword

use seq.alphaword

use seq.int

use seq.liblib


use seq.parc

use set.parc

use otherseq.word

use seq.word

use seq.seq.word

use svggraph.seq.word

use seq.arcinfo.seq.word

use seq.seq.seq.word

use seq.lparc

* To profile a function add a use clause"use options.<return type of /function >"and change /function so body is wrap by a call to PROFILE(<body>). Multiple procedures can be profiled at the same time. After the part of code of interest add a call to profileresults("time")to optain the result.

* Profiling is accomplished by adding code to perform measurements before and after each procedure call and recording the difference.

 
 type lparc is head:symbol,tail:symbol,measure:int

    
  type tmptype is graph:labeledgraph.lparc,max:int 
  
  
  use labeledgraph.lparc
  
   
  use symbol2
  
  use seq.symbol
  
function   decode(w:symbolref,l:liblib) symbol   
  if between(toint.w,1,length.decoderef.l) then
   (decoderef.l)_toint.w 
  else Lit.toint.w

Function profileresults(measure:seq.word)seq.word
 { Returns label graph of profile results. Measure is time, count, or space. }
 { let g = profileresults }
 let tmp =  for acc = tmptype(empty:labeledgraph.lparc,0), @e = loadedLibs do 
      for  g0=graph.acc,max=max.acc,arc=profiledata.@e do
        let m=if measure = "time" then clocks.arc
              else if measure = "count"then counts.arc 
              else
               assert measure = "space"report"unknown profile measure"
               space.arc
         if m=0 then next(g0,max)
  else next(g0+lparc(decode(caller.arc,@e),decode(callee.arc,@e),m),max(m,max))
   /for(tmptype(g0,max))
 /for(acc)
 let g3=removesmall(graph.tmp,max.tmp)
 { for acc ="", @e = toseq.nodes.g3 do 
   acc + for x="",t=codedown.head.@e do  x+t+";" /for(x) +EOL /for(acc)
  }
   { shorten the names of the functions and then build and display labeled graph }
   assert      for acc =empty:set.word, @e = toseq.nodes.g3 do acc + name.head.@e /for(cardinality.acc)
       = cardinality.nodes.g3 report "Problem:profile nodes names not distinct"
       +for txt="",  @e = toseq.nodes.g3 do txt+print.head.@e+EOL /for(txt)
{ let nodemap = shorten.for acc ="", @e = toseq.nodes.g3 do acc + head.@e /for(acc)}
   let z2 = for acc = empty:seq.arcinfo.seq.word, a = toseq.arcs.g3 do
   acc + {arcinfo(shorten(nodemap, head.a), shorten(nodemap, tail.a),}
      arcinfo([name(head.a)],[name.tail.a], [ toword(measure.a * 100 / max.tmp)])
  /for(acc)
     " /br" + measure + toword.max.tmp + " /br" + display.z2 + " /br"
   + measure
   + toword.max.tmp
    
  /     function symname(w:word) seq.word    (codedown.w)_1
       
 use set.word
  
 use set.lparc
 

function removesmall(g:labeledgraph.lparc,  m:int)labeledgraph.lparc
 let limit=m / 100
 for acc = g, node = toseq.nodes.g do 
 if cardinality.arcstosuccessors(acc, node) = 0 then
  if for total = 0, @e = toseq.backarcstopredecessors(acc, node)do total + measure.@e /for(total) < limit then
   deletenode(acc, node)
  else acc
 else acc
/for( 
  if cardinality.arcs.g = cardinality.arcs.acc then acc else removesmall(acc, m))




/Function shorten(pnodes:seq.word)nodemap
 { This procedure produces a map that takes fsigs and shortens them keeping them distinct. The following procedure uses this result to map the figs to the new ones. }
 let nodes = sort.toalphaseq.pnodes
 let c = for acc = [ empty:seq.seq.word], @e = towordseq.nodes do acc + codedown.@e /for(acc)
 + [ empty:seq.seq.word]
 let short = for acc = empty:seq.seq.word, @e = arithseq(length.c - 2, 1, 2)do
  acc + shorten(c, @e)
 /for(acc)
  nodemap(nodes, short)

Function shorten(map:nodemap, w:word)seq.word(short.map)_binarysearch(org.map, alphaword.w)

type nodemap is org:seq.alphaword, short:seq.seq.word

function shorten(a:seq.seq.seq.word, i:int)seq.word
let j = max(differ(a_(i - 1), a_i, 1), differ(a_i, a_(i + 1), 1))
 if j = 1 then a_i_1
 else
  let z = for acc = empty:seq.seq.word, @e = subseq(a_i, 1, j)do acc + formattype.@e /for(acc)
   z_1 + ":" + z_2 + "("
   + for acc ="", @e = subseq(z, 2, length.z)do list(acc,",", @e)/for(acc)
   + ")"

function formattype(a:seq.word)seq.word
 reverse.for acc ="", @e = a do list(acc,".", [ @e])/for(acc)

function differ(a:seq.seq.word, b:seq.seq.word, i:int)int
 if i > length.a ∨ i > length.b then i
 else if a_i = b_i then differ(a, b, i + 1)else i

/Export head(parc)word

/Export tail(parc)word

Export counts(parc)int

Export clocks(parc)int

Export space(parc)int


function ?(a:lparc, b:lparc)ordering head.a ? head.b ∧ tail.a ? tail.b

function ?2(a:lparc, b:lparc)ordering head.a ? head.b

function reverse(a:lparc)lparc lparc(tail.a, head.a, measure.a)

function tonode(a:lparc)lparc lparc(head.a, head.a, measure.a)


Function dumpprofileinfo seq.word 
let lib=loadedLibs_1
let e = profiledata.lib
 for acc ="", @e = profiledata.loadedLibs_1 do
  list(acc," /br",   print.decode(caller.@e,lib)+print.decode(callee.@e,lib)+toword.clocks.@e )
 /for(acc)