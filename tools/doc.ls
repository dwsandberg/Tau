#!/usr/local/bin/tau ; use doc ; createdoc

 callgraphwithin("bug11","seqiohelp")

;use doc; doclibrary."bug11"

;use wordgraph; testgraph

; use doc ; doclibrary."stdlib"


; use doc; usegraph("stdlib usegraph include main2 compilerfront passsymbol postbind  exclude    graph     bits  process set seq otherseq standard textio words")

; use doc ; doclibrary."stdlib"

; use doc ; createdoc

; use doc ; createdoc

; use pretty ; htmlcode("bug10")

; use doc ; callgraphbetween("stdlib","interperter tausupport mangle")

; use doc ; createdoc

; use doc ; doclibrary."stdlib"

; use doc ; createdoc

Module doc

use format

use libraryModule

use main2

use pretty

use standard

use symbol2

use textio

use seq.char

use seq.mytype

use encoding.symbol

use seq.symbol

use graph.symbolref

use seq.symbolref

use set.symbolref

use graph.word

use set.word

use seq.encodingpair.symbol

use seq.arc.symbolref

use set.arc.symbolref

use seq.arc.word

use set.arc.word

use svg2graph.seq.word


use seq.seq.word

Function htmlcode(libname:seq.word)seq.word
let p = prettyfile(true, '  /< noformat <hr id ="T">  />  /keyword ', getlibrarysrc.libname << 3)
let modules =
 for acc ="", @e ∈ p do
  if subseq(@e, 1, 2) ∈ [" /< noformat"]then acc + @e_7 else acc
 /for(acc)
" /< noformat <h1> Source code for Library" + libname + "</h1>  />"
+ for acc ="", modname ∈ modules do acc + '  /< noformat <a href ="' + merge.["#"_1, modname] + '"> ' + modname
+ "</a>  />" /for(acc)
+ for acc ="", @e ∈ p do acc + @e + " /p"/for(acc >> 1)


function symbolref(sym:symbol)symbolref symbolref.valueofencoding.encode.sym

function assignencoding(  a:symbol)int nextencoding.a

function decode(s:symbolref)symbol decode.to:encoding.symbol(toint.s)

Function createdoc seq.word
{ Creates html tau html documentation. Creates file taudocs.html }
let d =
 for acc ="", @e ∈ prettyfile(false,"", gettext."tools/doc.txt")do acc + addselect.@e /for(acc)
let x1 = createfile("doc.html", toUTF8bytes.d)
{ let x2 = createfile("appdoc.html", [ htmlheader + processpara.@(+, addselect,"", gettext."tools/appdoc.txt")]
)}
{ let y1 = createhtmlfile("testall.html", htmlcode."testall")}
let y1 = createfile("stdlib.html", toUTF8bytes.doclibrary."stdlib")
d

function addselect(s:seq.word)seq.word
if isempty.s then" /p" + s
else if first.s = first."/section"then" /< /section" + s << 1 + " />"
else if first.s ∈ "Module module"then" /p  /keyword" + s else" /p" + s

Function callgraphbetween(libname:seq.word, modulelist:seq.word)seq.word
{ Calls between modules in list of modules. }
let z = formcallarcs.libname
let arcs =
 for acc = empty:seq.arc.symbol, a ∈ z do
  let t1 =  tail.a
  let h1 =  head.a
  if module.t1 = module.h1 then acc
  else if name.module.t1 ∈ modulelist ∧ name.module.h1 ∈ modulelist then acc + arc(t1,h1) else acc
 /for(acc)
drawgraph.newgraph.arcs

use profile

use seq.arc.symbol

use graph.symbol

use svg2graph.symbol

Function formcallarcs(libname:seq.word)seq.arc.symbol 
for arcs2 = empty:seq.arc.symbol, p ∈ prg.compilerfront("text", libname)do
 let tail = decode.symbolref.sym.p
 for arcs = arcs2, sym ∈ code.p do
  if isconst.sym ∨ isspecial.sym ∨ sym = sym.p then arcs else arcs + arc(tail, decode.symbolref.sym)
 /for(arcs)
/for(arcs2)

Function callgraphwithin(libname:seq.word, modulelist:seq.word)seq.word
{ Calls within modules in list of modules. }
let t =
 for arcs2 = empty:seq.arc.symbol , p ∈ prg.compilerfront("pass1", libname)do
  let tail =  sym.p
  for arcs = arcs2, sym ∈ code.p do
   if isconst.sym ∨ isspecial.sym ∨ sym = sym.p then arcs else arcs + arc(tail, sym)
  /for(arcs)
 /for(arcs2)
let g = newgraph.formcallarcs.libname
let nodesnottoinclude =
 for acc = empty:set.symbol, @e ∈ toseq.nodes.g do
  if name.module.@e ∈ modulelist then acc else acc + @e
 /for(acc)
let g2 = for acc = g, @e ∈ toseq.nodesnottoinclude do deletenode(acc, @e)/for(acc)
drawgraph.g2

use set.symbol

  


use wordgraph

Function testdoc seq.word { callgraphwithin("stdlib","llvm")+ } doclibrary."stdlib"

Function doclibrary(libname:seq.word)seq.word
{ create summary documentation for libraray. }
let liba = getlibrarysrc.libname
let exports =liba_3
let todoc =
 for acc ="", s ∈ liba do
  if subseq(s, 1, 3) = "* only document"then acc + subseq(s, 4, length.s)else acc
 /for(if isempty.acc then exports else acc /if)
let g = newgraph.usegraph(liba,"mod"_1)
 modindex.todoc + docmodule(g, exports, todoc, liba)
  

function modindex(mods:seq.word)seq.word
for txt ="", modname ∈ mods do
 txt + '  /< noformat <a href ="' + merge.["#"_1, modname] + '"> '
 + modname
 + "</a>  />"
/for(txt)

+ if length.todoc > 0 then""else" /< /section Possibly Unused Functions  />  /< select x"+ uncalledfunctions.libname +" />"

* Paragraphs beginning with * are included in documentation.

* If a paragraph in the library module is of the form:* only document <module1 name> <module2 name>... then only those modules 
 named will be documented.

* If a paragraph in the library is of the form:* usegraph exclude <list of modules> include <list of modules> then a use graph 
 will be construction including and excluding the modules listed. Both the exclude and include are optional, but for a large 
 library should be used to restrict the size of the graph. An example of a use graph is included at the end of this module.




Function uncalledfunctions(libname:seq.word)seq.word
{ List of functions may include indirectly called functions. }
let g = newgraph.formcallarcs.libname
let sources =
 for acc = empty:seq.symbol , @e ∈ toseq.nodes.g do acc + sources(g, empty:set.symbol, @e)/for(acc)
for acc ="", @e ∈ sources do acc + print.@e + " /br"/for(acc)

* usegraph exclude standard seq set UTF8 stack graph otherseq

function usegraph(lib:seq.seq.word, kind:word)seq.arc.word
for      currentmod="?"_1,result=empty:seq.arc.word, p /in lib do
   if isempty.p then next(currentmod,result)
   else  if first.p ∈ "module Module"then
        next( p_2,result)
  else if first.p /in  "use" then
  let m =
   if length.p = 2 then p_2
   else if kind = "mod"_1  then  p_2
   else  merge.( p << 1)
  next(currentmod,if currentmod = m /or currentmod /in "?" then result else  result + arc(currentmod, m))
 else next( currentmod, result) 
 /for(result)
 
Function  usegraph(p:seq.word) seq.word
  let i= findindex("usegraph"_1, p)
  let lib=getlibrarysrc.subseq(p,1,i-1) 
 let l = findindex("include"_1, p)
   let k = findindex("exclude"_1, p)
   let include=subseq(p, l + 1, k)
   let exclude= subseq(p, k + 1, length.p)
  for arclist=empty:seq.arc.word,    a /in usegraph(lib,"mod"_1)  do
    if head.a /in exclude  /or not.isempty.include /and  tail.a /nin  include  then arclist
     else arclist+a
  /for(drawgraph(newgraph.arclist) ) 

 
 
 function docmodule(usegraph:graph.word
, exports:seq.word
, todoc:seq.word
, lib:seq.seq.word
)seq.word
for acc="",currentmod="?",funcs="",types="", p /in lib do 
 if isempty.p then next(acc,currentmod,funcs,types)
else if first.p ∈ "module Module"then
 let modname = p_2
 if  modname /nin todoc   then
  next(acc,currentmod,funcs,types)
 else
  let leftover =
   if length.types > 0 ∨ length.funcs > 0 then" /br defines types: " + types + funcs
   else""
  let name = [ modname] + if length.p > 2 then".T"else""
 next(acc+ leftover + '  /< noformat <hr id ="' + modname + '">  /> '
  + " /< /section  /keyword module"
  + name
  + " />"
  + if modname ∈ exports then"Module" + name + "is exported from library. "
  else""/if
  + " /br Module"
  + name
  + "is used in modules: "
  + alphasort.for acc2 ="", @e ∈ toseq.arcstopredecessors(usegraph, merge.name)do acc2 + tail.@e /for(acc2)
  , subseq(p, 2, length.p)
  ,""
  ,""
  )
else if currentmod = ""then
 next( acc,currentmod, funcs, types)
else if length.p > 2 /and first.p /in "*" then
   let toadd =
 " /p"
  + if p_2 = "usegraph"_1 then
   let l = findindex("include"_1, p)
   let k = findindex("exclude"_1, p)
   let include=subseq(p, l + 1, k)
   let exclude= subseq(p, k + 1, length.p)
  for arclist=empty:seq.arc.word,    a /in toseq.arcs.usegraph  do
    if head.a /in exclude  /or not.isempty.include /and  tail.a /nin  include  then arclist
     else arclist+a
  /for(drawgraph(newgraph.arclist) ) 
  else subseq(p, 2, length.p)
 next( acc,currentmod, funcs + toadd, types)
else if first.p ∈ "Function Export"then
 let z = getheader.p
 let toadd =
 " /p  /keyword"
  + if subseq(p, length.z, length.z + 1) = "{ *"then
   z >> 1 + "{" + subseq(p, length.z + 2, findindex("}"_1, p))
  else if last.z ∈ "stub"then z >> 1 else z
 next( acc,currentmod, funcs + toadd, types)
else if first.p /in  "type" then
 next( acc, currentmod, funcs, types + p_2)
else next( acc, currentmod, funcs, types)
/for(acc+if not.isempty.types ∨ not.isempty.funcs   then" /br defines types: " + types + funcs
 else"")
 

 
 module wordgraph 
 
 use standard
 
 use set.word
 
 use graph.word
 
  use svg2graph.word
  
  use seq.arc.word
 
 function nodeTitle(word)seq.word ""
 
 function node2text(a:word) seq.word [a]
 
 function generatenode(a:set.word)word toword.cardinality.a
 
 
 Export drawgraph(g:graph.word) seq.word 
 
 
  Function  testgraph seq.word
  let data= "parse mytype parse parsersupport parse format parse symboldict main2 libraryModule main2 process main2 timestamp main2 compilerfront main2 codegennew main2 format main2 interpreter passsymbol mytype passsymbol parse passsymbol symboldict typedict mytype pass2 localmap2 pass2 mergeblocks pass2 interpreter postbind mytype postbind localmap2 postbind passsymbol postbind typedict postbind symref postbind symboldict passparse mytype passparse parse passparse passsymbol passparse typedict passparse symboldict
 "
    let none=first."."
      for arcs=empty:seq.arc.word,  last=none,  w /in data+"." do 
      if last=none then 
         next(arcs,w)
      else 
         next(arcs+arc(last,w),none)
         /for( drawgraph.newgraph.arcs)
         
