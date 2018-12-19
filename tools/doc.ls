module doc

run useful testing2

run tools createdoc

use display

use displaytextgraph

use fileio

use format

use graph.word

use libscope

use pretty

use seq.arc.word

use seq.arcinfo.seq.word

use seq.moddesc

use seq.mytype

use seq.syminfo

use seq.tree.word

use set.arc.word

use set.word

use stdlib

use textio

use tree.word

use main2


/Function createdoc seq.word // Creates html tau html documentation. Creates file taudocs.html // let d = @(+, prettyit.newgraph.empty:seq.arc.word,"", gettext."tools/doc.txt")let x = createfile("taudoc.html", [ htmlheader + processpara.d])let e = @(+, prettyit.newgraph.empty:seq.arc.word,"", gettext."tools/appdoc.txt")let x2 = createfile("appdoc.html", [ htmlheader + processpara.e])let y = createfile("testall.html", [ htmlheader + processpara.htmlcode."testall"])let z = createfile("tools.html", [ htmlheader + processpara.htmlcode."tools"])d

/function prettyit(usegraph:graph.word, s:seq.word)seq.word if subseq(s, 1, 2)="* usegraph"then let l = findindex("include"_1, s)let k = findindex("exclude"_1, s){"&{ noformat <h2> Use graph</h2> &}"+ if k > l then usegraph(usegraph, subseq(s, l + 1, k), subseq(s, k + 1, length.s))else usegraph(usegraph, subseq(s, l + 1, length.s), subseq(s, k + 1, l))} else"&{ select 1"+ prettyparagraph(defaultcontrol, s)+"&}"

/Function htmlcode(libname:seq.word)seq.word let l = tolibdesc(libname_1)let g = newgraph.usegraph("mod", l){"&{ noformat <h1> Source code for Library"+ libname +"</h1> &}"+ @(+, ref,"", modules.l)+ @(seperator."&{ noformat <hr> &}", prettymod.g,"", modules.l)}

/function ref(m:moddesc)seq.word {"&{ noformat <a href = &quot"+ merge("#"_1, modname.m)+"&quot >"+ modname.m +"</a> &}"}

/function prettymod(usegraph:graph.word, m:moddesc)seq.word {"&{ noformat <hr id = &quot"+ modname.m +"&quot > &}"+ @(+, prettyit.usegraph,"", src.m)}

Function callgraphbetween(libname:seq.word, modulelist:seq.word)seq.word 
// Calls between modules in list of modules. // 
 let z = formcallgraph(firstPass(libname_1), 2)
  let g = newgraph.@(+, modarc.@(+, mytype, empty:seq.mytype, modulelist), empty:seq.arc.word, z)
  display.@(+, toarcinfo, empty:seq.arcinfo.seq.word, toseq.arcs.g)

Function callgraphwithin(libname:seq.word, modulelist:seq.word)seq.word 
// Calls within modules in list of modules. // 
 let g = newgraph.formcallgraph(firstPass(libname_1), 2)
  let nodestoinclude = @(∪, filterx.modulelist, empty:set.word, toseq.nodes.g)
  let g2 = @(deletenode, identity, g, toseq.nodestoinclude)
  display.@(+, toarcinfo, empty:seq.arcinfo.seq.word, toseq.arcs.g2)

function filterx(include:seq.word, w:word)set.word 
 let p = codedown.w 
  if length.p < 2 
  then empty:set.word 
  else if last(p_2)in include then empty:set.word else asset.[ w]

function mytype(w:word)mytype mytype.[ w]

function modarc(s:seq.mytype, a:arc.word)seq.arc.word 
 let t1 = codedown.tail.a 
  let h1 = codedown.head.a 
  if length.t1 < 2 ∨ length.h1 < 2 ∨ t1_2 = h1_2 ∨ not(mytype(h1_2)in s ∧ mytype(t1_2)in s)
  then empty:seq.arc.word 
  else [ arc(merge.readable.tail.a, merge.readable.head.a)]

function toarcinfo(a:arc.word)arcinfo.seq.word arcinfo(readable.tail.a, readable.head.a,"")

function readable(fsig:word)seq.word 
 let p = codedown.fsig 
  if length.p = 1 
  then p_1 
  else let plist = @(+, mytype, empty:seq.mytype, subseq(p, 3, length.p))
  p_1 +":"+ print.mytype(p_2)+"("+ @(seperator.",", print,"", plist)+")"

Function usegraph(g:graph.word, include:seq.word, exclude:seq.word)seq.word 
 let g2 = @(deletenode, identity, g, exclude + @(+, addabstractpara,"", exclude))
  let g3 = if include =""
   then g2 
   else newgraph.toseq.@(∪, arcstosuccessors.g2, empty:set.arc.word, include + @(+, addabstractpara,"", include))
  display.@(+, toarcinfo, empty:seq.arcinfo.seq.word, toseq.arcs.g3)

function addabstractpara(w:word)word merge([ w]+".T")

Function doclibrary(libname:seq.word)seq.word 
// create summary documentation for libraray. // 
 let lib = firstPass(libname_1)
  let r = @(+, findrestrict,"", lib)
  let g = newgraph.usegraph(lib,"mod"_1, 1,"?"_1, empty:seq.arc.word)
  let libclause = lib_1 
  let e = findindex("exports"_1, libclause, 3)
  let exports = subseq(libclause, e + 1, length.libclause)
  docmodule(g, exports, r, lib, 1,"","","")+ if length.r > 0 
   then""
   else
   "&{ select x &section Possibly Unused Functions &} &{ select x"+ uncalledfunctions.libname +"&}"

@(+, +("&br &br"),"", lib)

* Paragraphs beginning with * are included in documentation.

* If a paragraph in the library module if of the form:* only document <module1 name> <module2 name>... then only those modules named will be documented.

* If a paragraph in the library is of the form:* usegraph exclude <list of modules> include <list of modules> then a use graph will be construction including and excluding the modules listed. Both the exclude and include are optional, but for a large library should be used to restrict the size of the graph. An example of a use graph is included at the end of this module.

function findrestrict(s:seq.word)seq.word 
 if subseq(s, 1, 3)="skip * only document"then subseq(s, 4, length.s)else""

function docmodule(usegraph:graph.word, exports:seq.word, todoc:seq.word, lib:seq.seq.word, i:int, currentmod:seq.word, funcs:seq.word, types:seq.word)seq.word 
 if i > length.lib 
  then if length.types > 0 ∨ length.funcs > 0 
   then"&br defines types: "+ types + funcs 
   else""
  else if lib_i_1 ="module"_1 
  then let modname = lib_i_2 
   if not(modname in todoc ∨ length.todoc = 0)
   then docmodule(usegraph, exports, todoc, lib, i + 1,"", funcs, types)
   else let leftover = if length.types > 0 ∨ length.funcs > 0 
    then"&br defines types: "+ types + funcs 
    else""
   let name = [ modname]+ if length(lib_i)> 2 then".T"else""
   leftover +"&{ select x &section &keyword module"+ name +"&}"+(if modname in exports 
    then"Module"+ name +"is exported from library. "
    else"")+"&br Module"+ name +"is used in modules: "+ alphasort.@(+, tail,"", toseq.arcstopredecessors(usegraph, merge.name))+ docmodule(usegraph, exports, todoc, lib, i + 1, subseq(lib_i, 2, length(lib_i)),"","")
  else if currentmod =""
  then docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)
  else if subseq(lib_i, 1, 2)="skip *"
  then let a = subseq(lib_i, 2, length(lib_i))
   let toadd ="&{ select x"+(if a_2 ="usegraph"_1 
    then let l = findindex("include"_1, a)
     let k = findindex("exclude"_1, a)
     usegraph(usegraph, subseq(a, l + 1, k), subseq(a, k + 1, length.a))
    else subseq(a, 2, length.a))+"&}"
   docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs + toadd, types)
  else if lib_i_1 ="Function"_1 
  then let toadd ="&{ select x &keyword"+ subseq(lib_i, 1, length(lib_i) - if length.currentmod = 1 then 2 else 1)+ toword.length.currentmod +"&}"
   docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs + toadd, types)
  else if lib_i_1 in"record encoding sequence"
  then docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types + lib_i_2)
  else if lib_i_1 in"export"
  then let j = findindex("Function"_1, lib_i)
   if length(lib_i)> j 
   then let toadd ="&{ select x &keyword"+ subseq(lib_i, j, length(lib_i))
    docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs + toadd, types)+"&}"
   else docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)
  else docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)

Function uncalledfunctions(libname:seq.word)seq.word // List of functions may include indirectly called functions. // 
 let g = newgraph.formcallgraph(firstPass(libname_1), 2)
  let sources = @(+, sources(g, empty:set.word),"", toseq.nodes.g)
  @(seperator."&br", readable,"", alphasort.sources)

* usegraph exclude stdlib seq set

function usegraph(lib:seq.seq.word, kind:word, i:int, currentmod:word, result:seq.arc.word)seq.arc.word 
 if i > length.lib 
  then result 
  else let key = lib_i_1 
  if key ="module"_1 
  then usegraph(lib, kind, i + 1, merge.subseq(lib_i, 2, length(lib_i)), result)
  else if key ="use"_1 
  then let m = if length(lib_i)= 2 
    then lib_i_2 
    else if kind ="mod"_1 
    then merge([ lib_i_2]+".T")
    else merge.subseq(lib_i, 2, length(lib_i))
   if currentmod = m 
   then usegraph(lib, kind, i + 1, currentmod, result)
   else usegraph(lib, kind, i + 1, currentmod, result + arc(currentmod, m))
  else usegraph(lib, kind, i + 1, currentmod, result)

function formcallgraph(lib:seq.seq.word, i:int)seq.arc.word 
 if i > length.lib 
  then empty:seq.arc.word 
  else if lib_i_1 ="bindings"_1 
  then formcallgraph(lib_i_2, lib_i, 3, empty:seq.arc.word)+ formcallgraph(lib, i + 1)
  else formcallgraph(lib, i + 1)

function formcallgraph(func:word, src:seq.word, i:int, result:seq.arc.word)seq.arc.word 
 if i > length.src 
  then result 
  else let name = src_i 
  if name in"IDXUC CALLIDX STATE PROCESS2 FREF EQL if VERYSIMPLE"
  then formcallgraph(func, src, i + 1, result)
  else if name in"LIT PARAM LOCAL WORD SET define RECORD APPLY LOOPBLOCK STKRECORD CONTINUE FINISHLOOP CRECORD PRECORD"
  then formcallgraph(func, src, i + 2, result)
  else if name ="WORDS"_1 
  then formcallgraph(func, src, i + toint(src_(i + 1))+ 2, result)
  else if name = func 
  then formcallgraph(func, src, i + 1, result)
  else formcallgraph(func, src, i + 1, result + arc(func, name))

