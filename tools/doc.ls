Module doc

run tools createdoc


use display

use displaytextgraph

use fileio

use format

use graph.word

use libdesc

use libscope

use main

use passcommon

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

Function createdoc seq.word 
 // Creates html tau html documentation. Creates file taudocs.html // 
  let d = @(+, prettyit.newgraph.empty:seq.arc.word,"", gettext."tools/doc.txt")
  let x = createfile("taudoc.html", [ htmlheader + processpara.d])
  let e = @(+, prettyit.newgraph.empty:seq.arc.word,"", gettext."tools/appdoc.txt")
  let x2 = createfile("appdoc.html", [ htmlheader + processpara.e])
  let y = createfile("testall.html", [ htmlheader + processpara.htmlcode."testall"])
  let z = createfile("tools.html", [ htmlheader + processpara.htmlcode."tools"])
  d

function prettyit(usegraph:graph.word, s:seq.word)seq.word 
 if subseq(s, 1, 2)="* usegraph"
  then let l = findindex("include"_1, s)
   let k = findindex("exclude"_1, s)
   {"&{ noformat <h2> Use graph</h2> &}"+ if k > l 
    then usegraph(usegraph, subseq(s, l + 1, k), subseq(s, k + 1, length.s))
    else usegraph(usegraph, subseq(s, l + 1, length.s), subseq(s, k + 1, l))} 
  else"&{ select 1"+ prettyparagraph(defaultcontrol, s)+"&}"

Function htmlcode(libname:seq.word)seq.word 
 let l = tolibdesc(libname_1)
  let g = newgraph.usegraph("mod", l)
  {"&{ noformat <h1> Source code for Library"+ libname +"</h1> &}"+ @(+, ref,"", modules.l)+ @(seperator."&{ noformat <hr> &}", prettymod.g,"", modules.l)}

function ref(m:moddesc)seq.word 
 {"&{ noformat <a href = &quot"+ merge("#"_1, modname.m)+"&quot >"+ modname.m +"</a> &}"}

function prettymod(usegraph:graph.word, m:moddesc)seq.word 
 {"&{ noformat <hr id = &quot"+ modname.m +"&quot > &}"+ @(+, prettyit.usegraph,"", src.m)}

Function callgraphbetween(libname:seq.word, modulelist:seq.word)seq.word 
 // Calls between modules in list of modules. // 
  let x = bindings(libname_1)
  let z = @(+, formcallgraph, empty:seq.arc.word, newcode.x)
  let g = newgraph.@(+, modarc.@(+, mytype, empty:seq.mytype, modulelist), empty:seq.arc.word, z)
  display.@(+, toarcinfo, empty:seq.arcinfo.seq.word, toseq.arcs.g)

Function callgraphwithin(libname:seq.word, modulelist:seq.word)seq.word 
 // Callgraph within modules. // 
  let x = bindings(libname_1)
  let g = newgraph.@(+, formcallgraph, empty:seq.arc.word, newcode.x)
  let nodestoinclude = @(∪, filterx.modulelist, empty:set.word, toseq.nodes.g)
  let g2 = @(deletenode, identity, g, toseq.nodestoinclude)
  display.@(+, toarcinfo, empty:seq.arcinfo.seq.word, toseq.arcs.g2)

function filterx(include:seq.word, w:word)set.word 
 let p = codedown.w 
  if length.p < 2 
  then empty:set.word 
  else if last(p_2)in include then empty:set.word else asset.[ w]

function formcallgraph(sym:syminfo)seq.arc.word 
 formcallgraph(mangled.sym, instruction.sym, 2, empty:seq.arc.word)

function formcallgraph(func:word, s:seq.word, i:int, result:seq.arc.word)seq.arc.word 
 if i > length.s 
  then result 
  else if s_i in"PARA LIT CONST WORD LOCAL FLAT if IDX IDXUC $wordlist FLD RECORD APPLY ADD SET EQL $build comment let assert builtin @"
  then formcallgraph(func, s, i + 2, result)
  else let target = if s_i in"CALL CALLB"
   then s_(i + 2)
   else if s_i ="FREF"_1 then s_(i + 1)else s_i 
  let bump = if s_i in"CALL CALLB"then 3 else 2 
  if func = target 
  then formcallgraph(func, s, i + 2, result)
  else formcallgraph(func, s, i + bump, result + arc(func, target))

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

Function usegraph(kind:seq.word, lib:libdesc)seq.arc.word 
 // for graph of how modules are linked with use clauses. kind ="mod"will use nodes like seq.T, otherwise node names like seq.seq.int will be used. // 
  @(+, usegraph(kind_1), empty:seq.arc.word, modules.lib)

function usegraph(kind:word, m:moddesc)seq.arc.word 
 let name = if length(src(m)_1)> 2 then merge([ modname.m]+".T")else modname.m 
  @(+, usegraph(kind, name), empty:seq.arc.word, uses.m)

function usegraph(kind:word, modname:word, t:mytype)seq.arc.word 
 let a = arc(modname, if kind ="mod"_1 
   then if iscomplex.t then merge([ abstracttype.t]+".T")else abstracttype.t 
   else merge.print.t)
  if tail.a = head.a then empty:seq.arc.word else [ a]

Function doclibrary(libname:seq.word)seq.word 
 // create summary documentation for libraray.  // 
  let lib = tolibdesc(libname_1)
  let r = @(+,findrestrict,"",src.(modules.lib)_1)  
  let g = newgraph.usegraph("mod", lib)
  @(+, docmodule(g, exports.lib,r ),"", modules.lib )+ if length.r > 0 then "" else 
  "&{ select x &section Possibly Unused Functions &} &{ select x"+ uncalledfunctions.libname +"&}"

* Paragraphs beginning with * are included in documentation.

* If a paragraph in the library module if of the form:&{ block * only document <module1 name> <module2 name> ... &} then only those modules named will be documented.

* If a paragraph in the library is of the form:&{ block * usegraph exclude  <list of modules> include <list of modules> &} then a use
graph will be construction including and excluding the modules listed.   Both the exclude and include are optional, but for a large library should be used to restrict
the size of the graph.  An example of a use graph is included at the end of this module.

function findrestrict(s:seq.word) seq.word
 if subseq(s,1,3)="* only document" then subseq(s,4,length.s)
  else ""
  
function docmodule(usegraph:graph.word, exports:seq.word,todoc:seq.word, md:moddesc)seq.word 
   if not(modname.md in todoc &or length.todoc = 0) then "" else 
    let isexported = modname.md in exports 
    let name = [ modname.md]+ if length(src(md)_1)> 2 then".T"else""
  {"&{ select x &section &keyword module"+ name +"&}"+(if isexported 
   then"Module"+ name +"is exported from library. "
   else"")+"&br Module"+ name +"is used in modules: "+ alphasort.@(+, tail,"", toseq.arcstopredecessors(usegraph, merge.name))+ docfunction(usegraph, src.md, 1,"","")}

function docfunction(usegraph:graph.word, s:seq.seq.word, i:int, funcs:seq.word, types:seq.word)seq.word 
 // this is a comment // 
  if i > length.s 
  then"&br defines types: "+ types + funcs 
  else let a = s_i 
  if length.a = 0 
  then docfunction(usegraph, s, i + 1, funcs, types)
  else if a_1 ="*"_1 
  then let newfuncs = funcs +"&{ select x"+(if a_2 ="usegraph"_1 
    then let l = findindex("include"_1, a)
     let k = findindex("exclude"_1, a)
     usegraph(usegraph, subseq(a, l + 1, k), subseq(a, k + 1, length.a))
    else subseq(a, 2, length.a))+"&}"
   docfunction(usegraph, s, i + 1, newfuncs, types)
  else if a_1 ="Function"_1 
  then let t = parse(a, tree("xxx"_1))
   let txt = collectcomments(t_2)
   let t2 = if nosons(t_2)= 0 then t else tree(label.t, [ t_1, tree("stub"_1)]+ subseq(sons.t, 3, nosons.t))
   let b = prettytree(defaultcontrol, t2)
   let idx = findindex("stub"_1, b)
   docfunction(usegraph, s, i + 1, funcs +"&{ select x"+ subseq(b, 1, idx - 1)+(if length.txt > 0 then
    (if length.txt > 10 then "&br" else ". ")+ txt else"")+ subseq(b, idx + 1, length.b)+"&}", types)
  else if a_1 ="type"_1 
  then docfunction(usegraph, s, i + 1, funcs + prettyparagraph(defaultcontrol, a), types + a_2)
  else docfunction(usegraph, s, i + 1, funcs, types)

function collectcomments(t:tree.word)seq.word 
 if label.t ="comment"_1 
  then @(+, label,"", subseq(sons.t, 2, nosons.t))+ collectcomments(t_1)
  else""

Function uncalledfunctions(libname:seq.word)seq.word 
 // List of functions may include indirectly called functions. // 
  let x = bindings(libname_1)
  let g = newgraph.@(+, formcallgraph, empty:seq.arc.word, newcode.x)
  let sources = @(+, sources(g, empty:set.word),"", toseq.nodes.g)
  @(seperator."&br", readable,"", alphasort.sources)

* usegraph exclude stdlib seq set
