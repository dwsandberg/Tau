Module doc

/use display

use displaytextgraph

use fileio

use format

use libscope

use main2

use seq.mytype

use newpretty 

use stdlib

use textio

use seq.arc.word

use set.arc.word

use graph.word

use seq.arcinfo.seq.word

use svggraph.seq.word

use set.word

use seq.tree.word

use tree.word

Function createdoc seq.word // Creates html tau html documentation. Creates file taudocs.html //
let d = @(+, addselect,"", gettext."tools/doc.txt")
  let x1 = createfile("doc.html",   htmlheader + processpara.d )  
 // let x2 = createfile("appdoc.html", [ htmlheader + processpara.@(+, addselect,"", gettext."tools/appdoc.txt")])//
   let y1 = createfile("testall.html",   htmlheader + processpara.htmlcode."testall")  
  d

function addselect(s:seq.word)seq.word" &{ select X" + s + " &}"

Function callgraphbetween(libname:seq.word, modulelist:seq.word)seq.word
 // Calls between modules in list of modules. //
 let z = formcallgraph(firstPass.libname_1, 2)
 let g = newgraph.@(+, modarc(@(+, mytype, empty:seq.mytype, modulelist)), empty:seq.arc.word, z)
  display.@(+, toarcinfo, empty:seq.arcinfo.seq.word, toseq.arcs.g)

Function callgraphwithin(libname:seq.word, modulelist:seq.word)seq.word
 // Calls within modules in list of modules. //
 let g = newgraph.formcallgraph(firstPass.libname_1, 2)
 let nodestoinclude = @(∪, filterx(modulelist), empty:set.word, toseq.nodes.g)
 let g2 = @(deletenode, identity, g, toseq.nodestoinclude)
  display.@(+, toarcinfo, empty:seq.arcinfo.seq.word, toseq.arcs.g2)

function filterx(include:seq.word, w:word)set.word
 let p = codedown.w
  if length.p < 2 then empty:set.word
  else if last.p_2 in include then empty:set.word else asset.[ w]

function mytype(w:word)mytype mytype.[ w]

function modarc(s:seq.mytype, a:arc.word)seq.arc.word
 let t1 = codedown.tail.a
 let h1 = codedown.head.a
  if length.t1 < 2 ∨ length.h1 < 2 ∨ t1_2 = h1_2
  ∨ not(mytype.h1_2 in s ∧ mytype.t1_2 in s)then
  empty:seq.arc.word
  else [ arc(merge.readable.tail.a, merge.readable.head.a)]

function toarcinfo(a:arc.word)arcinfo.seq.word arcinfo(readable.tail.a, readable.head.a,"")

function readable(fsig:word)seq.word
 let p = codedown.fsig
  if length.p = 1 then p_1
  else
   let plist = @(+, mytype, empty:seq.mytype, subseq(p, 3, length.p))
    p_1 + ":" + print.mytype.p_2 + "("
    + @(seperator(","), print,"", plist)
    + ")"

Function usegraph(g:graph.word, include:seq.word, exclude:seq.word)seq.word
 let g2 = @(deletenode, identity, g, exclude + @(+, addabstractpara,"", exclude))
 let g3 = if include = ""then g2
 else
  newgraph.toseq.@(∪, arcstosuccessors(g2), empty:set.arc.word, include + @(+, addabstractpara,"", include))
  display.@(+, toarcinfo, empty:seq.arcinfo.seq.word, toseq.arcs.g3)

function addabstractpara(w:word)word merge([ w] + ".T")

Function doclibrary(libname:seq.word)seq.word
 // create summary documentation for libraray. //
 let lib = firstPass.libname_1
 let r = @(+, findrestrict,"", lib)
 let g = newgraph.usegraph(lib,"mod"_1, 1,"?"_1, empty:seq.arc.word)
 let libclause = lib_1
 let e = findindex("exports"_1, libclause, 3)
 let exports = subseq(libclause, e + 1, length.libclause)
  docmodule(g, exports, r, lib, 1,"","","")
  + if length.r > 0 then""
  else" &{ select x &section Possibly Unused Functions  &}  &{ select x" + uncalledfunctions.libname + " &}"

@(+, +(" &br  &br"),"", lib)

* Paragraphs beginning with * are included in documentation.

* If a paragraph in the library module if of the form:* only document <module1 name> <module2 name>... then only those modules named will be documented.

* If a paragraph in the library is of the form:* usegraph exclude <list of modules> include <list of modules> then a use graph will be construction including and excluding the modules listed. Both the exclude and include are optional, but for a large library should be used to restrict the size of the graph. An example of a use graph is included at the end of this module.

function findrestrict(s:seq.word)seq.word
 if subseq(s, 1, 3) = "skip * only document"then subseq(s, 4, length.s)else""

function plist(t:seq.word, i:int, parano:int, names:seq.word)seq.word
 if i = 1 then
 if length.names > 0 then
  ("("
   + if names_parano = ":"_1 then""else [ names_parano] + ":")
   + t_i
   + plist(t, i + 1, parano + 1, names)
  else t
 else if t_i = ".a"_1 ∨ t_i = ". a"_1 then
 subseq(t, i, i + 1) + plist(t, i + 2, parano, names)
 else if parano ≤ length.names then
 (","
  + if names_parano = ":"_1 then""else [ names_parano] + ":")
  + t_i
  + plist(t, i + 1, parano + 1, names)
 else")" + subseq(t, i, length.t)

function docmodule(usegraph:graph.word, exports:seq.word, todoc:seq.word, lib:seq.seq.word, i:int, currentmod:seq.word, funcs:seq.word, types:seq.word)seq.word
 if i > length.lib then
 if length.types > 0 ∨ length.funcs > 0 then
  " &br defines types: " + types + funcs
  else""
 else if lib_i_1 = "module"_1 then
 let modname = lib_i_2
   if not(modname in todoc ∨ length.todoc = 0)then
   docmodule(usegraph, exports, todoc, lib, i + 1,"", funcs, types)
   else
    let leftover = if length.types > 0 ∨ length.funcs > 0 then
    " &br defines types: " + types + funcs
    else""
    let name = [ modname] + if length.lib_i > 2 then".T"else""
     {(leftover + " &{ select x &section  &keyword module" + name + " &}"
     + if modname in exports then"Module" + name + "is exported from library. "else"")
     + " &br Module"
     + name
     + "is used in modules: "
     + alphasort.@(+, tail,"", toseq.arcstopredecessors(usegraph, merge.name))
     + docmodule(usegraph, exports, todoc, lib, i + 1, subseq(lib_i, 2, length.lib_i),"","")}
 else if currentmod = ""then docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)
 else if subseq(lib_i, 1, 2) = "skip *"then
 let a = subseq(lib_i, 2, length.lib_i)
  let toadd =(" &{ select x"
  + if a_2 = "usegraph"_1 then
  let l = findindex("include"_1, a)
   let k = findindex("exclude"_1, a)
    usegraph(usegraph, subseq(a, l + 1, k), subseq(a, k + 1, length.a))
  else subseq(a, 2, length.a))
  + " &}"
   docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs + toadd, types)
 else if lib_i_1 in "Parsedfunc"then
 let z = lib_i
  let nopara = toint.z_4
  let headlength = toint.z_2
  let toadd =" &{ select x  &keyword Function" + z_3
  + plist(subseq(z, 5, headlength + 2 - nopara), 1, 1, subseq(z, headlength + 2 - nopara + 1, headlength + 2))
  + " &}"
   docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs + toadd, types)
 else if lib_i_1 in "record encoding sequence"then
 docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types + lib_i_2)
 else if subseq(lib_i, 1, 2) = "skip type"then
 docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types + lib_i_3)
 else docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)

Function uncalledfunctions(libname:seq.word)seq.word
 // List of functions may include indirectly called functions. //
 let g = newgraph.formcallgraph(firstPass.libname_1, 2)
 let sources = @(+, sources(g, empty:set.word),"", toseq.nodes.g)
  @(seperator(" &br"), readable,"", alphasort.sources)

* usegraph exclude stdlib seq set

function usegraph(lib:seq.seq.word, kind:word, i:int, currentmod:word, result:seq.arc.word)seq.arc.word
 if i > length.lib then result
 else
  let key = lib_i_1
   if key = "module"_1 then
   usegraph(lib, kind, i + 1, merge.subseq(lib_i, 2, length.lib_i), result)
   else if key = "use"_1 then
   let m = if length.lib_i = 2 then lib_i_2
    else if kind = "mod"_1 then merge([ lib_i_2] + ".T")
    else merge.subseq(lib_i, 2, length.lib_i)
     if currentmod = m then usegraph(lib, kind, i + 1, currentmod, result)
     else usegraph(lib, kind, i + 1, currentmod, result + arc(currentmod, m))
   else usegraph(lib, kind, i + 1, currentmod, result)

function formcallgraph(lib:seq.seq.word, i:int)seq.arc.word
 if i > length.lib then empty:seq.arc.word
 else if lib_i_1 in "Parsedfunc parsedfunc"then
 let j = toint.lib_i_2 + 3
   if lib_i_j = "unknown"_1 then formcallgraph(lib, i + 1)
   else
    formcallgraph(lib_i_j, lib_i, j + 1, empty:seq.arc.word)
    + formcallgraph(lib, i + 1)
 else formcallgraph(lib, i + 1)

function formcallgraph(func:word, src:seq.word, i:int, result:seq.arc.word)seq.arc.word
 if i > length.src then result
 else
  let name = src_i
   if name in "IDXUC CALLIDX STATE PROCESS2 FREF EQL if VERYSIMPLE"then formcallgraph(func, src, i + 1, result)
   else if name in "LIT PARAM LOCAL WORD SET define RECORD APPLY LOOPBLOCK STKRECORD CONTINUE FINISHLOOP CRECORD PRECORD"then
   formcallgraph(func, src, i + 2, result)
   else if name in "WORDS COMMENT"then
   formcallgraph(func, src, i + toint.src_(i + 1) + 2, result)
   else if name = func then formcallgraph(func, src, i + 1, result)
   else formcallgraph(func, src, i + 1, result + arc(func, name))