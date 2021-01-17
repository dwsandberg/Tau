#!/usr/local/bin/tau ; use doc ; createdoc

Module doc

use seq.char

use displaytextgraph

use fileio

use format

use groupparagraphs

use main2

use mangle

use seq.mytype

use mytype

use pretty

use standard

use textio

use seq.arc.word

use set.arc.word

use graph.word

use seq.arcinfo.seq.word

use svggraph.seq.word

use set.word


Function createdoc seq.word // Creates html tau html documentation. Creates file taudocs.html //
let d = gettext."tools/doc.txt" @ +("", addselect.@e)
let x1 = createhtmlfile("doc.html", d)
 // let x2 = createfile("appdoc.html", [ htmlheader + processpara.@(+, addselect,"", gettext."tools/appdoc.txt")])//
 let y1 = createhtmlfile("testall.html", htmlcode."testall")
  d

function addselect(s:seq.word)seq.word" &{ select X" + s + " &}"

Function callgraphbetween(libname:seq.word, modulelist:seq.word)seq.word
 // Calls between modules in list of modules. //
 let z = formcallgraph(compile("pass1",libname), 2)
 let a = modulelist @ +(empty:seq.mytype, mytype.@e)
 let arcs = z @ +(empty:seq.arc.word, modarc(a, @e))
  display(toseq.arcs.newgraph.arcs @ +(empty:seq.arcinfo.seq.word, toarcinfo.@e))

Function callgraphwithin(libname:seq.word, modulelist:seq.word)seq.word
 // Calls within modules in list of modules. //
 let g = newgraph.formcallgraph(compile("pass1",libname), 2)
 let nodestoinclude = toseq.nodes.g @ ∪(empty:set.word, filterx(modulelist, @e))
 let g2 = toseq.nodestoinclude @ deletenode(g, @e)
  display(toseq.arcs.g2 @ +(empty:seq.arcinfo.seq.word, toarcinfo.@e))

function filterx(include:seq.word, w:word)set.word
 let p = codedown.w
  if length.p < 2 then empty:set.word
  else if last.p_2 ∈ include then empty:set.word else asset.[ w]

function mytype(w:word)mytype mytype.[ w]

function modarc(s:seq.mytype, a:arc.word)seq.arc.word
 let t1 = codedown.tail.a
 let h1 = codedown.head.a
  if length.t1 < 2 ∨ length.h1 < 2 ∨ t1_2 = h1_2
  ∨ not(mytype.h1_2 ∈ s ∧ mytype.t1_2 ∈ s)then
  empty:seq.arc.word
  else [ arc(merge.readable.tail.a, merge.readable.head.a)]

function toarcinfo(a:arc.word)arcinfo.seq.word arcinfo(readable.tail.a, readable.head.a,"")

function readable(fsig:word)seq.word
 let p = codedown.fsig
  if length.p = 1 then p_1
  else
   let plist = subseq(p, 3, length.p) @ +(empty:seq.mytype, mytype.@e)
    p_1 + ":" + print.mytype.p_2 + "("
    + plist @ list("",",", print.@e)
    + ")"

Function usegraph(g:graph.word, include:seq.word, exclude:seq.word)seq.word
 let g1 = exclude + exclude @ +("", addabstractpara.@e)
 let g2 = g1 @ deletenode(g, @e)
 let g3 = if include = ""then g2
 else
  let a = include + include @ +("", addabstractpara.@e)
  let b = a @ ∪(empty:set.arc.word, arcstosuccessors(g2, @e))
  newgraph.toseq.b
 let d = toseq.arcs.g3 @ +(empty:seq.arcinfo.seq.word, toarcinfo.@e)
  display.d

function addabstractpara(w:word)word merge([ w] + ".T")

Function testdoc seq.word // callgraphwithin("stdlib","llvm")+ // doclibrary."stdlib"

Function doclibrary(libname:seq.word)seq.word
 // create summary documentation for libraray. //
 let liba = getlibrarysrc.libname 
 let r = liba @ +("", findrestrict.@e)
 let g = newgraph.usegraph(liba,"mod"_1, 1,"?"_1, empty:seq.arc.word)
 let exports =(getlibraryinfo.libname )_3
  docmodule(g, exports, r, liba, 1,"","","")
  + if length.r > 0 then""
  else" &{ select x &section Possibly Unused Functions  &}  &{ select x" + uncalledfunctions.libname + " &}"

* Paragraphs beginning with * are included in documentation.

* If a paragraph in the library module if of the form:* only document <module1 name> <module2 name>... then only those modules named will be documented.

* If a paragraph in the library is of the form:* usegraph exclude <list of modules> include <list of modules> then a use graph will be construction including and excluding the modules listed. Both the exclude and include are optional, but for a large library should be used to restrict the size of the graph. An example of a use graph is included at the end of this module.

function findrestrict(s:seq.word)seq.word
 if subseq(s, 1, 3) = "* only document"then subseq(s, 4, length.s)else""

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
 else if length.lib_i = 0 then docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)
 else if lib_i_1 ∈ "module Module"then
 let modname = lib_i_2
   if not(modname ∈ todoc ∨ length.todoc = 0)then
   docmodule(usegraph, exports, todoc, lib, i + 1,"", funcs, types)
   else
    let leftover = if length.types > 0 ∨ length.funcs > 0 then
    " &br defines types: " + types + funcs
    else""
    let name = [ modname] + if length.lib_i > 2 then".T"else""
     {(leftover + " &{ select x &section  &keyword module" + name + " &}"
     + if modname ∈ exports then"Module" + name + "is exported from library. "else"")
     + " &br Module"
     + name
     + "is used in modules: "
     + alphasort(toseq.arcstopredecessors(usegraph, merge.name) @ +("", tail.@e))
     + docmodule(usegraph, exports, todoc, lib, i + 1, subseq(lib_i, 2, length.lib_i),"","")}
 else if currentmod = ""then docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)
 else if subseq(lib_i, 1, 1) = "*"then
 let a = lib_i
  let toadd =(" &{ select x"
  + if a_2 = "usegraph"_1 then
  let l = findindex("include"_1, a)
   let k = findindex("exclude"_1, a)
    usegraph(usegraph, subseq(a, l + 1, k), subseq(a, k + 1, length.a))
  else subseq(a, 2, length.a))
  + " &}"
   docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs + toadd, types)
 else if lib_i_1 ∈ "Function"then
 let z = getheader.lib_i
  let x = if last.z ∈ "export stub"then subseq(z, 1, length.z - 1)else z
  let toadd =" &{ select x  &keyword" + x + " &}"
   docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs + toadd, types)
 else if subseq(lib_i, 1, 1) = "type"then
 docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types + lib_i_2)
 else docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)

Function uncalledfunctions(libname:seq.word)seq.word
 // List of functions may include indirectly called functions. //
 let g = newgraph.formcallgraph(compile("pass1",libname), 2)
 let sources = toseq.nodes.g @ +("", sources(g, empty:set.word, @e))
  alphasort.sources @ list(""," &br", readable.@e)

* usegraph exclude stdlib seq set

function usegraph(lib:seq.seq.word, kind:word, i:int, currentmod:word, result:seq.arc.word)seq.arc.word
 if i > length.lib then result
 else
  let key = if length.lib_i > 1 then lib_i_1 else"empty"_1
   if key ∈ "module Module"then
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
 else
  let t = callarcs(lib_i, 1, empty:seq.word)
   toseq(asset.subseq(t, 2, length.t) - asset.subseq(t, 1, 1))
   @ +(empty:seq.arc.word, arc(t_1, @e))
   + formcallgraph(lib, i + 1)

function callarcs(s:seq.word, i:int, result:seq.word)seq.word
 if i + 1 > length.s then result
 else
  let this = s_i
   if this = '"'_1 then
   callarcs(s, findindex2('"'_1, s, i + 1) + 1, result)
   else if this = "'"_1 then
   callarcs(s, findindex2("'"_1, s, i + 1) + 1, result)
   else
    let next = s_(i + 1)
     if next ∈ "(:"then
     let j = findindex2(")"_1, s, i + 1)
       if this = "RECORD"_1 then callarcs(s, j + 1, result)
       else
        assert j < length.s report"JKL" + subseq(s, i, length.s)
        let module = gathermod(s, j + 2, [ s_(j + 1)])
        let end = 2 * (length.module - 1) + 1 + j + 1
         callarcs(s, end, result + mangle(subseq(s, i, j), module))
     else if this ∈ "RECORD DEFINE EXITBLOCK BR BLOCK APPLY WORD APPLYP APPLYI APPLYR"then callarcs(s, i + 2, result)
     else if this = "global"_1 then
     // global has strange format. global atype()builtin //
      let atype = gathermod(s, i + 2, [ next])
      let end = 2 * (length.atype - 1) + 1 + i + 1 + //()builtin // 3
       // assert false report"JK"+ subseq(s, end, length.s)// callarcs(s, end, result)
     else if this ∈ " &br FREF"then callarcs(s, i + 1, result)
     else
      let chs = decodeword.this
       assert length.chs > 0 ∧ chs_1 ∈ decodeword.merge."%-0123456789"report"call arcs problem" + this + toword.i + "full text" + s
         callarcs(s, i + 1, result)

function gathermod(s:seq.word, i:int, result:seq.word)seq.word
 if i > length.s ∨ not(s_i = "."_1)then result
 else gathermod(s, i + 2, [ s_(i + 1)] + result)