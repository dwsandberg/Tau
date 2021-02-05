#!/usr/local/bin/tau ; use doc ; createdoc

Module doc

use displaytextgraph

use fileio

use format

use groupparagraphs

use main2

use mangle

use mytype

use pretty

use standard

use textio

use seq.char

use seq.mytype

use graph.word

use set.word

use seq.arc.word

use set.arc.word

use svggraph.seq.word

use seq.arcinfo.seq.word

Function createdoc seq.word \\ Creates html tau html documentation. Creates file taudocs.html \\
let d = {(for(@e ∈ gettext."tools/doc.txt", acc ="")acc + addselect.@e)}
let x1 = createhtmlfile("doc.html", d)
 \\ let x2 = createfile("appdoc.html", [ htmlheader + processpara.@(+, addselect,"", gettext."tools/appdoc.txt")])\\
 // let y1 = createhtmlfile("testall.html", htmlcode."testall") //
  d

function addselect(s:seq.word)seq.word" &{ select X" + s + " &}"

Function callgraphbetween(libname:seq.word, modulelist:seq.word)seq.word
 \\ Calls between modules in list of modules. \\
 let z = formcallgraph(compile("pass1",libname), 2)
 let a = {(for(@e ∈ modulelist, acc = empty:seq.mytype)acc + mytype.@e)}
 let arcs = {(for(@e ∈ z, acc = empty:seq.arc.word)acc + modarc(a, @e))}
  display
  .{(for(@e ∈ toseq.arcs.newgraph.arcs, acc = empty:seq.arcinfo.seq.word)acc + toarcinfo.@e)}

Function callgraphwithin(libname:seq.word, modulelist:seq.word)seq.word
 \\ Calls within modules in list of modules. \\
 let g = newgraph.formcallgraph(compile("pass1",libname), 2)
 let nodestoinclude = {(for(@e ∈ toseq.nodes.g, acc = empty:set.word)acc ∪ filterx(modulelist, @e))}
 let g2 = { for(@e ∈ toseq.nodestoinclude, acc = g)deletenode(acc, @e)}
  display
  .{(for(@e ∈ toseq.arcs.g2, acc = empty:seq.arcinfo.seq.word)acc + toarcinfo.@e)}

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
   let plist = {(for(@e ∈ subseq(p, 3, length.p), acc = empty:seq.mytype)acc + mytype.@e)}
    p_1 + ":" + print.mytype.p_2 + "("
    + { for(@e ∈ plist, acc ="")list(acc,",", print.@e)}
    + ")"

Function usegraph(g:graph.word, include:seq.word, exclude:seq.word)seq.word
 let g1 = exclude + {(for(@e ∈ exclude, acc ="")acc + addabstractpara.@e)}
 let g2 = { for(@e ∈ g1, acc = g)deletenode(acc, @e)}
 let g3 = if include = ""then g2
 else
  let a = include + {(for(@e ∈ include, acc ="")acc + addabstractpara.@e)}
  let b = {(for(@e ∈ a, acc = empty:set.arc.word)acc ∪ arcstosuccessors(g2, @e))}
  newgraph.toseq.b
 let d = {(for(@e ∈ toseq.arcs.g3, acc = empty:seq.arcinfo.seq.word)acc + toarcinfo.@e)}
  display.d

function addabstractpara(w:word)word merge([ w] + ".T")

Function testdoc seq.word \\ callgraphwithin("stdlib","llvm")+ \\ doclibrary."stdlib"

Function doclibrary(libname:seq.word)seq.word
 \\ create summary documentation for libraray. \\
 let liba = getlibrarysrc.libname 
 let r = {(for(@e ∈ liba, acc ="")acc + findrestrict.@e)}
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
     + alphasort.{(for(@e ∈ toseq.arcstopredecessors(usegraph, merge.name), acc ="")acc + tail.@e)}
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
 \\ List of functions may include indirectly called functions. \\
 let g = newgraph.formcallgraph(compile("pass1",libname), 2)
 let sources = {(for(@e ∈ toseq.nodes.g, acc ="")acc + sources(g, empty:set.word, @e))}
  { for(@e ∈ alphasort.sources, acc ="")list(acc," &br", readable.@e)}

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
   {(for(@e ∈ toseq(asset.subseq(t, 2, length.t) - asset.subseq(t, 1, 1)), acc = empty:seq.arc.word)acc + arc(t_1, @e))}
   + formcallgraph(lib, i + 1)
   
function findindex2(w:word, s:seq.word, i:int)int
 if i > length.s then i
 else if s_i = w then i else findindex2(w, s, i + 1)

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
     else if this ∈ "DEFINE EXITBLOCK BR BLOCK APPLY WORD APPLYP APPLYI APPLYR "then callarcs(s, i + 2, result)
     else if this ∈ " &br FREF Litfalse Littrue "then callarcs(s, i + 1, result)
     else
      let chs = decodeword.this
       assert length.chs > 0 ∧ chs_1 ∈ decodeword.merge."%-0123456789"report"call arcs problem" + this + toword.i + "full text" + s
         callarcs(s, i + 1, result)

function gathermod(s:seq.word, i:int, result:seq.word)seq.word
 if i > length.s ∨ not(s_i = "."_1)then result
 else gathermod(s, i + 2, [ s_(i + 1)] + result)