#!/usr/local/bin/tau  ; use doc ; callgraphwithin("tools","doc")


; use doc ; createdoc

; use doc ; doclibrary."stdlib"



; use doc ; createdoc

Module doc

use displaytextgraph

use fileio

use format

use groupparagraphs

use main2

use mangle

use mytype

use symbol

use pretty

use standard

use textio

use fileio

use seq.char

use seq.mytype

use graph.word

use set.word

use seq.arc.word

use set.arc.word

use svggraph.seq.word

use seq.arcinfo.seq.word

Function createdoc seq.word { Creates html tau html documentation. Creates file taudocs.html }
let d = for acc ="", @e = gettext."tools/doc.txt"do acc + addselect.@e /for(acc)
let x1 = createfile("doc.html", toUTF8bytes.d)
{ let x2 = createfile("appdoc.html", [ htmlheader + processpara.@(+, addselect,"", gettext."tools/appdoc.txt")])}
 { let y1 = createhtmlfile("testall.html", htmlcode."testall")} d

use pro2gram

function addselect(s:seq.word)seq.word 
 if not.isempty.s /and first.s=first."/section" then  "/< /section " + s << 1 + " />" else "/p " + s   

Function callgraphbetween(libname:seq.word, modulelist:seq.word)seq.word
 { Calls between modules in list of modules. }
 let z = formcallarcs.libname
 let a = for acc = empty:seq.mytype, @e = modulelist do acc + mytype.@e /for(acc)
 let arcs = for acc = empty:seq.arc.word, @e = z do acc + modarc(a, @e)/for(acc)
  display.for acc = empty:seq.arcinfo.seq.word, @e = toseq.arcs.newgraph.arcs do acc + toarcinfo.@e /for(acc)

Function formcallarcs(libname:seq.word) seq.arc.word
for  arcs2=empty:seq.arc.word,  p=  tosymdefs.prg.compilerfront("pass1",libname) do
     let tail=mangledname.sym.p
     for arcs=arcs2 ,  sym=code.p do
        if isconst.sym /or isspecial.sym /or sym=sym.p then arcs else  arcs+arc(tail,mangledname.sym)
     /for(arcs)
     /for(arcs2)

Function callgraphwithin(libname:seq.word, modulelist:seq.word)seq.word
 { Calls within modules in list of modules. }
 let t= for  arcs2=empty:seq.arc.word,  p=  tosymdefs.prg.compilerfront("pass1",libname) do
     let tail=mangledname.sym.p
     for arcs=arcs2 ,  sym=code.p do
        if isconst.sym /or isspecial.sym /or sym=sym.p then arcs else  arcs+arc(tail,mangledname.sym)
     /for(arcs)
     /for(arcs2)
  let g = newgraph.formcallarcs.libname
 let nodestoinclude = for acc = empty:set.word, @e = toseq.nodes.g do acc ∪ filterx(modulelist, @e)/for(acc)
 let g2 = for acc = g, @e = toseq.nodestoinclude do deletenode(acc, @e)/for(acc)
  display.for acc = empty:seq.arcinfo.seq.word, @e = toseq.arcs.g2 do acc + toarcinfo.@e /for(acc)

function filterx(include:seq.word, w:word)set.word
let p = codedown.w
 if length.p < 2 then empty:set.word
 else if last.p_2 ∈ include then empty:set.word else asset.[ w]

function mytype(w:word)mytype TypeFromOldTyperep.[ w]

function modarc(s:seq.mytype, a:arc.word)seq.arc.word
let t1 = codedown.tail.a
let h1 = codedown.head.a
 if length.t1 < 2 ∨ length.h1 < 2 ∨ t1_2 = h1_2
 ∨ not(TypeFromOldTyperep.h1_2 ∈ s ∧ TypeFromOldTyperep.t1_2 ∈ s)then
  empty:seq.arc.word
 else [ arc(merge.readable.tail.a, merge.readable.head.a)]

function toarcinfo(a:arc.word)arcinfo.seq.word arcinfo(readable.tail.a, readable.head.a,"")

function readable(fsig:word)seq.word
let p = codedown.fsig
 if length.p = 1 then p_1
 else
  let plist = for acc = empty:seq.mytype, @e = subseq(p, 3, length.p)do acc + TypeFromOldTyperep.@e /for(acc)
   p_1 + ":" + print.TypeFromOldTyperep.p_2 + "("
   + for acc ="", @e = plist do list(acc,",", print.@e)/for(acc)
   + ")"

Function usegraph(g:graph.word, include:seq.word, exclude:seq.word)seq.word
let g1 = exclude + for acc ="", @e = exclude do acc + addabstractpara.@e /for(acc)
let g2 = for acc = g, @e = g1 do deletenode(acc, @e)/for(acc)
let g3 = if include = ""then g2
else
 let a = include + for acc ="", @e = include do acc + addabstractpara.@e /for(acc)
 let b = for acc = empty:set.arc.word, @e = a do acc ∪ arcstosuccessors(g2, @e)/for(acc)
  newgraph.toseq.b
let d = for acc = empty:seq.arcinfo.seq.word, @e = toseq.arcs.g3 do acc + toarcinfo.@e /for(acc)
 display.d

function addabstractpara(w:word)word merge([ w] + ".T")

Function testdoc seq.word { callgraphwithin("stdlib","llvm")+ } doclibrary."stdlib"

Function doclibrary(libname:seq.word)seq.word
 { create summary documentation for libraray. }
 let liba = getlibrarysrc.libname
 let r = for acc ="", @e = liba do acc + findrestrict.@e /for(acc)
 let g = newgraph.usegraph(liba,"mod"_1, 1,"?"_1, empty:seq.arc.word)
 let exports =(getlibraryinfo.libname)_3
  docmodule(g, exports, r, liba, 1,"","","")
  + if length.r > 0 then""
  else" /<  /section Possibly Unused Functions  />  /< select x" + uncalledfunctions.libname + " />"

* Paragraphs beginning with * are included in documentation.

* If a paragraph in the library module if of the form:* only document <module1 name> <module2 name>... then only those modules named will be documented.

* If a paragraph in the library is of the form:* usegraph exclude <list of modules> include <list of modules> then a use graph will be construction including and excluding the modules listed. Both the exclude and include are optional, but for a large library should be used to restrict the size of the graph. An example of a use graph is included at the end of this module.

function findrestrict(s:seq.word)seq.word
 if subseq(s, 1, 3) = "* only document"then subseq(s, 4, length.s)else""

function plist(t:seq.word, i:int, parano:int, names:seq.word)seq.word
 if i = 1 then
  if length.names > 0 then
   "("
   + if names_parano = ":"_1 then""else [ names_parano] + ":"/if
   + t_i
   + plist(t, i + 1, parano + 1, names)
  else t
 else if t_i = ".a"_1 ∨ t_i = ". a"_1 then
  subseq(t, i, i + 1) + plist(t, i + 2, parano, names)
 else if parano ≤ length.names then
  ","
  + if names_parano = ":"_1 then""else [ names_parano] + ":"/if
  + t_i
  + plist(t, i + 1, parano + 1, names)
 else")" + subseq(t, i, length.t)

function docmodule(usegraph:graph.word, exports:seq.word, todoc:seq.word, lib:seq.seq.word, i:int, currentmod:seq.word, funcs:seq.word, types:seq.word)seq.word
 if i > length.lib then
  if length.types > 0 ∨ length.funcs > 0 then
   " /br defines types: " + types + funcs
  else""
 else if length.lib_i = 0 then docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)
 else if lib_i_1 ∈ "module Module"then
 let modname = lib_i_2
  if not(modname ∈ todoc ∨ length.todoc = 0)then
   docmodule(usegraph, exports, todoc, lib, i + 1,"", funcs, types)
  else
   let leftover = if length.types > 0 ∨ length.funcs > 0 then
    " /br defines types: " + types + funcs
   else""
   let name = [ modname] + if length.lib_i > 2 then".T"else""
    leftover + " /< /section  /keyword module" + name + " />"
    + if modname ∈ exports then"Module" + name + "is exported from library. "else""/if
    + " /br Module"
    + name
    + "is used in modules: "
    + alphasort.for acc ="", @e = toseq.arcstopredecessors(usegraph, merge.name)do acc + tail.@e /for(acc)
    + docmodule(usegraph, exports, todoc, lib, i + 1, subseq(lib_i, 2, length.lib_i),"","")
 else if currentmod = ""then docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)
 else if subseq(lib_i, 1, 1) = "*"then
 let a = lib_i
 let toadd =" /< select x"
 + if a_2 = "usegraph"_1 then
 let l = findindex("include"_1, a)
 let k = findindex("exclude"_1, a)
  usegraph(usegraph, subseq(a, l + 1, k), subseq(a, k + 1, length.a))
 else subseq(a, 2, length.a)/if
 + " />"
  docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs + toadd, types)
 else if lib_i_1 ∈ "Function"then
 let z = getheader.lib_i
 let x = if last.z ∈ "export stub"then subseq(z, 1, length.z - 1)else z
 let toadd =" /p  /keyword" + x  
  docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs + toadd, types)
 else if subseq(lib_i, 1, 1) = "type"then
  docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types + lib_i_2)
 else docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)

Function uncalledfunctions(libname:seq.word)seq.word
 { List of functions may include indirectly called functions. }
 let g = newgraph.formcallarcs.libname
 let sources = for acc ="", @e = toseq.nodes.g do acc + sources(g, empty:set.word, @e)/for(acc)
  for acc ="", @e = alphasort.sources do list(acc," /br", readable.@e)/for(acc)

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

