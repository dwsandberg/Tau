#!/usr/local/bin/tau ; use doc ; createdoc

; use doc ; createdoc

; use doc ; createdoc

; use pretty ; htmlcode("bug10")

; use doc ; callgraphbetween("stdlib","interperter tausupport mangle")

; use doc ; createdoc

; use doc ; doclibrary."stdlib"

; use doc ; createdoc

Module doc

use displaytextgraph


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

use svggraph.seq.word

use seq.arcinfo.seq.word

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
 for acc = empty:seq.arc.symbolref, a ∈ z do
  let t1 = decode.tail.a
  let h1 = decode.head.a
  if module.t1 = module.h1 then acc
  else if name.module.t1 ∈ modulelist ∧ name.module.h1 ∈ modulelist then acc + a else acc
 /for(acc)
display.for acc = empty:seq.arcinfo.seq.word, @e ∈ toseq.arcs.newgraph.arcs do acc + toarcinfo.@e /for(acc)

Function formcallarcs(libname:seq.word)seq.arc.symbolref
for arcs2 = empty:seq.arc.symbolref, p ∈ prg.compilerfront("text", libname)do
 let tail = symbolref.sym.p
 for arcs = arcs2, sym ∈ code.p do
  if isconst.sym ∨ isspecial.sym ∨ sym = sym.p then arcs else arcs + arc(tail, symbolref.sym)
 /for(arcs)
/for(arcs2)

Function callgraphwithin(libname:seq.word, modulelist:seq.word)seq.word
{ Calls within modules in list of modules. }
let t =
 for arcs2 = empty:seq.arc.symbolref, p ∈ prg.compilerfront("pass1", libname)do
  let tail = symbolref.sym.p
  for arcs = arcs2, sym ∈ code.p do
   if isconst.sym ∨ isspecial.sym ∨ sym = sym.p then arcs else arcs + arc(tail, symbolref.sym)
  /for(arcs)
 /for(arcs2)
let g = newgraph.formcallarcs.libname
let nodesnottoinclude =
 for acc = empty:set.symbolref, @e ∈ toseq.nodes.g do
  let p = decode.@e
  if name.module.p ∈ modulelist then acc else acc + @e
 /for(acc)
let g2 = for acc = g, @e ∈ toseq.nodesnottoinclude do deletenode(acc, @e)/for(acc)
display.for acc = empty:seq.arcinfo.seq.word, @e ∈ toseq.arcs.g2 do acc + toarcinfo.@e /for(acc)

function toarcinfo(a:arc.symbolref)arcinfo.seq.word arcinfo(print.decode.tail.a, print.decode.head.a,"")

Function usegraph(g:graph.word, include:seq.word, exclude:seq.word)seq.word
let g1 =
 exclude + for acc ="", @e ∈ exclude do acc + addabstractpara.@e /for(acc)
let g2 = for acc = g, @e ∈ g1 do deletenode(acc, @e)/for(acc)
let g3 =
 if include = ""then g2
 else
  let a =
   include + for acc ="", @e ∈ include do acc + addabstractpara.@e /for(acc)
  let b = for acc = empty:set.arc.word, @e ∈ a do acc ∪ arcstosuccessors(g2, @e)/for(acc)
  newgraph.toseq.b
let d =
 for acc = empty:seq.arcinfo.seq.word, @e ∈ toseq.arcs.g3 do acc + arcinfo([ tail.@e], [ head.@e],"")/for(acc)
display.d

function addabstractpara(w:word)word merge([ w] + ".T")

Function testdoc seq.word { callgraphwithin("stdlib","llvm")+ } doclibrary."stdlib"

Function doclibrary(libname:seq.word)seq.word
{ create summary documentation for libraray. }
let liba = getlibrarysrc.libname
let exports =liba_3
let todoc =
 for acc ="", s ∈ liba do
  if subseq(s, 1, 3) = "* only document"then acc + subseq(s, 4, length.s)else acc
 /for(if isempty.acc then exports else acc /if)
let g = newgraph.usegraph(liba,"mod"_1, 1,"?"_1, empty:seq.arc.word)
modindex.todoc + docmodule(g, exports, todoc, liba, 1,"","","")

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

function docmodule(usegraph:graph.word
, exports:seq.word
, todoc:seq.word
, lib:seq.seq.word
, i:int
, currentmod:seq.word
, funcs:seq.word
, types:seq.word
)seq.word
if i > length.lib then
 if length.types > 0 ∨ length.funcs > 0 then" /br defines types: " + types + funcs
 else""
else if length.lib_i = 0 then docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)
else if lib_i_1 ∈ "module Module"then
 let modname = lib_i_2
 if not(modname ∈ todoc ∨ length.todoc = 0)then
  docmodule(usegraph, exports, todoc, lib, i + 1,"", funcs, types)
 else
  let leftover =
   if length.types > 0 ∨ length.funcs > 0 then" /br defines types: " + types + funcs
   else""
  let name = [ modname] + if length.lib_i > 2 then".T"else""
  leftover + '  /< noformat <hr id ="' + modname + '">  /> '
  + " /< /section  /keyword module"
  + name
  + " />"
  + if modname ∈ exports then"Module" + name + "is exported from library. "
  else""/if
  + " /br Module"
  + name
  + "is used in modules: "
  + alphasort.for acc ="", @e ∈ toseq.arcstopredecessors(usegraph, merge.name)do acc + tail.@e /for(acc)
  + docmodule(usegraph
  , exports
  , todoc
  , lib
  , i + 1
  , subseq(lib_i, 2, length.lib_i)
  ,""
  ,""
  )
else if currentmod = ""then
 docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)
else if subseq(lib_i, 1, 1) = "*"then
 let a = lib_i
 let toadd =
 " /p"
  + if a_2 = "usegraph"_1 then
   let l = findindex("include"_1, a)
   let k = findindex("exclude"_1, a)
   usegraph(usegraph, subseq(a, l + 1, k), subseq(a, k + 1, length.a))
  else subseq(a, 2, length.a)
 docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs + toadd, types)
else if lib_i_1 ∈ "Function Export"then
 let z = getheader.lib_i
 let toadd =
 " /p  /keyword"
  + if subseq(lib_i, length.z, length.z + 1) = "{ *"then
   z >> 1 + "{" + subseq(lib_i, length.z + 2, findindex("}"_1, lib_i))
  else if last.z ∈ "stub"then z >> 1 else z
 docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs + toadd, types)
else if subseq(lib_i, 1, 1) = "type"then
 docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types + lib_i_2)
else docmodule(usegraph, exports, todoc, lib, i + 1, currentmod, funcs, types)

Function uncalledfunctions(libname:seq.word)seq.word
{ List of functions may include indirectly called functions. }
let g = newgraph.formcallarcs.libname
let sources =
 for acc = empty:seq.symbolref, @e ∈ toseq.nodes.g do acc + sources(g, empty:set.symbolref, @e)/for(acc)
for acc ="", @e ∈ sources do acc + print.decode.@e + " /br"/for(acc)

* usegraph exclude stdlib seq set

function usegraph(lib:seq.seq.word, kind:word, i:int, currentmod:word, result:seq.arc.word)seq.arc.word
if i > length.lib then result
else
 let key = if length.lib_i > 1 then lib_i_1 else"empty"_1
 if key ∈ "module Module"then
  usegraph(lib, kind, i + 1, merge.subseq(lib_i, 2, length.lib_i), result)
 else if key = "use"_1 then
  let m =
   if length.lib_i = 2 then lib_i_2
   else if kind = "mod"_1 then merge([ lib_i_2] + ".T")
   else merge.subseq(lib_i, 2, length.lib_i)
  if currentmod = m then usegraph(lib, kind, i + 1, currentmod, result)
  else usegraph(lib, kind, i + 1, currentmod, result + arc(currentmod, m))
 else usegraph(lib, kind, i + 1, currentmod, result) 