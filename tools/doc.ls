Module doc

use UTF8

use format

use frontcmd

use libraryModule

use pretty

use standard

use symbol2

use textio

use wordgraph

use seq.char

use seq.mytype

use graph.symbol

use seq.symbol

use set.symbol

use svg2graph.symbol

use graph.symbolref

use seq.symbolref

use set.symbolref

use graph.word

use set.word

use seq.arc.symbol

use seq.arc.symbolref

use set.arc.symbolref

use seq.arc.word

use set.arc.word

use seq.seq.word

use svg2graph.seq.word

Function htmlcode(libname:seq.word)seq.word {OPTION INLINE}
let p = 
 prettyfile(true
 , " /< noformat <hr id=" + dq."T" + ">  />  /keyword"
 , getlibrarysrc.libname << 1
 )
let modules = 
 for txt = "", state = 0, name = "1"_1, idx = 1, d ∈ p do
  if d ∈ " /keyword"then next(txt, 1, name, idx + 1)
  else if state = 1 ∧ d ∈ "Module"then next(txt, 2, name, idx + 1)
  else if state = 2 then next(txt, 3, d, idx + 1)
  else if state = 3 then next(txt + name, 0, name, idx + 1)else next(txt, 0, name, idx + 1)
 /for(txt)
" /< noformat <h1> Source code for Library" + libname + "</h1>  />"
+ for acc = "", modname ∈ modules do
 acc + " /< noformat <a href=" + dq.[merge.["#"_1, modname]] + ">"
 + modname
 + "</a>  />"
/for(acc + p)

Function formatdoc(args:seq.word)seq.word
{OPTION INLINE}
prettyfile(false, "", breakparagraph.getfile:UTF8(args + ".txt"))

Function createdoc seq.word
{Creates html tau html documentation. Creates file taudocs.html}
let d = prettyfile(false, "", breakparagraph.getfile:UTF8("tools/doc.txt"))
let x1 = createfile("taudoc.html", toseqbyte(toUTF8.htmlheader + HTMLformat.d))
let d2 = prettyfile(false, "", breakparagraph.getfile:UTF8("tools/install.txt"))
let x2 = createfile("install.html", toseqbyte(toUTF8.htmlheader + HTMLformat.d2))
{let x2=createfile("appdoc.html", [htmlheader+processpara.@(+, addselect, "", gettext."tools/appdoc.txt")]
)}
{let y1=createhtmlfile("testall.html", htmlcode."testall")}
let y1 = 
 createfile("stdlib.html", toseqbyte(toUTF8.htmlheader + HTMLformat.doclibrary."stdlib"))
d

Function callgraphbetween(prg:seq.symdef, modulelist:seq.word)seq.word
{Calls between modules in list of modules. }
let z = formcallarcs.prg
let arcs = 
 for acc = empty:seq.arc.symbol, a ∈ z do
  let t1 = tail.a
  let h1 = head.a
  if module.t1 = module.h1 then acc
  else if name.module.t1 ∈ modulelist ∧ name.module.h1 ∈ modulelist then acc + arc(t1, h1)else acc
 /for(acc)
drawgraph.newgraph.arcs

function formcallarcs(prg:seq.symdef)seq.arc.symbol
for arcs2 = empty:seq.arc.symbol, p ∈ prg do
 let tail = decode.symbolref.sym.p
 for arcs = arcs2, sym ∈ code.p do
  if isconst.sym ∨ isspecial.sym ∨ sym = sym.p then arcs else arcs + arc(tail, decode.symbolref.sym)
 /for(arcs)
/for(arcs2)

Function callgraphwithin(prg:seq.symdef, modulelist:seq.word)seq.word
{Calls within modules in list of modules. }
let g = newgraph.formcallarcs.prg
let nodesnottoinclude = 
 for acc = empty:set.symbol, @e ∈ toseq.nodes.g do if name.module.@e ∈ modulelist then acc else acc + @e /for(acc)
let g2 = for acc = g, @e ∈ toseq.nodesnottoinclude do deletenode(acc, @e)/for(acc)
drawgraph.g2

Function doclibrary(libname:seq.word)seq.word
{create summary documentation for libraray. }
let liba = getlibrarysrc.libname
let exports = break(liba_1, "exports", true)_2 << 1
let todoc = 
 for acc = "", s ∈ liba do
  if subseq(s, 1, 3) = "* only document"then acc + subseq(s, 4, length.s)else acc
 /for(if isempty.acc then exports else acc /if)
let g = newgraph.usegraph(liba, "mod"_1)
modindex.todoc + docmodule(g, exports, todoc, liba)

function modindex(mods:seq.word)seq.word
for txt = "", modname ∈ mods do
 txt + " /< noformat <a href=" + dq.[merge.["#"_1, modname]] + ">"
 + modname
 + "</a>  />"
/for(txt)

* Paragraphs beginning with * are included in documentation.

* If a paragraph in the library module is of the form:* only document <module1 name> <module2 name>... then only those modules 
named will be documented.

* If a paragraph in the library is of the form:* usegraph exclude <list of modules> include <list of modules> then a use graph 
will be construction including and excluding the modules listed. Both the exclude and include are optional, but for a large 
library should be used to restrict the size of the graph. An example of a use graph is included at the end of this module.

Function uncalledfunctions(prg:seq.symdef)seq.word
{List of functions may include indirectly called functions. }
let g = newgraph.formcallarcs.prg
let sources = 
 for acc = empty:seq.symbol, @e ∈ toseq.nodes.g do acc + sources(g, empty:set.symbol, @e)/for(acc)
for acc = "", @e ∈ sources do acc + print.@e + " /br"/for(acc)

* usegraph exclude standard seq set UTF8 stack graph otherseq

function usegraph(lib:seq.seq.word, kind:word)seq.arc.word
for currentmod = "?"_1, result = empty:seq.arc.word, p ∈ lib do
 if isempty.p then next(currentmod, result)
 else if first.p ∈ "module Module"then next(p_2, result)
 else if first.p ∈ "use"then
  let m = 
   if length.p = 2 then p_2
   else if kind = "mod"_1 then p_2 else merge(p << 1)
  next(currentmod
  , if currentmod = m ∨ currentmod ∈ "?"then result else result + arc(currentmod, m)
  )
 else next(currentmod, result)
/for(result)

Function usegraphcmd(library:seq.word, include:seq.word, exclude:seq.word)seq.word
let usegraph = usegraph(getlibrarysrc.library, "mod"_1)
drawgraph(usegraph, asset.include, asset.exclude)

function docmodule(usegraph:graph.word, exports:seq.word, todoc:seq.word, lib:seq.seq.word)seq.word
for acc = ""
, currentmod = "?"
, funcs = ""
, types = ""
, p ∈ lib
do
 if isempty.p then next(acc, currentmod, funcs, types)
 else if first.p ∈ "module Module"then
  let modname = p_2
  if modname ∉ todoc then next(acc, currentmod, funcs, types)
  else
   let leftover = 
    if length.types > 0 ∨ length.funcs > 0 then" /br defines types: " + types + funcs
    else""
   let name = [modname] + if length.p > 2 then".T"else""
   next(acc + leftover + " /< noformat <hr id=" + dq.[modname] + ">  />"
   + " /< /section  /keyword module"
   + name
   + " />"
   + if modname ∈ exports then"Module" + name + "is exported from library. "
   else""/if
   + " /br Module"
   + name
   + "is used in modules: "
   + alphasort.for acc2 = "", @e ∈ toseq.arcstopredecessors(usegraph, merge.name)do acc2 + tail.@e /for(acc2)
   , subseq(p, 2, length.p)
   , ""
   , ""
   )
 else if currentmod = ""then next(acc, currentmod, funcs, types)
 else if length.p > 2 ∧ first.p ∈ "*"then
  let toadd = 
   " /p"
   + if p_2 = "usegraph"_1 then
    let l = findindex("include"_1, p)
    let k = findindex("exclude"_1, p)
    let include = subseq(p, l + 1, k)
    let exclude = subseq(p, k + 1, length.p)
    drawgraph(toseq.arcs.usegraph, asset.include, asset.exclude)
   else subseq(p, 2, length.p)
  next(acc, currentmod, funcs + toadd, types)
 else if first.p ∈ "Function Export"then
  let z = getheader.p
  let toadd = 
   " /p  /keyword"
   + if subseq(p, length.z, length.z + 1) = "{*"then
    z >> 1 + "{" + subseq(p, length.z + 2, findindex("}"_1, p))
   else if last.z ∈ "stub"then z >> 1 else z
  next(acc, currentmod, funcs + toadd, types)
 else if first.p ∈ "type"then next(acc, currentmod, funcs, types + p_2)
 else next(acc, currentmod, funcs, types)
/for(acc
+ if not.isempty.types ∨ not.isempty.funcs then" /br defines types: " + types + funcs
else""/if)

module wordgraph

use standard

use graph.word

use set.word

use svg2graph.word

use seq.arc.word

function nodeTitle(word)seq.word""

function node2text(a:word)seq.word[a]

function generatenode(a:set.word)word toword.cardinality.a

Export drawgraph(arcs:seq.arc.word, set.word, set.word)seq.word 