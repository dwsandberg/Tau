Module doc

use file

use seq.file

use format

use pretty

use standard

use textio

use seq.arc.word

use set.arc.word

use graph.word

use otherseq.seq.word

use set.word

use wordgraph

Export drawgraph(seq.arc.word, set.word, set.word)seq.word

Export extractValue(seq.word, seq.word)seq.word

function prettyfile3(escape:boolean, modhead:seq.word, text:seq.seq.word)seq.word
for uses = empty:seq.seq.word
, libbody = empty:seq.seq.word
, result = ""
, modules = ""
, s ∈ text + "Module ?"
do
 if length.s = 0 then next(uses, libbody, result, modules)
 else if s_1 ∈ "use"then next(uses + s, libbody, result, modules)
 else if s_1 ∈ "Export unbound"then next(uses, libbody + (" /keyword" + s), result, modules)
 else if s_1 ∈ "Function function type"then next(uses, libbody + pretty.s, result, modules)
 else if s_1 ∈ "module Module"then
  let target = 
   if length.modhead > 1 then subseq(modhead, 1, 6) + s_2 + subseq(modhead, 8, length.modhead)
   else" /keyword"
  let newresult = 
   result + " /p"
   + %(" /p", sortuse(uses, " /keyword") + libbody) >> 1
   + if s_2 ∈ "?"then""else" /p" + target + s
  next(empty:seq.seq.word, empty:seq.seq.word, newresult, modules + s_2)
 else
  let temp = if escape then escapeformat.s else s
  if length.uses = 0 then next(uses, libbody, result + (" /p" + temp), modules)
  else next(uses, libbody + (" /p" + temp), result, modules)
/for(if isempty.modhead then result
else
 let libname = extractValue(first.text, "Library")
 " /< noformat <h1> Source code for Library" + libname + "</h1>  />"
 + for acc = "", modname ∈ modules >> 1 do
  acc + " /< noformat <a href=" + dq.[merge.["#"_1, modname]] + ">"
  + modname
  + "</a>  />"
 /for(acc + result)/if)

Function formatdoc(input:seq.file, o:seq.word)seq.file
[file(filename.o, prettyfile3(false, "", breakparagraph.data.first.input))]

Function htmlcode(input:seq.file, o:seq.word)seq.file
let libsrc = breakparagraph.data.first.input
[file(filename.o
, prettyfile3(true, " /< noformat <hr id=" + dq."T" + ">  />  /keyword", libsrc)
)
]

Function doclibrary(input:seq.file, o:seq.word)seq.file
{OPTION PROFILE}
let libsrc = breakparagraph.data.first.input
{create summary documentation for libraray. }
let exports = extractValue(first.libsrc, "exports")
let todoc = 
 for acc = "", s ∈ libsrc do
  if subseq(s, 1, 3) = "* only document"then acc + subseq(s, 4, length.s)else acc
 /for(if isempty.acc then exports else acc /if)
let g = newgraph.usegraph(libsrc, "mod"_1)
[file(filename.o, modindex.todoc + docmodule(g, exports, todoc, libsrc))]

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

/Function uncalledfunctions(prg:seq.symdef)seq.word{List of functions may include indirectly called functions. }let g=newgraph 
.formcallarcs.prg let sources=for acc=empty:seq.symbol, @e ∈ toseq.nodes.g do acc+sources(g, empty:set.symbol, @e 
)/for(acc)for acc="", @e ∈ sources do acc+print.@e+"
 /br"/for(acc)

* usegraph exclude standard seq set UTF8 stack graph otherseq

Function usegraph(input:seq.file, o:seq.word, include:seq.word, exclude:seq.word)seq.file
let out = drawgraph(usegraph(breakparagraph.input, "mod"_1), asset.include, asset.exclude)
[file(filename.o, out)]

Function usegraph(lib:seq.seq.word, kind:word)seq.arc.word
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