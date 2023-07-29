Module doc

use bits

use seq.byte

use file

use functionHeader

use newPretty

use standard

use textio

use seq.arc.word

use set.arc.word

use graph.word

use set.word

use wordgraph

Function usegraph(
 input:seq.file
 , o:seq.word
 , include:seq.word
 , exclude:seq.word
) seq.file
{ENTRYPOINT /strong usegraph creates a graph with each node being a module and the arcs to the module referenced in the /keyword use clauses. /br options:/strong exclude lists the modules to ignore in the use clauses. 
 /br /strong include restricts the modules considered to those listed.
 /p Examples:<* block
 /br > usegraph /sp+built core.libsrc /< a href ="./install1.html" > Result /< /a>
 /br > usegraph /sp+built core.libsrc exclude = seq standard /< a href ="./install2.html" > Result /< /a>
 /br > usegraph /sp+built core.libsrc include = UTF8 words standard textio exclude = seq standard /< a href ="./install3.html" > Result /< /a>
 /br > usegraph /sp+core UTF8.ls textio words standard encoding xxhash exclude = seq standard *>
 /p The last two examples give the same result. The first excludes modules from consideration and the second only includes source files of modules that should be included. }
let out = drawgraph(usegraph(breakparagraph.input, 1_"mod"), asset.include, asset.exclude),
[file(filename.o, out)]

Function doclibrary(input:seq.file, o:seq.word, mods:seq.word) seq.file
{OPTION PROFILE ENTRYPOINT /strong doclibrary create summary documentation for library source code. /br The option /strong mods list the modules to be document if the option is not empty. 
 /p This document was created using
 /br doclibrary+subtools frontcmd.ls doc.ls}
let libsrc =
 for acc = empty:seq.byte, f ∈ input
 do if ext.fn.f ∈ "ls libsrc" then acc + tobyte.10 + tobyte.10 + data.f else acc,
 breakparagraph.acc
let todoc =
 if isempty.mods then
  for acc = "", s ∈ libsrc
  do if subseq(s, 1, 1) ∈ ["module", "Module"] then acc + subseq(s, 2, 2) else acc,
  acc
 else mods
let g = newgraph.usegraph(libsrc, 1_"mod")
let modindex =
 for txt = "", modname ∈ todoc
 do txt + "/< a href = /ldq" + merge.[1_"#", modname] + dq + ">^(modname) /< /a>",
 txt
,
[file(filename.o, modindex + docmodule(g, todoc, libsrc))]

Function usegraph(lib:seq.seq.word, kind:word) seq.arc.word
for currentmod = 1_"?", result = empty:seq.arc.word, p ∈ lib
do
 if isempty.p then
 next(currentmod, result)
 else if 1_p ∈ "module Module" then
 next(2_p, result)
 else if 1_p ∈ "use" then
  let m = if n.p = 2 then 2_p else if kind = 1_"mod" then 2_p else merge(p << 1),
  next(
   currentmod
   , if currentmod = m ∨ currentmod ∈ "?" then result else result + arc(currentmod, m)
  )
 else next(currentmod, result)
,
result

function docmodule(usegraph:graph.word, todoc:seq.word, lib:seq.seq.word) seq.word
for acc = "", currentmod = "?", funcs = "", types = "", p ∈ lib
do
 if isempty.p then
 next(acc, currentmod, funcs, types)
 else if 1_p ∈ "module Module" then
  let modname = 2_p,
   if modname ∉ todoc then
   next(acc, subseq(p, 2, n.p), funcs, types)
   else
    let leftover = if n.types > 0 ∨ n.funcs > 0 then "/br defines types: ^(types)^(funcs)" else ""
    let name = [modname] + if n.p > 2 then ".T" else ""
    let usedin = toseq.arcstopredecessors(usegraph, merge.name),
    next(
     acc
     + leftover
     + "/< hr id = /ldq^(modname)^(dq) >"
     + "<* section /keyword module^(name) *>"
     + 
      if isempty.usedin then
      ""
      else "/br Module^(name) is used in modules: ^(for acc2 = "", @e ∈ usedin do acc2 + tail.@e, alphasort.acc2)"
     , subseq(p, 2, n.p)
     , ""
     , ""
    )
 else if currentmod = "" ∨ 1_currentmod ∉ todoc then
 next(acc, currentmod, funcs, types)
 else if 1_p ∈ "Export" then
 next(acc, currentmod, funcs + "/p" + pretty.p, types)
 else if 1_p ∈ "Function" then
  let t5 = extractHeader(headerTable, p)
  let doc =
   if subseq(p, n.t5 + 1, n.t5 + 1) = "{" then
    let t6 = p << (n.t5 + 1)
    let t7 = subseq(t6, 1, findindex(t6, 1_"}") - 1)
    for i = 0, w ∈ t7 while w ∈ "ENTRYPOINT" do i + 1,
    t7 << i
   else ""
  ,
  next(acc, currentmod, funcs + "/p" + pretty(t5 + "stub") >> 1 + doc, types)
 else if 1_p ∈ "type" then
 next(acc, currentmod, funcs, types + 2_p)
 else next(acc, currentmod, funcs, types)
,
acc
 + 
 if not.isempty.types ∨ not.isempty.funcs then
 "/br defines types: ^(types)^(funcs)"
 else "" 