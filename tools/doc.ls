Module doc

use standard

use textio

use file

use seq.file

use newPretty

use functionHeader

Function docsource(input:seq.file, cmd:boolean, o:seq.word) seq.file
{COMMAND /strong docsource create summary documentation for source code
/br The option /strong cmd extracts just the command documentation}
let acc = getHeaders(breakparagraph.input, cmd),
if cmd then
 let esc = if 1^o ∈ "html" then "" else [escapeformat]
 for acc3 = "", e ∈ acc
 do
  let j = findindex(header.e, 1#"COMMAND"),
   acc3
    + "^(esc) /tag <h3> /sp Command /strong^(2#header.e) /sp /tag </h3>^(esc) /p^(esc)"
    + subseq(header.e, j + 1, n.header.e - 1)
    + "^(esc) /p",
 [file(o, acc3)]
else
 for acc2 = "", lastmod = "", mods = empty:set.word, e ∈ acc
 do next(
  acc2
   + (if modname.e ≠ lastmod then "/tag <a /sp id = /tag^(1#modname.e) /sp />" else "")
   + 
   if 1#header.e ∈ "type" then
   modname.e + header.e + "/p"
   else
    let i = if 1^header.e ∈ "}" then findindex(header.e, 1#"{") else n.header.e + 1
    let head = subseq(header.e, 1, i - 1)
    let t =
     if 1#header.e ∈ "Export Builtin builtin" then
     pretty.head
     else pretty(head + "stub") >> 1
    let newtxt = if i < n.header.e then t + "/br" + subseq(header.e, i + 1, n.header.e - 1) else t,
    modname.e + newtxt + "/p"
  , modname.e
  , if isempty.modname.e then mods else mods + 1#modname.e
 )
 for modindex = "", name ∈ toseq.mods
 do modindex + "/tag <a /sp href =#^(name) >^(name) /tag </a>",
 [file(o, modindex + acc2)]

use set.word

use UTF8 