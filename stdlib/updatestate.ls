Module updatestate

use set.cmdpara

use file

use seq.file

use seq.arc.filename

use graph.filename

use seq.filename

use set.filename

use standard

use textio

use otherseq.word

use words

Function prettystate(input:seq.file,o:seq.word)seq.file
for acc = "", a ∈ breakparagraph.data.first.input do
 if subseq(a,1,1) /in ["-","comment"] then
    acc +"/p comment"+ a << 1
 else if subseq(a,1,1) /in [":","define"]   then 
   for txt="",w /in a do
     if w /in "define:"  /and not.isempty.txt then txt+"/br define" else txt+w 
   /for(acc + " /p define" + txt << 1)
   else 
 for txt = "", have = "",lastbreak=0, p ∈ a do
  if p ∈ "+=" then
   next(if p ∈ "+"then txt + " /br+"else txt >> 1 + " /br" + last.txt + p
   , have,0
   )
  else 
   let addbreak=lastbreak > 10 /and  last.txt /in "."
   next( if addbreak   then txt+"/br"+space+p else txt + p
      , if p ∈ "+="then have + p else have
   ,if addbreak  then 0 else lastbreak+1)
 /for(acc + " /p" + txt)
/for([file(o, acc)])

type defines is name:word,lib:word,cmds:seq.word

function cmd(a:defines) word first.cmds.a

function ?(a:defines,b:defines) ordering name.a ? name.b

use set.defines


Function updatestate(input:seq.file, o:seq.word)seq.file
let allfile = for acc = empty:seq.seq.word, f ∈ input do acc + breakparagraph.data.f /for(acc)
for acc = empty:seq.arc.filename, defs2 = empty:set.cmdpara,
defines=empty:set.defines, aa ∈ allfile do
 if first.aa ∈ "comment"then next(acc, defs2, defines)
  else if first.aa ∈ "define" then
     next(acc,defs2
     ,for newcmds=defines,cmd="",   w /in aa << 1 +"define" do
          if w /in "define"  then  {defines x lib}
              if length.cmd=2 then
                next(newcmds+defines(cmd_1,cmd_2,[cmd_1]),"")
                else next(newcmds+defines(cmd_1,cmd_2,cmd << 2),"")
         else next(newcmds,cmd+w )
     /for( 
     newcmds)
     )
 else
  let cmd0 = first.aa
      let bb=    lookup(defines,defines(cmd0,cmd0,""))
        assert not.isempty.bb report"command \em" +  aa + "is not defined"
   let cmd = cmd.bb_1
   let cmdlib = [lib.bb_1]+ ".lib"
   let idx = findindex("="_1, aa + "?=")
  let rest = if idx > length.aa then""else aa << (idx - 2)
  let filenames = 
   getfilenames("+$build"+ subseq(aa, 2, 4) + cmdlib + subseq(aa, 5, length.aa - length.rest + 3))
  let tail = first.filenames
  next(for arcs = acc, fn ∈ filenames << 1 do arcs + arc(tail, fn)/for(if cmd ∈ "makelib"then
   arcs + arc(changeext(tail, "libsrc"), tail)
   + arc(changeext(tail, "libinfo"), tail)
  else arcs /if)
  , defs2 + cmdpara(tail, filenames << 1, rest, cmd)
  , defines
  )
/for({let g=newgraph.acc HTMLformat.drawgraph(toseq.arcs(subgraph(g, nodes.g \ asset.sinks.g)), empty:set.word, empty 
:set.word)}
let g = newgraph.acc
let sinks = sinks.g
let scriptstart = 
 for acc2 = "set $([space])-e", n ∈ sinks do
   if name.n /in "shell" then acc2 else acc2 + " /br checksrc" + fullname.n
 /for(acc2)
let out = createorder(subgraph(g, nodes.g \ asset.sinks), defs2, scriptstart)
[file(filename.o, out)])

function createorder(g:graph.filename, defs:set.cmdpara, out:seq.word)seq.word
let sinks = sinks.g
if isempty.sinks then
 assert isempty.nodes.g report"cycle in graph"
 out
else
 for txt = out, p ∈ if isempty.sinks then toseq.nodes.g else sinks do txt + tosetvars(defs, p)/for(createorder(subgraph(g, nodes.g \ asset.sinks), defs, txt + " /br #________________"))

function ?(a:filename, b:filename)ordering
alphaword.name.a ? alphaword.name.b ∧ alphaword.ext.a ? alphaword.ext.b
∧ toalphaseq.dirpath.a ? toalphaseq.dirpath.b

function print(filenames:seq.filename)seq.word
for f2 = "", n ∈ filenames do f2 + fullname.n /for(f2)

function tosetvars(defs2:set.cmdpara, fn:filename)seq.word
let node = fullname.fn
let cmdpara = lookup(defs2, cmdpara(fn, empty:seq.filename, empty:seq.word, first."noop"))
if isempty.cmdpara then""
else
 let parts = print.parts.cmdpara_1
 let lib = [name.first.parts.cmdpara_1]
 let cmd = cmd.cmdpara_1
 if lib = "shell" then
  "/br"+   cmd+ parts << 1 +">"+node
 else if cmd ∈ "makelib"then
  let B = extractValue(data.cmdpara_1, "uses")
  for depends = ""
  , libinfo = ""
  , ccode = "void init_libs(){"
  , u ∈ reverse.B
  do
   next(depends + fullname.filename("+$build $([u]).$libtype")
   ,if isempty.libinfo then  [u]+".libinfo" else libinfo+u
   , "void init_$([u])(); $(ccode)init_$([u])();"
   )
   /for(let out = changeext(fn,"libsrc")
  " /p parts3=$(dq(parts << 1))
 /br dependsOn=$(dq("$parts3" + first.parts))
 /br libsrcargs=$(dq."$(lib)libsrc $parts3 $(data.cmdpara_1)o=$(("+"+dirpath.out+name.out+".libsrc"))")
 /br compileargs=$(dq(lib + "makebitcode+$build" + name.out+"."+ext.out + libinfo))
 /br dependlibs=$(dq.depends)
 /br ccode=$(dq.ccode)
 /br makelibrary $([name.fn])")
 else 
  " /p node=$(dq.[node])
 /br parts3=$(dq(parts << 1))
 /br dependsOn=$(dq("$parts3" + first.parts))
 /br libexeAll $(lib + cmd)$parts3 $(data.cmdpara_1 + "o=$(("+"+dirpath.fn+[name.fn, "."_1, ext.fn]))")"

type cmdpara is fn:filename, parts:seq.filename, data:seq.word, cmd:word

function ?(a:cmdpara, b:cmdpara)ordering fn.a ? fn.b 