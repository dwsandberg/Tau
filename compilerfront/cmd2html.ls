Module cmd2html

use file

use seq.file

use standard

use otherseq.word

use otherseq.seq.word

use seq.seq.word

use set.seq.word

use set.word

use UTF8

use functionHeader

type paradesc is name:word, code:seq.word, text:seq.word

use seq.paradesc

Function cmd2html(input:seq.file, libname:seq.word, o:seq.word) seq.file
{COMMAND}
let outfn = filename.o
let outname = 1#libname
assert not.isempty.libname ∧ name.outfn ≠ 1#libname
report "libname cannot be empty or the same as o name"
let allsrc = breakparagraph.input
assert not.isempty.allsrc report "empty input"
for uses = empty:set.seq.word, code = "", txt = "", idx = 1, e ∈ getHeaders(allsrc, true)
do
 let cmdname = 2#header.e
 let cmddescfull = cmddesc.e
 let ii = findindex(cmddescfull << 2, 1#"/br") + 1
 let cmddesc = subseq(cmddescfull, 4, ii)
 for
  params = empty:seq.paradesc
  , idxp = idx + 1
  , cmd = ""
  , nest = 0
  , w ∈ cmddescfull << ii + "/br"
 do
  let end = w ∈ "/br <* *>" ∧ not.isempty.cmd
  let newparams =
   if end ∧ n.cmd > 1 then
    let kind = 1#cmd
    let argname = (2 - nest)#cmd
    let argdesc = cmd << (2 - nest),
     if kind ∈ "flag" then
      params
       + paradesc(
       argname
       , ", getElementValue.^(id.idxp) =^(dq."true")"
       , "/br /tag <label><input /sp type = /tag^(dq."checkbox") id =^(id.idxp) />^(argname)"
        + "/tag </label>^(argdesc)"
      )
     else if nest = 1 then
      let first = not.isempty.code.1^params
      let name = id.idxp,
       params
        + paradesc(
        argname
        , ""
        , "/tag <br><label><input /sp type = radio id =^(name) name =^(name) value =^(argname)
        ^(if first then "checked" else "")"
         + ">^(argdesc)"
          + "/tag </label>"
       )
     else
      let value = if argname ∈ "o" then "value = /tag^(dq(%.cmdname + ".html"))" else "",
       params
        + paradesc(
        argname
        , ", getElementValue.^(id.idxp)"
        , if w ∈ "<*" then
         "/br^(argdesc)"
         else "
         /br /tag <label>^(argname) /tag <input /sp id =^(id.idxp)^(value) /> /tag </label>
         ^(argdesc)"
       )
   else params
  let newidxp = if end ∧ nest = 0 then idxp + 1 else idxp,
   if w ∈ "/br" then
   next(newparams, newidxp, "", nest)
   else if w ∈ "<*" then
   next(newparams, newidxp, if end then "" else cmd, nest + 1)
   else if w ∈ "*>" then
   next(newparams, newidxp, if end then "" else cmd, nest - 1)
   else next(newparams, newidxp, cmd + w, nest)
 let callname = if 3#header.e ∈ ":" then [cmdname] + ":callconfig" else [cmdname]
 for codepara = "", last = 1#"x", continue = true, w ∈ header.e
 while continue
 do
  if w ∈ ":" then
   for code2 = codepara, p ∈ params do if last = name.p then code2 + code.p else code2,
   next(code2, w, true)
  else if w = 1#"{}" then
  next(codepara, w, false)
  else next(codepara, w, true)
 for txt2 = "", e2 ∈ params do txt2 + text.e2
 let callcmd = "^(callname) (input^(codepara))"
 let callcmd1 =
  if returnType.e = "seq.word" then
  "[file (^(dq(%.cmdname + ".html")),^(callcmd))]"
  else callcmd,
 next(
  uses + if n.modname.e > 1 then [1#modname.e] + ".callconfig" else modname.e
  , code + "if cmdno =^(idx).0 then^(callcmd1) /br else"
  , txt
   + "
   /p /tag <button /sp onclick = /tag^(dq."runcmd1 (^(idx))") >^(cmdname) /tag </button>
   ^(cmddesc) <* block^(txt2) *>"
  , idxp
 )
assert not.isempty.txt report "No commands found in input"
let html = "/tag <p /sp id = pageready> loading /tag <p><input /sp id = input value =
^(dq."+built core.libsrc") >^(txt)"
let ls =
 other.outname
  + "/p use"
  + %("/p use", toseq.uses) >> 2
  + "
 /p Function runcmd2 (p2:JS.HTTPstate.real) int
 /br let s = fromJS.p2,
 /br let cmdno = args.s, let input = files.s
 /br let discard = setElementValue (^(dq."pageready"),
 ^(dq("ready^" + "(print (3, cmdno))"))"
  + ")
 /br let files =^(code) empty:seq.file
 /br if isempty.files then
 /br setElementValue (^(dq) pageready^(dq),^(dq) no output^(dq))
 /br else
 /br let t = writefiles (files, 0.0,
 ^(dq) runcmd3^(dq)), 0",
[
 file("+built^(outname).html", html)
 , file("+built^(outname).ls", ls)
 , file(outfn, "cmd2html created files: ^(outname).html^(outname).ls")
]

function id(i:int) seq.word "/tag^(dq.[merge.[1#"I", toword.i]])"

Export +(seq.int, seq.int) seq.int

function other(outname:word) seq.word
let sp = encodeword.[char.32],
"Module^(outname)
/p use webHTTP.real
/p use webIO
/p use bits
/p use seq.byte
/p use file
/p use standard
/p use seq.file
/p use JS.real
/p use JS.HTTPstate.real
/p use real
/p use UTF8
/p use otherseq.filename
/p use webtools2
/p Function runcmd1 (i:real) int
/br let filenames = tofilenames (getElementValue.^(dq) input^(dq)),
/br for acc = empty:seq.file, fn ∈ filenames do
/br acc+file (fn, empty:seq.byte)
/br, let discard = setElementValue (
^(dq) pageready^(dq),^(dq) readyz^"
 + "(%n.filenames)^(dq))
/br let z = readfiles (acc, i,^(dq) runcmd2^(dq)), 0
/p Function runcmd3 (p2:JS.HTTPstate.real) int
/br for links =
^(dq)^(dq), f /in files.fromJS.p2 do
/br let name = fullname.fn.f
/br links+^(dq)^(merge("/tag" + sp + "<a" + sp + "/sp")) href =^"
 + "(merge (^(dq)../^(dq)+name)) >^"
 + "(name)^(merge("/tag" + sp + "</a>"))^(dq)
/br setElementValue (^(dq) pageready
^(dq),^(dq) results: ^"
 + "(links)^(dq))
/p Function^(outname) int setElementValue (^(dq) pageready^(dq),^(dq) ready
^(dq))"

------------------

Function entrypoint(input:seq.file, entryUses:seq.word) seq.word
{COMMAND /strong entrypoint For seeing the package the compiler generates to define the entry point
. 
/br Options:
/br /strong entryUses addition use clause added to module when building entry point. }
for acc = "", p ∈ modEntry(breakparagraph.input, entryUses)
do acc + if 1#p ∈ "Function function" then pretty.p + "/p" else p + "/p",
acc

use newPretty

Function modEntry(src:seq.seq.word, entryUses:seq.word) seq.seq.word
{The format of entryUses is flexible}
for acc0 = empty:seq.seq.word, state = 0, w ∈ entryUses
do
 if w ∈ "use, /p" then
 next(acc0, state)
 else if w ∈ "." then
 next(acc0, 1)
 else if state = 0 then
 next(acc0 + ("use" + w), 0)
 else next(acc0 >> 1 + (1^acc0 + ".^(w)"), 0)
for acc = "", uses = asset.acc0, e ∈ getHeaders(src, true)
do
 let p = header.e
 let abstract = 3#p ∈ ":"
 let cmd = if abstract then [2#p] + ":callconfig" else [2#p],
 next(
  acc + "else if cmd /in^(dq.cmd) then^(buildruncmd(e, cmd))"
  , if abstract then uses else uses + ("use" + 1#modname.e)
 ),
[
 "use standard"
 , "use file"
 , "use llvmcode"
 , "use seq.file"
 , "use seq.seq.file"
 , "use bits"
 , "use seq.byte"
 , "use process.UTF8"
]
 + toseq.uses
 + [
 "Export addbcwords (seq.byte) int"
 , "Function entrypoint (args:UTF8) UTF8 let p = process.entrypoint2 (args), if aborted.p
 then finishentry.[file (^(dq."error.html"), message.p)] else result.p"
 , "function entrypoint2 (args0:UTF8) UTF8 let args = towords.args0, let cmd = 1#args,
 finishentry.^(acc << 1)^(if isempty.uses then "" else "else") assert false report
 ^(dq."No command named")+cmd empty:seq.file"
]

function buildruncmd(e:headerType, cmd:seq.word) seq.word
let p = header.e
let k = min(findindex(p, 1#"("), findindex(p, 1#"{}"))
let firstpara = if k#p ∈ "(" then [(k + 1)#p] else ""
for
 txt2 = ""
 , fileparam = empty:seq.seq.word
 , name = ""
 , last = 1#"?"
 , continue = true
 , w ∈ header.e
while continue
do
 if w ∈ ":" then
 next(txt2, fileparam, [last], w, true)
 else if w ∈ ",)" then
  if last ∈ "word" then
  next(txt2 + ", extractValue (param,^(dq.name))", fileparam, "", w, true)
  else if last ∈ "boolean" then
  next(txt2 + ", extractFlag (param,^(dq.name))", fileparam, "", w, true)
  else if last ∈ "file" then
   let new = fileparam + "tofilenames.extractValue (param,^(dq.name))",
   next(txt2 + ",^(n.new)#files", new, "", w, true)
  else next(txt2 + ", ?", fileparam, "", w, true)
 else if w = 1#"{}" then
 next(txt2, fileparam, name, w, false)
 else next(txt2, fileparam, name, w, true)
let CommandArgs = if isempty.txt2 then "" else "(^(txt2 << 1))"
let cmdReturnType = returnType.e,
(if isempty.txt2 then "" else "let param = addDefaultName (args, 1#^(dq.firstpara))")
 + (
 if isempty.fileparam then
 ""
 else "let files = getfiles.[^(%(",", fileparam) >> 1)]"
)
 + 
 if cmdReturnType = "seq.file" then
 cmd + CommandArgs
 else "[file (extractValue (args,^(dq."o")),^(cmd + CommandArgs))]"
 