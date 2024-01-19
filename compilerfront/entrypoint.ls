Module entrypoint

use UTF8

use file

use seq.file

use seq.filename

use functionHeader

use pretty

use standard

use otherseq.word

use otherseq.seq.word

use seq.seq.word

use set.seq.word

use set.word

Function entrypoint(input:seq.file, entryUses:seq.word, core:boolean) seq.word
{COMMAND /strong entrypoint For seeing the Module the compiler generates to define the entry point. 
/br Options:
/br /strong entryUses addition use clause added to module when building entry point. 
/br /strong core Only show core of Module. }
for acc = "", p ∈ modEntry(breakparagraph.input, entryUses, core)
do acc + if 1#p ∈ "Function function" then pretty.p + "/p" else p + "/p",
if core then
 for names = "", f ∈ input do names + name.fn.f + "." + ext.fn.f,
 "<<<< Code Below was generated with command entrypoint^(names) entryUses:^(entryUses) core: >>>>
 /p^(acc)"
else acc

Function modEntry(src:seq.seq.word, entryUses:seq.word, core:boolean) seq.seq.word
{The format of entryUses is flexible}
for acc0 = empty:seq.seq.word, state = 0, w ∈ entryUses
do
 if w
 ∈ "use,
 /p" then next(acc0, state)
 else if w ∈ "." then next(acc0, 1)
 else if state = 0 then next(acc0 + ("use" + w), 0)
 else next(acc0 >> 1 + (1^acc0 + ".^(w)"), 0)
for acc = "", uses = asset.acc0, info = "", e ∈ getHeaders(src, true)
do
 let p = header.e
 let abstract = 3#p ∈ ":"
 let cmd = if abstract then [2#p] + ":callconfig" else [2#p],
 let t = buildruncmd2(e, cmd),
 next(
  acc + "else if cmd /in^(dq.subseq(cmd, 1, 1)) then^(1#t)"
  , if abstract then uses else uses + ("use" + 1#modname.e)
  , info + dq.2#t + ","
 )
let common =
 toseq.uses
  + [
  "function cmdDesc seq.seq.word^(if isempty.info then "empty:seq.seq.word" else "[^(info >> 1)]")"
  , "function runthecmd (cmdline:seq.word, files:seq.seq.file) seq.file let cmd = 1#cmdline^(acc << 1)^(if isempty.uses then "" else "else") empty:seq.file"
 ]
let tt = pretty.2^common
assert 1#"Fail" ∉ tt ∧ 1#"Failed" ∉ tt report pretty.2^common,
if not.core then
 [
  "use standard"
  , "use file"
  , "use llvmcode"
  , "use seq.file"
  , "use seq.seq.file"
  , "use seq.seq.filename"
  , "use bits"
  , "use seq.byte"
  , "use process.UTF8"
 ]
  + [
  "Export addbcwords (seq.byte) int"
  , "Function entrypoint (args:UTF8) UTF8 let p = process.entrypoint2 (args), if aborted.p then finishentry.[file (^(dq."error.html"), message.p)] else result.p"
  , "function entrypoint2 (args0:UTF8) UTF8 let args = towords.args0,^(partA), assert not.isempty.cmdline report^(dq."No command named")+cmd let files = getfiles.b let errors = errors.files assert isempty.errors report^(dq."Error fetching input files
  /br")+errors finishentry.runthecmd (cmdline, files)"
 ]
  + common
else common

function partA seq.word
"let cmdline0 = args let cmd = 1#cmdline0 for cmdline =^(dq.""), b = empty:seq.seq.filename, e ∈ cmdDesc while isempty.cmdline do if cmd = 1#e then let cl = if n.e = 1 then cmdline0 else [cmd]+addDefaultName (cmdline0, 2#e) for fs = empty:seq.seq.filename, p ∈ e << 2 do fs+tofilenames.extractValue (cl, [p]), next (cl+^(dq."output: default.html"), fs) else next (cmdline, b)"

function buildruncmd2(e:headerType, cmd:seq.word) seq.seq.word
let p = header.e
let k = min(findindex(p, 1#"("), findindex(p, 1#"{}"))
let firstpara = if k#p ∈ "(" then [(k + 1)#p] else ""
for
 zzz = ""
 , txt2 = ""
 , fileparam = empty:seq.seq.word
 , name = ""
 , last = 1#"?"
 , continue = true
 , w ∈ header.e
while continue
do
 if w ∈ ":" then next(zzz, txt2, fileparam, [last], w, true)
 else if w ∈ ",)" then
  if last ∈ "word" then
   next(
    zzz
    , txt2 + ", extractValue (cmdline,^(dq(if name = "output" then "output o" else name)))"
    , fileparam
    , ""
    , w
    , true
   )
  else if last ∈ "boolean" then next(zzz, txt2 + ", extractFlag (cmdline,^(dq.name))", fileparam, "", w, true)
  else if last ∈ "file" then
   let new = fileparam + "tofilenames.extractValue (cmdline,^(dq.name))",
   next(zzz + name, txt2 + ",^(n.new)#files", new, "", w, true)
  else next(zzz, txt2 + ", ?", fileparam, "", w, true)
 else if w = 1#"{}" then next(zzz, txt2, fileparam, name, w, false)
 else next(zzz, txt2, fileparam, name, w, true)
let CommandArgs = if isempty.txt2 then "" else "(^(txt2 << 1))"
let cmdReturnType = returnType.e,
[
 if cmdReturnType = "seq.file" then cmd + CommandArgs
 else "[file (extractValue (cmdline,^(dq."output o")),^(cmd + CommandArgs))]"
 , [1#cmd] + firstpara + zzz
] 