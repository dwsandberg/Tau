Module entrypoint

use UTF8

use file

use seq.file

use seq.filename

use functionHeader

use pretty

use format1a

use standard

use seq1.word

use seq1.seq.word

use seq.seq.word

use set.seq.word

use set.word

use token

use seq.byte

use bits

Function entrypoint(input:seq.file, entryUses:seq.word, core:boolean) seq.byte
{COMMAND /strong entrypoint For seeing the Module the compiler generates to define the entry point. 
/br Options:
/br /strong entryUses addition use clause added to module when building entry point. 
/br /strong core Only show core of Module. }
let discard=tknencoding
for acc = "", p ∈ modEntry(breakparagraph.input, entryUses, core)
do acc + if p sub 1 ∈ "Function function" then removeMarkup.pretty.p + "/p" else p + "/p",
let words=if core then
 for names = "", f ∈ input do names + name.fn.f + "." + ext.fn.f,
 "<<<< Code Below was generated with command entrypoint:(names) entryUses::(entryUses) core: >>>>
 /p:(acc)"
else acc
toseqbyte.textFormat1a.words



Function modEntry(src:seq.seq.word, entryUses:seq.word, core:boolean) seq.seq.word
{The format of entryUses is flexible}
for acc0 = empty:seq.seq.word, state = 0, w ∈ entryUses
do
 if w
 ∈ "use,
 /p" then next(acc0, state)
 else if w ∈ "." then next(acc0, 1)
 else if state = 0 then next(acc0 + ("use" + w), 0)
 else next(acc0 >> 1 + (acc0 sub n.acc0 + ".:(w)"), 0)
for acc = "", uses = asset.acc0, info = "", e ∈ getHeaders(src, true)
do
 let p = header.e
 let abstract = p sub 3 ∈ ":"
 let cmd = if abstract then [p sub 2] + ":callconfig" else [p sub 2],
 let t = buildruncmd2(e, cmd),
 next(
  acc + "else if cmd ∈:(dq.subseq(cmd, 1, 1)) then:(t sub 1)"
  , if abstract then uses else uses + ("use" + (modname.e) sub 1)
  , info + dq.t sub 2 + ","
 )
let common =
 toseq.uses
  + [
  "function cmdDesc seq.seq.word:(if isempty.info then "empty:seq.seq.word" else "[:(info >> 1)]")"
  , "function runthecmd (cmdline:seq.word, files:seq.seq.file) seq.file let cmd = (cmdline sub 1):(acc << 1):(if isempty.uses then "" else "else") empty:seq.file"
 ],
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
  , "use textio"
  , "use process.UTF8"
 ]
  + [
  "Export addbcwords (seq.byte) int"
  , "Function entrypoint (args:UTF8) UTF8 let p = process.entrypoint2 (args), if aborted.p then finishentry.[file (:(dq."error.html"), message.p)] else result.p"
  , "function entrypoint2 (args0:UTF8) UTF8 let args = towords.args0,:(partA), assert not.isempty.cmdline report:(dq."No command named")+cmd let files = getfiles.b let errors = errors.files assert isempty.errors report:(dq."Error fetching input files
  /br")+errors finishentry.runthecmd (cmdline, files)"
 ]
  + common
else common

function partA seq.word
"let cmdline0 = args let cmd = cmdline0 sub 1 for cmdline =:(dq.""), b = empty:seq.seq.filename, e ∈ cmdDesc while isempty.cmdline do if cmd = e sub 1 then let cl = if n.e = 1 then cmdline0 else [cmd]+addDefaultName (cmdline0, e sub 2) for fs = empty:seq.seq.filename, p ∈ e << 2 do fs+tofilenames.extractValue (cl, [p]), next (cl+:(dq."output: default.html"), fs) else next (cmdline, b)"

function buildruncmd2(e:headerType, cmd:seq.word) seq.seq.word
let p = header.e
let k = min(findindex(p, "(" sub 1), findindex(p, "{}" sub 1))
let firstpara = if p sub k ∈ "(" then [p sub (k + 1)] else ""
for
 zzz = ""
 , txt2 = ""
 , fileparam = empty:seq.seq.word
 , name = ""
 , last = "?" sub 1
 , continue = true
 , w ∈ header.e
while continue
do
 if w ∈ ":" then next(zzz, txt2, fileparam, [last], w, true)
 else if w ∈ ",)" then
  if last ∈ "word" then
   next(
    zzz
    , txt2 + ", extractValue (cmdline,:(dq(if name = "output" then "output o" else name)))"
    , fileparam
    , ""
    , w
    , true
   )
  else if last ∈ "boolean" then next(zzz, txt2 + ", extractFlag (cmdline,:(dq.name))", fileparam, "", w, true)
  else if last ∈ "file" then
   let new = fileparam + "tofilenames.extractValue (cmdline,:(dq.name))",
   next(zzz + name, txt2 + ", files sub:(n.new)", new, "", w, true)
  else next(zzz, txt2 + ", ?", fileparam, "", w, true)
 else if w = "{}" sub 1 then next(zzz, txt2, fileparam, name, w, false)
 else next(zzz, txt2, fileparam, name, w, true)
let CommandArgs = if isempty.txt2 then "" else "(:(txt2 << 1))"
let cmdReturnType = returnType.e,
[
 if cmdReturnType = "seq.file" then cmd + CommandArgs
 else "[file (extractValue (cmdline,:(dq."output o")),:(cmd + CommandArgs))]"
 , [cmd sub 1] + firstpara + zzz
] 
