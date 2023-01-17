Module main2

use UTF8

use bits

use seq.byte

use compilerfrontT.callconfig

use codegennew

use compilerfront

use file

use seq.file

use process.seq.file

use format

use llvmcode

use objectio.midpoint

use seq.midpoint

use seq.modExports

use standard

use symbol2

use set.symdef

use textio

use seq.seq.word

Function libname(info:midpoint) word extractValue(first.src.info, "Library")_1

function makeentry(libraryuses:seq.word, libname:seq.word, input:seq.byte) seq.word
let aa = 
 for acc = empty:seq.seq.word, modname = "?"_1, p ∈ breakparagraph.input do
  if subseq(p, 1, 1) = "Function" ∧ subseq(p, 3, 8) = "(input:seq.file" then
   let t = "use" + modname,
   next(
    if not.isempty.acc ∧ first.acc = t then acc else [t] + acc /if
    + ["Export $(subseq(p, 2, findindex(p, ")"_1))) seq.file"]
    , modname)
  else if length.p > 1 ∧ p_1 ∈ "Module module" then
   next(acc, p_2)
  else
   next(acc, modname)
 /do acc
,
for txt = "", useclauses = "", p ∈ aa do
 if first.p ∈ "use" then
  next(txt, useclauses + p + "/p")
 else if first.p ∉ "Export" then
  next(txt, useclauses)
 else
  next(
   for para = "", name = ","_1, last = ","_1, type = "", w ∈ p << 9
   while last ∉ ")"
   do
    if w ∈ ",)" then
     next(
      para
      + if type = "seq.word" then
       ", extractValue (args, $(dq.[name]))"
      else if type = "boolean" then
       ", first.$(dq.[name]) ∈ extractValue (args, $(dq."flags"))"
      else
       ", ?"
      , name
      , w
      , "")
    else if last ∈ ":" then
     next(para, name, last, type + w)
    else if last ∈ "," then next(para, w, w, "") else next(para, name, w, type)
   /do txt + "/br else if cmd /in $(dq.subseq(p, 2, 2)) then $(subseq(p, 2, 2)) (input $(para))"
   , useclauses)
/do
 if isempty.txt then
  txt
 else
  "Module $(merge(libname + "$root"))
   /p use file
   /p use seq.file
   /p use standard
   /p $(useclauses) Function $(merge(libname + "$EP"))
   (args:seq.word, input:seq.file) seq.file
   /br let cmd = first.args,
   /br $(txt << 2)
   /br else empty:seq.file"

Function libsrc(input:seq.file, uses:seq.word, exports:seq.word, o:seq.word) seq.file
let outname = filename.o
let Library = [name.outname],
for acc1 = empty:seq.byte, acc2 = empty:seq.byte, f ∈ input do
 if ext.fn.f ∈ "ls" then
  next(acc1 + tobyte.10 + tobyte.10 + data.f, acc2)
 else if ext.fn.f ∈ "libsrc" then
  next(acc1, acc2 + tobyte.10 + tobyte.10 + data.f)
 else
  next(acc1, acc2)
/do
 let firstpart = 
  if isempty.exports then
   "Library = $(Library) uses = $(uses) exports = $(exports)"
  else
   let entrypointname = [merge(Library + "$EP")],
   "Library = $(Library) uses = $(uses) exports = $(exports + entrypointname)
    /p $(makeentry(uses, Library, acc1 + acc2))"
 ,
 [file(outname, toseqbyte.textformat.firstpart + acc1 + acc2)]

function entrypointmodule(Library:seq.word) seq.seq.word
let entrypointname = [merge(Library + "$EP")],
["Module $(entrypointname)"
 , "use standard"
 , "use file"
 , "use $(merge(Library + "$root"))"
 , "use llvmcode"
 , "use seq.file"
 , "use bits"
 , "use seq.byte"
 , "use process.UTF8"
 , "Export addbcwords (seq.byte) int"
 , "Function entrypoint (args:UTF8) UTF8 let p = process.entrypoint2 (args), if aborted.p then finishentry
  .[file ($(dq."error.html"), message.p)] else result.p"
 , "function entrypoint2 (args0:UTF8) UTF8 let args = towords.args0, finishentry.$(entrypointname)
  (args, getfiles.args)"]

function subcompilelib(allsrc:seq.seq.word, dependentlibs:midpoint, outname:filename, options:seq.word) seq.file
{OPTION XPROFILE}
let libname = extractValue(first.allsrc, "Library")
let uses = extractValue(first.allsrc, "uses")
let entrymod = entrypointmodule.libname
let m = compilerfront2:callconfig("bitcode $(options)", allsrc + entrymod, dependentlibs)
let m2 = outlib.m
let files = compilerback(m, outname, options),
files + file(changeext(outname, "libinfo"), outbytes:midpoint([m2]))

Function makebitcode(input:seq.file, options:seq.word) seq.file
{OPTION PROFILE}
let info = breakparagraph.data.first.input
let libname = extractValue(first.info, "Library")
let outname = filename."+$(dirpath.fn.first.input + libname).bc"
let uses = extractValue(first.info, "uses")
let dep = 
 for mp = empty:midpoint, i ∈ input << 1 do
  let new = first.inbytes:midpoint(data.i),
  midpoint("", prg.mp ∪ prg.new, emptytypedict, libmods.mp + libmods.new, empty:seq.seq.word)
 /do mp
let p = process.subcompilelib(info, dep, outname, options),
if aborted.p then
 [
  file("error.html", "COMPILATION ERROR in libray:$(libname) /br $(message.p)")]
else
 result.p 