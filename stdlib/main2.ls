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

use makeentry

use objectio.midpoint

use newPretty

use standard

use otherseq.word

use otherseq.seq.word

use seq.seq.word

Function entrypoint(input:seq.file, entryUses:seq.word) seq.word
{ENTRYPOINT}
%("/p", modEntry(breakparagraph.input, entryUses))

Function libsrc(input:seq.file, uses:seq.word, exports:seq.word, o:seq.word) seq.file
{ENTRYPOINT}
let outname = filename.o
let Library = [name.outname]
for acc1 = empty:seq.byte, acc2 = empty:seq.byte, f ∈ input
do
 if ext.fn.f ∈ "ls" then
 next(acc1 + tobyte.10 + tobyte.10 + data.f, acc2)
 else if ext.fn.f ∈ "libsrc" then
 next(acc1, acc2 + tobyte.10 + tobyte.10 + data.f)
 else next(acc1, acc2)
let firstpart = "Library =^(Library)",
[file(outname, toseqbyte.textformat.firstpart + acc1 + acc2)]

function subcompilelib(
 input:seq.file
 , outname:filename
 , options:seq.word
 , libname:seq.word
 , exports:seq.word
 , entryUses:seq.word
) seq.file
{OPTION XPROFILE First line of src.m was added by compilerFront so remove it}
let m = compilerFront:callconfig("bitcode^(options)", input, libname, exports, entryUses)
let m2 = outlib.m
for all = "", lib = "", libs = empty:seq.file, p ∈ src.m << 1 + ["Library = ?"]
do
 if subseq(p, 1, 2) = "Library =" then
 next(
  all + "/p" + lib
  , p
  , if isempty.lib ∨ name.outname = 3_lib then
   libs
   else libs + file(filename("+^(dirpath.outname)" + 3_lib + ".libsrc"), lib)
 )
 else next(
  all
  , lib
   + "/p"
   + 
    if subseq(p, 1, 1) ∈ ["Function", "function", "Export", "type"] then
    prettyNoChange.p
    else escapeformat.p
  , libs
 ),
compilerback(m, outname, options)
 + file(changeext(outname, "libinfo"), outbytes:midpoint([m2]))
 + file(changeext(outname, "libsrc"), all)
 + libs

Function makebitcode(
 input:seq.file
 , libname:seq.word
 , exports:seq.word
 , uses:seq.word
 , info:boolean
 , profile:boolean
 , showllvm:seq.word
 , entryUses:seq.word
) seq.file
{OPTION ENTRYPOINT}
let options =
 (if info then "info =" else "")
 + (if profile then "profile =" else "")
 + if not.isempty.showllvm then "showllvm =^(showllvm)" else ""
let outname = filename."+built^(libname).bc"
let tmp = "Library =^(libname) uses =^(uses)"
let p = process.subcompilelib([file("??.ls", tmp)] + input, outname, options, libname, exports, entryUses),
if aborted.p then
[file("error.html", "COMPILATION ERROR in libray:^(libname) /br^(message.p)")]
else result.p 