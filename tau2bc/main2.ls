Module main2

use UTF8

use bits

use seq.byte

use compilerfrontT.callconfig

use codegen

use compilerfront

use file

use seq.file

use process.seq.file

use seq.filename

use llvmcode

use objectio.midpoint

use pretty 

use standard

use seq1.word

use seq1.seq.word

use seq.seq.word

Function makebitcode(
input:seq.file
, exports:seq.word
, info:boolean
, profile:boolean
, showllvm:seq.word
, entryUses:seq.word
, output:seq.word
) seq.file
{COMMAND OPTION PROFILE /strong makebitcode compiler /br
Options:/br
/strong entryUses addition use clause added to module when building entry point. /br
/strong profile generates information for profiling /br
/strong showllvm show text form of llvm code generated for the names of procedure given./br
/info show text form of code info /br
/exports list of packes to show. }
let options =
 (if info then "info: " else "")
  + (if profile then "profile: " else "")
  + (if not.isempty.showllvm then "showllvm: :(showllvm)" else "")
let outfn = tofilenames.output
let p = process.subcompile(input, outfn, options, exports, entryUses),
if aborted.p then [file("error.html", "COMPILATION ERROR in libray::(name.outfn sub 1) /br:(message.p)")]
else result.p

function subcompile(
input:seq.file
, outfn:seq.filename
, options:seq.word
, exports:seq.word
, entryUses:seq.word
) seq.file
{OPTION PROFILE First line of src.m was added by compilerFront so remove it}
for uses = "", e ∈ input
do if ext.fn.e ∈ "libinfo" then uses + name.fn.e else uses
let m =
 compilerFront:callconfig(
  "bitcode uses: :(uses):(options) Library::(name.outfn sub 1)"
  , input
  , exports
  , entryUses
 )
let p = process.compilerback(m, changeext(outfn sub 1, "bc"), options, uses)
assert not.aborted.p report message.p,
result.p
 + file(changeext(outfn sub 1, "libinfo"), outbytes:midpoint([outlib.m]))
 + libsrc(m, outfn) 
