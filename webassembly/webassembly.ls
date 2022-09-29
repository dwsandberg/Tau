Module webassembly

* usegraph exclude standard seq set otherseq bits encoding UTF8 stack

use UTF8

use bits

use seq.byte

use file

use seq.file

use libllvm

use compilerfrontT.libllvm

use standard

use seq.symbol

use symbol2

use set.symdef

use textio

use wasmcompile

Function cat(files:seq.file, uses:seq.word, exports:seq.word, Library:seq.word)seq.file
for acc = empty:seq.byte, names = "parts=", f ∈ files do
 if ext.fn.f ∈ "ls libsrc"then next(acc + tobyte.10 + tobyte.10 + data.f, names + fullname.fn.f)
 else next(acc, names)
/for([file(filename(Library + ".libsrc")
, toseqbyte.toUTF8(names + "uses=$(uses)exports=$(exports)Library=$(Library)")
+ acc
)
])

Function wasm(input:seq.file, Library:seq.word, exports:seq.word, o:seq.word, info:boolean)seq.file
{problem is same symbol is used in different onclicks}
let includetemplate = false
let input2 = cat(input, "", exports, Library)
let info2 = breakparagraph.data.first.input2
let libname = Library
let libexports = exports + "SpecialExports" + "SpecialImports"
let rcinfo = 
 compilerFront:libllvm("wasm"
 , [file("hhh.ls"
 , "exports=tausupport webIOtypes $(libexports)Library=$(libname)"
 )
 ]
 + input
 )
{assert Library /ne"webtools"report for txt="", sd /in toseq.prg.rcinfo do if not.isconst.sym.sd /and name.sym.
  sd /in"newstk"then txt+"
  /p"+print.sym.sd+print.subseq(code.sd, 1, 5)else txt /for(txt)}
for syms2 = empty:seq.symbol, imports = empty:seq.symbol, m ∈ libmods.rcinfo do
 if name.modname.m ∈ "SpecialImports"then next(syms2, imports + exports.m)
 else if name.modname.m ∈ libexports then next(syms2 + exports.m, imports)else next(syms2, imports)
/for({should check for dup names on syms2}
let scriptstart = 
 for txt = "<script>  /br", sym ∈ syms2 do
  let f = 
   for args = "", i ∈ arithseq(nopara.sym, 1, 1)do args + "a b c d e f g h i j k l m n o p q r s t u v w x y z"_i + ", "/for([name.sym] + "(" + args >> 1 + ")")
  {Cannot just call reclaimspace after call to function f because f may be interpreted and return control will waiting
    for a callback. javascript global inprogress counts the number of callbacks we are waiting for. if inprogress is
    zero then it is safe to reclaim space.}
  txt
  + "function"
  + f
  + "{exports."
  + f
  + "; if(inprogress==0)exports.reclaimspace();} /br"
 /for(txt)
let wasmfiles = wasmcompile(typedict.rcinfo, asset.renumberconstants.toseq.prg.rcinfo, syms2, o, imports, info)
let script = 
 {if includetemplate then toseqbyte.toUTF8."<script>"+getfile:byte("/webassembly/template.js")+toseqbyte
   .toUTF8."</script>"else}
 toseqbyte.toUTF8("<script src=" + dq + "/webassembly/template.js" + dq + "> </script>")
for acc = wasmfiles, page ∈ input do
 if ext.fn.page ∉ "html"then acc
 else
  let pagehtml = data.page
  acc
  + file(filename("+" + dirpath.fn.first.wasmfiles + [name.fn.page] + ".html")
  , pagehtml + script
  + toseqbyte.toUTF8(scriptstart
  + " /br pageinit($(dq.libname), $([name.fn.page])); </script>")
  )
/for(acc))

Function doc seq.word
"Steps to call function f1 as a process.
  /br 1. Create a record, R. The first two fields are deepcopy function for the result type of f1 and seq.word. The third
  field is the webassembly funcidx. The remain fields are the actual parameters of f1.
  /br 2. get typeidx for f1. Let assume the typeidx is 45.
  /br 3. create at compile time a function processX45 that takes the record R and funcidx of f1 as parameters, unpacks the
  record R and calls the third field in R. In this case it will call f1. 
  /br 4. call the javascript function callprocess with R and function index of processX45 as parameters.
  /br 5. callprocess will call exported function,  /em processbody, with R and processX45 as parameters
  /br 6. processbody will call  /em processX45 with R as parameter in a new process context and restore the orignal
  context when it finishes. if the first field of R is not zero then it will deepcopy the result. Finally it will release
  any space used by the new process.
  /br 7. If f1 aborts then processbody will catch the error and call exported function  /em handleerror
  /br 8.  /em handleerror restores the parent process context and copies the errormessage to the parent process. 
  Finally it will release any space used by the process" 