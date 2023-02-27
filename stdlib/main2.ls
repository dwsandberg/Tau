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



Function libsrc(input:seq.file, uses:seq.word, exports:seq.word, o:seq.word) seq.file
{ } let outname = filename.o
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
   "Library = $(Library) "
    ,
 [file(outname, toseqbyte.textformat.firstpart + acc1 + acc2)]
 
 use pretty

function subcompilelib(input:seq.file, outname:filename, options:seq.word) seq.file
{OPTION PROFILE}
let m = compilerFront:callconfig("bitcode $(options)", input)
let m2 = outlib.m
{  First line of src.m was added by compilerFront so remove it}
     for all="",lib="",libs=empty:seq.file,   p /in src.m << 1 +["Library=?"] do  
     if  subseq(p,1,2)="Library=" then 
         next(all+"/p"+lib,p,   if isempty.lib /or name.outname = lib_3 
         then libs else libs+
         file(filename("+"+dirpath.outname+ lib_3+".libsrc"), lib))
     else 
       next(all,lib+"/p"+ 
   if subseq(p,1,1) /in ["Function","function"] then pretty.p else p
   ,libs)  
   /do  
    assert true report for txt="" , f /in libs do
      txt+fullname.fn.f /do txt
  compilerback(m, outname, options)
   + file(changeext(outname, "libinfo"), outbytes:midpoint([m2]))
+file(changeext(outname, "libsrc"),all)
+libs 

Function makebitcode(input:seq.file, options:seq.word, libname:seq.word
,exports:seq.word,uses:seq.word,o:seq.word) seq.file
{OPTION PROFILE} 
 let fn=filename.o
let outname = filename."+$(dirpath.fn + libname).bc"
let tmp =" Library=$(libname) uses=$(uses) exports=$(exports )"
let p = process.subcompilelib( [ file("??.ls", tmp)]+input , outname, options),
if aborted.p then
 [
  file("error.html", "COMPILATION ERROR in libray:$(libname) /br $(message.p)")]
else
 result.p 