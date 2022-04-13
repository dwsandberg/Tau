Module main2


use UTF8

use bits

use codegennew

use compilerfront

use format

use inputoutput

use libraryModule

use standard

use symbol

use textio

use timestamp

use typedict

use words

use bitcast:UTF8

use seq.byte

use otherseq.char

use process.compileinfo

use process.int

use bitcast:int

use seq.liblib

use compilerfrontT.libllvm

use pass2T.libllvm

use set.modref

use seq.mytype

use set.mytype

use seq.symbol

use set.symbol

use seq.symbolref

use seq.symdef

use set.symdef

use otherseq.word

use set.word

use process.seq.bits

use encoding.seq.char

use seq.seq.char

use seq.seq.mytype

use process.seq.word

use seq.seq.word

use set.seq.word

use process.seq.seq.word

use seq.seq.seq.word

function makeentry(input:seq.byte) seq.byte
let entryheader="use standard /p use file /p use fileIO /p use seq.file
/p Function entrypoint(args0:UTF8)UTF8
/br let args = towords.args0 
/br let input=getfiles.args
/br let cmd= first.args  /br finishentry."
 for acc="", modname="?"_1, mods="", p /in  breakparagraph.input  do
   if subseq(p,1,1) = "Function" /and subseq(p,3,8)=  "(input:seq.file"   then
     let idx=findindex(")"_1,p)
       next(for  para="" ,name=","_1,last=","_1,type="",      w /in subseq(p,10,idx) do
         if w /in ",)" then
            next(para+if type="seq.word" then 
                ",extractValue(args,$(dq.[name]))"
            else ",?",name,w,"")
         else if last /in ":" then 
            next(para,name,last,type+w)
         else if last /in "," then
              next(para,w,w,"")
         else 
           next(para,name,w,type) 
         /for( acc+ "/br   else if  cmd /in $(dq.subseq(p,2,2)) then $(subseq(p,2,2))(input $(para))") 
     ,modname,mods+modname)
     else if  length.p > 1 /and p_1 /in "Module" then
       next(acc,p_2,mods)
   else next(acc,modname,mods) 
   /for(let uses=for uses="", u /in toseq.asset.mods do 
      uses+"use" +u +"/p" 
    /for(uses)
    [tobyte(10),tobyte(10)]+toseqbyte.textformat(uses+ entryheader+(acc << 2) +"/br  else empty:seq.file  "))



function cat(input:seq.file,uses:seq.word,exports:seq.word,Library:seq.word) seq.file
   for acc=empty:seq.byte,names="parts=",f /in input do 
     if ext.fn.f /in "ls libsrc" then 
      next(acc+tobyte(10)+tobyte(10)+data.f  ,names+fullname.fn.f) 
     else next(acc,names)
   /for(  let firstpart=if isempty.exports then 
     toseqbyte.toUTF8(names+"uses=$(uses)exports=$(exports)Library=$(Library)")
     else 
       let entrypointname=merge(Library+"$EP")
       toseqbyte.toUTF8(names+"uses=$(uses)exports=$(exports+entrypointname)Library=$(Library)")
       +tobyte(10)+tobyte(10)+toseqbyte.toUTF8("Module"+entrypointname)+makeentry.acc 
   [file(filename(Library+".libsrc"),firstpart+acc)])
   

Function subcompilelib(info:seq.seq.word)seq.bits
{OPTION PROFILE}
let p = compileinfo:libllvm("all", info)
assert not.aborted.p report message.p
let cinfo = result.p
codegen(last.extractValue(first.info, "Library")
, extractValue(first.src.cinfo, "uses")
, cinfo
)

Function compileinfo:libllvm(option:seq.word, info:seq.seq.word)process.compileinfo
{OPTION INLINE}
let dependentlibs = dependentinfo:libllvm(extractValue(first.info, "uses"))
process.compilerfront4:libllvm(option, info, dependentlibs) 


Function entrypoint(arg:UTF8)UTF8 
let args0=towords.arg
let args=if  first.args0 /in "libsrc" then args0
    else if args0="stdlib" then "stdlib +built stdlib.libsrc"
else args0
let input=getfiles.args
let cmd=first.args
finishentry.if cmd /in "libsrc" then
     cat(input, extractValue(args, "uses"), extractValue(args, "exports"), extractValue(args, "Library"))
  else 
  stdlib.input
   
  
use file

use fileIO

use seq.file

 Function stdlib(input:seq.file) seq.file
 let info=breakparagraph.data.first.input 
 let libname = extractValue(first.info, "Library")
 let p = process.subcompilelib.info
 [if aborted.p then
   file("error.html","COMPILATION ERROR in libray:" + libname + EOL + message.p) 
 else
 file(  filename(libname + ".bc"),result.p )] 


Function entrywrapper(t:int, newarg:UTF8)UTF8
let p2 = 
 createthread(funcaddress.deepcopySym.typeref."UTF8 UTF8"
 , funcaddress.deepcopySym.seqof.typeword
 , t
 , [bitcast:int(toptr.newarg)]
 , 4
 )
let r = if aborted.p2 then HTMLformat.message.p2 else bitcast:UTF8(toptr.result.p2)
let discard = createfile("stdout", toseqbyte(toUTF8.htmlheader + r))
r

Function astext(info:compileinfo)seq.seq.word
for acc = empty:seq.seq.word, p ∈ prg.info do acc + [print.sym.p + print.code.p]/for(acc)

Function compilerfront(option:seq.word, info:seq.seq.word)compileinfo
let p = compileinfo:libllvm(option, info)
assert not.aborted.p report message.p
result.p

Function compilerfront:libllvm(option:seq.word, allsrc:seq.seq.word)compileinfo
compilerfront4:libllvm(option, allsrc, dependentinfo:libllvm(extractValue(first.allsrc, "uses")))

function funcaddress:libllvm(sym:symbol)int funcaddress.sym

function buildargcode:libllvm(sym:symbol, typedict:typedict)int
{needed because the call interface implementation for reals is different than other types is some implementations}
for acc = 1, typ ∈ paratypes.sym + resulttype.sym do acc * 2 + if basetype(typ, typedict) = typereal then 1 else 0 /for(acc)

_______________

Function addlibrarywords(l:liblib)int
let discard = addencodingpairs.words.l
1

Export type:libllvm

type libllvm is a:int

function dependentinfo:libllvm(dependentlibs:seq.word)loadedresult
for org = empty:loadedresult, ll ∈ loadedLibs do
 let libname = (libname.ll)_1
 if libname ∈ dependentlibs then toloadedresult(org, libinfo.ll, libname)else org
/for(org) 