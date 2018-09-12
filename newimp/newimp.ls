#!/usr/local/bin/tau

Library newimp     
 uses stdlib
 exports main newimp



Module newimp

* usegraph exclude seq

run newimp test1


use stdlib

use main2

use seq.mytype

use libscope

use prims

use process.seq.word

use seq.liblib

use seq.libmod

use seq.libsym


Function test1 seq.word
// compilelib2("imp2"_1) //
let t=compilelib2("imp2"_1)
assert t="OK" report "HH"+t
let t2=compilelib2("test4"_1)
assert t2="OK" report "HHH"+t2
// @(+,libname,"",libs)
"&br &br"+@(seperator."&br  &br",print, "",defines.last.mods.last.libs)
//
 //  let p2 = process.execute.mangle("gentau2"_1, mytype."genhash", empty:seq.mytype) //
 let p2 = process.execute.mangle("test4"_1, mytype."test4", empty:seq.mytype)
    (if aborted.p2 then message.p2 else result.p2 )
+"&br &br"+@(seperator."&br  &br",print, "",defines.last.mods.last.libs)


  HH COMPILATION ERROR: DDD3 WORDS 16 9 seq.word int seq.templatepart word int seq.int int int int 
  bb PARAM 1 LIT 0 IDXUC deepcopyQ3AseqQ2EwordZdeepcopy PARAM 1 LIT 1 IDXUC deepcopyQ3AseqQ2EtemplatepartZdeepcopy PARAM 1 LIT 2 IDXUC PARAM 1 LIT 3 IDXUC deepcopyQ3AseqQ2EintZdeepcopy PARAM 1 LIT 4 IDXUC PARAM 1 LIT 5 IDXUC RECORD 6

function subfld(desc:seq.word, i:int, fldno:int, starttype:int)seq.word 
 if i > length.desc 
  then "RECORD"+ toword.fldno 
else if  i < length.desc &and desc_(i+1) ="."_1 
 then subfld(desc, i + 2, fldno, starttype)
 else  
 let fldtype =mytype.@(+,_(desc),"",arithseq( (i-starttype+2) / 2,-2,i))
 "PARAM 1 LIT"+ toword.fldno +"IDXUC"+ deepcopymangle.fldtype+subfld(desc, i + 1, fldno+1, i+1)
  
  "RECORD"+ toword.fldno 
  else if desc_i ="."_1 
  then subfld(desc, i + 2, fldno, starttype)
  else if desc_i ="seq"_1 
  then subfld(desc, i + 1, fldno, i)
  else    let fldtype= mytype.if starttype > 0 then @(+,_(desc),"",arithseq( (i-starttype+1) / 2,-2,i-1)) else [desc_(i-1)] 
   {"PARAM 1 LIT"+ toword.fldno +"IDXUC"+ deepcopymangle.fldtype+ subfld(desc, i + 1, fldno + 1, 0)} 
   
function deepcopymangle(m:mytype) seq.word print.m  
 
