#!/usr/local/bin/tau

Library newimp other     libdescfunc newparse  
 uses stdlib
 exports main
 

Module newimp

* usegraph exclude seq

run main test1

use stdlib

Module main

use stdlib

use cvttoinst

use libdescfunc

use codegen

use fileio

use other

use set.word

use pass2

use libscope

use seq.libmod

use seq.libsym

use newsymbol

use seq.symbol

use set.symbol

use seq.mytype


use seq.seq.seq.word


use textio

use groupparagraphs

Function findlibclause(a:seq.seq.word, i:int)seq.word 
 assert i < length.a report"No Library clause found"
  let s = a_i 
  if s_1 ="Library"_1 then s else findlibclause(a, i + 1)


function gettext2(libname:word, e:seq.word, a:word)seq.seq.seq.word
 @(+, identity, empty:seq.seq.seq.word, groupparagraphs("module Module", gettext.[ merge([ libname]+"/"+ a +".ls")]))
 
 function print2(l:libsym) seq.word // print.l+"mn:"+// ""+ fsig.l+instruction.l



type libinfo is record known:symbolset,mods:set.firstpass

function addliblib( a:libinfo,l:liblib) libinfo
  libinfo(@(+,tosymbol,known.a,defines.last.mods.l),
  asset.tofirstpass.l  &cup mods.a)
 
 use process.liblib
 
  use set.firstpass

function loadlibs(dependentlibs:seq.word, i:int, time:int)int 
 if i > length.dependentlibs 
  then time 
  else let stamp = loadlibrary(dependentlibs_i)
  assert stamp ≥ time report"library"+ dependentlibs_i +"is out of date"+ toword.time + toword.stamp 
  loadlibs(dependentlibs, i + 1, stamp)

Function loadlibrary(libname:word)int loadlib([ libname], 0)

 
 function subcompilelib(libname:word) seq.word
let a = gettext.[ merge( [libname]+"/"+ libname +".ls")]
  let s = findlibclause(a, 1)
  let u = findindex("uses"_1, s, 3)
  let e = findindex("exports"_1, s, 3)
  let uses = subseq(s, u + 1, e - 1)
  let filelist = subseq(s, 2, min(u - 1, e - 1))
  let exports = subseq(s, e + 1, length.s)
   let allsrc = @(+, gettext2(s_2, exports), empty:seq.seq.seq.word, filelist)
   let b = unloadlib.[libname]
   let li=if libname.last.libs="newimp" then libinfo(emptysymbolset,empty:set.firstpass)
   else 
     let discard5 = loadlibs(uses, 1, timestamp(libs_1))
     addliblib(libinfo(emptysymbolset,empty:set.firstpass),last.libs)
  let p1=pass1(allsrc,exports,known.li,mods.li)
  // let kk=      (symset.p1)_("wordencodingZstdlib"_1)  
  // // assert false report  
   @(+,print5,"",toseq.symset.p1)  //
 let intercode= pass2(symset.p1,toseq.roots.p1,known.li) 
 let liblib=libdesc( roots.p1 ,intercode ,libname,mods.p1,symset.p1) 
 let bc=codegen5(intercode,libname,liblib)
 let z2 = createlib(bc, libname, "") 
 "OK"
 
Function compilelib2(libname:word)seq.word 
 let p1 = process.subcompilelib.libname 
  if aborted.p1 
  then"COMPILATION ERROR:"+ space + message.p1 
  else let aa = result.p1 
  if subseq(aa, 1, 1)="OK"
  then aa 
  else"COMPILATION ERROR:"+ space + aa
  
use format

   use libscope
   
   use seq.liblib
   
   use prims

use process.seq.word

 
 Function main(arg:seq.int)outputformat 
 let args = towords(arg + 10 + 10)
  let libname = args_1 
  let p = process.compilelib2.libname 
  let output = if aborted.p 
   then message.p 
   else if subseq(result.p, 1, 1)="OK"∧ length.args = 3 
   then // execute function specified in arg // 
    let p2 = process.execute.mangle(args_3, mytype.[ args_2], empty:seq.mytype)
    if aborted.p2 then message.p2 else result.p2 
   else if subseq(result.p, 1, 1)="OK"∧ not(length.args = 1)
   then"not correct number of args:"+ args 
   else result.p 
  outputformat.toUTF8plus(htmlheader + processpara.output)


  @(seperator."&br  &br",print, "",defines.last.mods.liblib)
  
  @(+,modname,"",mods.liblib)

 print.intercode
 
   
 function print5(s:symbol) seq.word
   let d=decode(mangledname.s)
   if isdefined.s &and ( modname.s=mytype."internal"
    &or   subseq(d,1,15)=   decode("siQ7AeoftypeQ3A"_1) ) then
    "&br"+print2.s else ""

 

function print2(full:boolean,l:libsym) seq.word 
   if full  then  "&br"+fsig.l+":"+print.mytype.returntype.l+instruction.l
   else [fsig.l] 


function print(l:libmod) seq.word
   "&br &br"+if parameterized.l then [modname.l]+".T" else [modname.l]
   +"&br defines:"+ @(+,print2(modname.l="$other"_1),"",defines.l ) 
    +"&br exports:"+ @(+,print2(modname.l="$other"_1),"",defines.l ) 
  


/Function test1 seq.word
// compilelib2("imp2"_1) //
let t=compilelib2("imp2"_1)
assert t="OK" report "HH"+t
// "&br &br"+@(seperator."&br  &br",print, "",defines.last.mods.last.libs)
// 
let p2 = process.execute.mangle("ZXX"_1, mytype."main", empty:seq.mytype)
    (if aborted.p2 then message.p2 else towords.cast.result.p2 )

Function test1 seq.word
// compilelib2("imp2"_1) //
let t=compilelib2("imp2"_1)
assert t="OK" report "HH"+t
let t2=compilelib2("test6"_1)
assert t2="OK" report "HHH"+t2
// @(+,libname,"",libs)
"&br &br"+@(seperator."&br  &br",print, "",defines.last.mods.last.libs)
//
 //  let p2 = process.execute.mangle("gentau2"_1, mytype."genhash", empty:seq.mytype) //
 let p2 = process.execute.mangle("test6"_1, mytype."test6", empty:seq.mytype)
    (if aborted.p2 then message.p2 else result.p2 )
+"&br &br"+@(seperator."&br  &br",print, "",defines.last.mods.last.libs)
  
genlex genhash

function cast(seq.word) seq.int builtin.NOOP
 
