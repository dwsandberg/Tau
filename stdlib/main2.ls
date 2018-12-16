Module main2

use stdlib

use cvttoinst

use libdescfuncnew

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

use format

   use libscope
   
   use seq.liblib
   
   use prims

use process.seq.word

 

  Function findlibclause(a:seq.seq.word, i:int)seq.word 
 assert i < length.a report"No Library clause found"
  let s = a_i 
  if s_1 ="Library"_1 then s else findlibclause(a, i + 1)


  function gettext2(libname:word, e:seq.word, a:word)seq.seq.seq.word
 @(+, identity, empty:seq.seq.seq.word, groupparagraphs("module Module", gettext.[ merge([ libname]+"/"+ a +".ls")]))
 
/ function print2(l:libsym) seq.word // print.l+"mn:"+// ""+ fsig.l+instruction.l



 type libinfo is record known:symbolset,mods:seq.firstpass
 
 known:symbolset,mods:set.firstpass

  function addliblib(s:seq.word, a:libinfo,l:liblib) libinfo
  if (libname.l)_1 in s then 
  libinfo(@(+,tosymbol,known.a,defines.last.mods.l),
   tofirstpass.l  + mods.a)
   else a
 
 use process.liblib
 
  use set.firstpass
  
  use textio


  function loadlibs(dependentlibs:seq.word, i:int, time:int)int 
 if i > length.dependentlibs 
  then time 
  else let stamp = loadlibrary(dependentlibs_i)
  assert stamp ≥ time report"library"+ dependentlibs_i +"is out of date"+ toword.time + toword.stamp 
  loadlibs(dependentlibs, i + 1, stamp)

 use deepcopy.seq.word
 
 function subcompilelib(libname:word) seq.word
  PROFILE. 
  let a = gettext.[ merge( [libname]+"/"+ libname +".ls")]
  let s = findlibclause(a, 1)
  let u = findindex("uses"_1, s, 3)
  let e = findindex("exports"_1, s, 3)
  let dependentlibs = subseq(s, u + 1, e - 1)
  let filelist = subseq(s, 2, min(u - 1, e - 1))
  let exports = subseq(s, e + 1, length.s)
   let b = unloadlib.[libname]
   let li=if (libname) in "newimp stdlib imp2" then libinfo(emptysymbolset,empty:seq.firstpass)
   else 
     let discard5 = loadlibs(dependentlibs, 1, timestamp(loadedlibs_1))
     @(addliblib(dependentlibs),identity,libinfo(emptysymbolset,empty:seq.firstpass), loadedlibs)
  let allsrc = @(+, gettext2(s_2, exports), empty:seq.seq.seq.word, filelist)
  let p1=pass1(allsrc,exports,known.li,asset.mods.li)
   let roots=roots.p1
 let mods=mods.p1
 let known2=symset.p1
 let intercode= pass2(symset.p1,toseq.roots.p1,known.li) 
  let bc = codegen5(intercode,libname,liblib([libname],libdesc( roots ,intercode ,mods,known2) ))
  let z2 = createlib(bc, libname, dependentlibs) 
 "OK"
 
Function compilelib2(libname:word)seq.word 
 let p1 = process.subcompilelib.libname 
  if aborted.p1 
  then"COMPILATION ERROR:"+ space + message.p1 
  else let aa = result.p1 
  if subseq(aa, 1, 1)="OK"
  then aa 
  else"COMPILATION ERROR:"+ space + aa
  

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
  
  

function loadlibrary(libname:word)int loadlib([ libname], 0)

     
 function firstPass(libname:word) seq.word
  let a = gettext.[ merge( [libname]+"/"+ libname +".ls")]
  let s = findlibclause(a, 1)
  let u = findindex("uses"_1, s, 3)
  let e = findindex("exports"_1, s, 3)
  let dependentlibs = subseq(s, u + 1, e - 1)
  let filelist = subseq(s, 2, min(u - 1, e - 1))
  let exports = subseq(s, e + 1, length.s)
   let b = unloadlib.[libname]
   let li=if (libname) in "newimp stdlib imp2" then libinfo(emptysymbolset,empty:seq.firstpass)
   else 
     let discard5 = loadlibs(dependentlibs, 1, timestamp(loadedlibs_1))
     @(addliblib(dependentlibs),identity,libinfo(emptysymbolset,empty:seq.firstpass), loadedlibs)
  let allsrc = @(+, gettext2(s_2, exports), empty:seq.seq.seq.word, filelist)
  let r=pass1(allsrc,exports,known.li,asset.mods.li)
  printcode.symset.r+@(+,print,"",mods.r)
     
     use process.linkage
     
  Function firstpassonly(libname:word) seq.word
 let p1 = process.firstPass.libname 
   assert not.aborted.p1 report "COMPILATION ERROR:"+ space + message.p1 
     result.p1 
    
     
 /function print5(s:symbol) seq.word
   let d=decode(mangledname.s)
   if isdefined.s &and ( modname.s=mytype."internal"
    &or   subseq(d,1,15)=   decode("siQ7AeoftypeQ3A"_1) ) then
    "&br"+print2.s else ""

 

/function print2(full:boolean,l:libsym) seq.word 
   if full  then  "&br"+fsig.l+":"+print.mytype.returntype.l+instruction.l
   else [fsig.l] 


/function print(l:libmod) seq.word
   "&br &br"+if parameterized.l then [modname.l]+".T" else [modname.l]
   +"&br defines:"+ @(+,print2(modname.l="$other"_1),"",defines.l ) 
    +"&br exports:"+ @(+,print2(modname.l="$other"_1),"",defines.l ) 
  


 
