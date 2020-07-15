Module main2

use UTF8

use fileio

use seq.firstpass

use set.firstpass

use format

use groupparagraphs






use process.liblib

use seq.liblib


use libdesc


use seq.mytype

use set.mytype

use parse

use pass1

use prims

use stdlib

use seq.symbol

use set.symbol

use symbol

use textio

use timestamp

use otherseq.word


use process.seq.word

use seq.seq.seq.word

use set.seq.word

use set.word



function loadlibs(dependentlibs:seq.word, i:int, time:int)int
 if i > length.dependentlibs then time
 else
  let stamp = loadlibrary.dependentlibs_i
   assert stamp ≥ time report"library" + dependentlibs_i + "is out of date" + toword.time + toword.stamp
    loadlibs(dependentlibs, i + 1, stamp)

function subcompilelib(libname:word)seq.word
 let a = gettext.[ merge([ libname] + "/" + libname + ".ls")]
 let s = findlibclause(a, 1)
 let u = findindex("uses"_1, s, 3)
 let e = findindex("exports"_1, s, 3)
  let dependentlibs = dependentlibs.if libname in "stdlibbak stdlib " then "" else subseq(s, u + 1, e - 1)
 let filelist = subseq(s, 2, min(u - 1, e - 1))
 let exports = subseq(s, e + 1, length.s)
 let b = unloadlib.[ libname]
 let allsrc= getlibrarysrc.libname 
    let p1 = pass1(groupparagraphs("module Module",allsrc), exports, dependentlibs )
 let intercode2 = pass2(result.p1,compiled.p1,roots.p1,mods.p1,templates.p1,exports)
 let bc=codegen( theprg.intercode2 ,defines.intercode2,uses.intercode2,libname,libdesc.intercode2)
 let z2 = createlib(bc, libname, subseq(s, u + 1, e - 1))
 // let save = @(+, bindingformat.symset.p1, empty:seq.seq.word, mods.p1) 
 let name = merge("pass1/" + libname + "." + print.currenttime + ".txt")
 let z = createfile([ name], save) //
  "OK"
  
use pass2new

use codegennew





Function compilelib2(libname:word)seq.word
 let p1 = process.subcompilelib(libname)
  if aborted.p1 then"COMPILATION ERROR:" + space + message.p1
  else
   let aa = result.p1
    if subseq(aa, 1, 1) = "OK"then aa else"COMPILATION ERROR:" + space + aa

Function main(arg:seq.int)outputformat
 let args = towords.UTF8(arg + 10 + 10)
 let libname = args_1
 let p = process.compilelib2(libname)
 let output = if aborted.p then message.p
 else if subseq(result.p, 1, 1) = "OK" ∧ length.args = 3 then
 // execute function specified in arg //
  let p2 = process.execute.mangle2([args_3], [ args_2], empty:seq.seq.word)
   if aborted.p2 then message.p2 else result.p2
 else if subseq(result.p, 1, 1) = "OK" ∧ not(length.args = 1)then
 "not correct number of args:" + args
 else result.p
  outputformat.toseqint.toUTF8(htmlheader + processpara.output)
  
use mangle

Function testcomp(s:seq.seq.word)seq.seq.word
 let exports ="testit"
 let allsrc = groupparagraphs("module Module", s)
  let r = pass1(allsrc, exports,dependentlibs."stdlib")
  @(+,print.result.r,empty:seq.seq.word, toseq.toset.result.r)
 

Function firstPass(libname:word)seq.seq.word
 let a = gettext.[ merge([ libname] + "/" + libname + ".ls")]
 let s = findlibclause(a, 1)
 let u = findindex("uses"_1, s, 3)
 let e = findindex("exports"_1, s, 3)
  let dependentlibs = dependentlibs.if libname in "stdlibbak stdlib " then "" else subseq(s, u + 1, e - 1)
 let filelist = subseq(s, 2, min(u - 1, e - 1))
 let exports = subseq(s, e + 1, length.s)
     let allsrc=groupparagraphs("module Module",getlibrarysrc.s_2)
 let r = pass1(allsrc, exports, dependentlibs )
 @(+,print.result.r,empty:seq.seq.word, toseq.toset.result.r)
 
 
 

Function secondPass(libname:word)seq.seq.word
 let a = gettext.[ merge([ libname] + "/" + libname + ".ls")]
 let s = findlibclause(a, 1)
 let u = findindex("uses"_1, s, 3)
 let e = findindex("exports"_1, s, 3)
 let dependentlibs = dependentlibs.if libname in "stdlibbak stdlib " then "" else subseq(s, u + 1, e - 1)
 let filelist = subseq(s, 2, min(u - 1, e - 1))
 let exports = subseq(s, e + 1, length.s)
      let allsrc =getlibrarysrc.s_2 
  let p1 = pass1(groupparagraphs("module Module",allsrc), exports, dependentlibs  )
 let p2 =  pass2(result.p1,compiled.p1,roots.p1,mods.p1,templates.p1,exports)
   @(+,print.theprg.p2,empty:seq.seq.word, defines.p2)
 