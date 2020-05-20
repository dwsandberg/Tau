Module main2

use UTF8

use fileio

use seq.firstpass

use set.firstpass

use format

use groupparagraphs

use seq.fsignrep


use intercode


/use libdesc

use process.liblib

use seq.liblib

use seq.libmod

use libscope

use seq.libsym

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

use deepcopy.seq.word

use process.seq.word

use seq.seq.seq.word

use set.seq.word

use set.word


type libinfo is record known:symbolset, mods:seq.firstpass

function addliblib(s:seq.word, a:libinfo, l:liblib)libinfo
 if(libname.l)_1 in s then
  libinfo(addknown( known.a,l), tofirstpass.l + mods.a)
 else a

function loadlibs(dependentlibs:seq.word, i:int, time:int)int
 if i > length.dependentlibs then time
 else
  let stamp = loadlibrary.dependentlibs_i
   assert stamp ≥ time report"library" + dependentlibs_i + "is out of date" + toword.time + toword.stamp
    loadlibs(dependentlibs, i + 1, stamp)

function subcompilelib(libname:word)seq.word
 PROFILE
 .
 let a = gettext.[ merge([ libname] + "/" + libname + ".ls")]
 let s = findlibclause(a, 1)
 let u = findindex("uses"_1, s, 3)
 let e = findindex("exports"_1, s, 3)
 let dependentlibs = subseq(s, u + 1, e - 1)
 let filelist = subseq(s, 2, min(u - 1, e - 1))
 let exports = subseq(s, e + 1, length.s)
 let b = unloadlib.[ libname]
 let li = if libname in "stdlibbak stdlib "then libinfo(emptysymbolset, empty:seq.firstpass)
 else
  let discard5 = loadlibs(dependentlibs, 1, timestamp.loadedlibs_1)
   @(addliblib.dependentlibs, identity, libinfo(emptysymbolset, empty:seq.firstpass), loadedlibs)
// let allsrc = @(+, gettext2(s_2), empty:seq.seq.seq.word, filelist) //
 let allsrc= getlibrarysrc.libname 
 let p1 = pass1(groupparagraphs("module Module",allsrc), exports, known.li, asset.mods.li)
 let x = basesigs(allsrc)
       let intercode2 = pass2new(symset.p1, mods.p1, known.li)  
   let bc=codegen( intercode2 , libname)
 let z2 = createlib(bc, libname, dependentlibs)
 let save = @(+, bindingformat.symset.p1, empty:seq.seq.word, mods.p1)
 let name = merge("pass1/" + libname + "." + print.currenttime + ".txt")
 let z = createfile([ name], save)
  "OK"
  
use pass2new

use codegennew

use processOptions

use libdesc


Function compilelib2(libname:word)seq.word
 PROFILE
 .
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
  let p2 = process.execute.mangle(args_3, mytype.[ args_2], empty:seq.mytype)
   if aborted.p2 then message.p2 else result.p2
 else if subseq(result.p, 1, 1) = "OK" ∧ not(length.args = 1)then
 "not correct number of args:" + args
 else result.p
  outputformat.toseqint.toUTF8(htmlheader + processpara.output)

Function testcomp(s:seq.seq.word)seq.seq.word
 let exports ="testit"
 let allsrc = groupparagraphs("module Module", s)
 let li = @(addliblib."stdlib", identity, libinfo(emptysymbolset, empty:seq.firstpass), loadedlibs)
 let r = pass1(allsrc, exports, known.li, asset.mods.li)
  @(+, bindingformat.symset.r, empty:seq.seq.word, mods.r)
  

Function firstPass(libname:word)seq.seq.word
 let a = gettext.[ merge([ libname] + "/" + libname + ".ls")]
 let s = findlibclause(a, 1)
 let u = findindex("uses"_1, s, 3)
 let e = findindex("exports"_1, s, 3)
 let dependentlibs = subseq(s, u + 1, e - 1)
 let filelist = subseq(s, 2, min(u - 1, e - 1))
 let exports = subseq(s, e + 1, length.s)
 let li = if libname in "stdlib"then libinfo(emptysymbolset, empty:seq.firstpass)
 else
  let discard5 = loadlibs(dependentlibs, 1, timestamp.loadedlibs_1)
   @(addliblib(dependentlibs), identity, libinfo(emptysymbolset, empty:seq.firstpass), loadedlibs)
    let allsrc=groupparagraphs("module Module",getlibrarysrc.s_2)
 let r = pass1(allsrc, exports, known.li, asset.mods.li)
  @(+, bindingformat(symset.r), empty:seq.seq.word, mods.r)

function bindingformat(known:symbolset, m:firstpass)seq.seq.word
     @(+, extractparsed(parameter.modname.m = mytype."T", known), empty:seq.seq.word, toseq.defines.m)
  


function extractparsed(abstract:boolean, known:symbolset, s:symbol)seq.seq.word
 let a = if abstract then src.s
 else
  let sy = lookupsymbol(known, mangledname.s)
   // assert false report [ mangledname.s]+ src.sy // src.sy
  if length.a > 0 ∧ a_1 = "parsedfunc"_1 then
  // assert false report [ mangledname.s]+ src.sy //
   let headlength = toint.a_2 + 2
    [ subseq(a, 1, headlength) + mangledname.s + subseq(a, headlength + 1, length.a)]
  else empty:seq.seq.word


Function secondPass(libname:word)seq.seq.word
 let a = gettext.[ merge([ libname] + "/" + libname + ".ls")]
 let s = findlibclause(a, 1)
 let u = findindex("uses"_1, s, 3)
 let e = findindex("exports"_1, s, 3)
 let dependentlibs = subseq(s, u + 1, e - 1)
 let filelist = subseq(s, 2, min(u - 1, e - 1))
 let exports = subseq(s, e + 1, length.s)
 let li = if libname in "stdlib"then libinfo(emptysymbolset, empty:seq.firstpass)
 else
  let discard5 = loadlibs(dependentlibs, 1, timestamp.loadedlibs_1)
   @(addliblib.dependentlibs, identity, libinfo(emptysymbolset, empty:seq.firstpass), loadedlibs)
      let allsrc =getlibrarysrc.s_2 
 let p1 = pass1(groupparagraphs("module Module",allsrc), exports, known.li, asset.mods.li)
 let x = basesigs(allsrc)
 let p2 = pass2new(symset.p1, mods.p1, known.li)
   print.p2 