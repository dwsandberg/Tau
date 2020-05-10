Module main2

use UTF8

use codegen

use fileio

use seq.firstpass

use set.firstpass

use format

use groupparagraphs

use seq.inst

use intercode


use libdesc

use process.liblib

use seq.liblib

use seq.libmod

use libscope

use seq.libsym

use seq.mytype

use set.mytype

use parse

use pass1

use pass2

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
 let b=tofirstpass.l
 libinfo(@(+, tosymbol, known.a, defines.last.mods.l), b + mods.a)
 else a

function loadlibs(dependentlibs:seq.word, i:int, time:int)int
 if i > length.dependentlibs then time
 else
  let stamp = loadlibrary.dependentlibs_i
   assert stamp ≥ time report"library" + dependentlibs_i + "is out of date" + toword.time + toword.stamp
    loadlibs(dependentlibs, i + 1, stamp)

function subcompilelib(libname:word,old:boolean)seq.word
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
 let allsrc=groupparagraphs("module Module",getlibrarysrc.libname)
 let p1 = pass1(allsrc, exports, known.li, asset.mods.li)
  let bc = if old then
   let intercode2= pass2(symset.p1, toseq.roots.p1, known.li)
   let libmods=libdesc(intercode2, mods.p1, symset.p1)
   codegen5(addlibmods(libmods,intercode2), libname,  libmods)
    else 
      let intercode2 = pass2new(symset.p1, toseq.roots.p1, known.li)  
  let libmods=libdesc(intercode2, mods.p1, symset.p1)
   codegen(addlibmods(libmods,intercode2), libname,  libmods)
 let z2 = createlib(bc, libname, dependentlibs)
 let save = @(+, bindingformat.symset.p1, empty:seq.seq.word, mods.p1)
 let name = merge("pass1/" + libname + "." + print.currenttime + ".txt")
 let z = createfile([ name], save)
  "OK"
  
use pass2new

use codegennew

Function mainnew(arg:seq.word) seq.word
   let libname=arg_1 let modname=arg_2 let funcname=arg_3
 let p = process.compilelib2(libname,false)
 if aborted.p then message.p
 else if subseq(result.p, 1, 1) = "OK" then
 // execute function specified in arg //
  let p2 = process.execute.mangle(funcname, mytype.[modname], empty:seq.mytype)
   if aborted.p2 then message.p2 else result.p2
 else result.p

Function compilelib2(libname:word,old:boolean)seq.word
 PROFILE
 .
 let p1 = process.subcompilelib(libname,old)
  if aborted.p1 then"COMPILATION ERROR:" + space + message.p1
  else
   let aa = result.p1
    if subseq(aa, 1, 1) = "OK"then aa else"COMPILATION ERROR:" + space + aa

Function main(arg:seq.int)outputformat
 let args = towords.UTF8(arg + 10 + 10)
 let libname = args_1
 let p = process.compilelib2(libname,false)
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
 // let allsrc = @(+, gettext2(s_2 ), empty:seq.seq.seq.word, filelist) //
 let r = pass1(allsrc, exports, known.li, asset.mods.li)
  @(+, bindingformat(symset.r), empty:seq.seq.word, mods.r)

function bindingformat(known:symbolset, m:firstpass)seq.seq.word
 if length.rawsrc.m = 0 then empty:seq.seq.word
 else
  let header = moduleHeaderLines(rawsrc.m, 2)
  let autouses = @(+, extractencoding, empty:seq.mytype, rawsrc.m)
  let uses = @(+, formatuse, empty:set.seq.word, toseq(asset.uses.m - asset.autouses))
  let dd = @(+, extractparsed(parameter.modname.m = mytype."T", known), empty:seq.seq.word, toseq.defines.m)
   @(+, bindingfind(dd), ["module" + print.modname.m] + header + alphasort.toseq.uses, subseq(rawsrc.m, length.header + 2, length.rawsrc.m))

function moduleHeaderLines(s:seq.seq.word, i:int)seq.seq.word
 if i > length.s then empty:seq.seq.word
 else
  let p = s_i
   if length.p = 0 then ["skip"] + moduleHeaderLines(s, i + 1)
   else if p_1 in "function Function type use"then empty:seq.seq.word
   else
    [ if p_1 = "Library"_1 then p else"skip" + p]
    + moduleHeaderLines(s, i + 1)

function extractencoding(s:seq.word)seq.mytype
 if length.s > 3 ∧ s_1 = "type"_1
 ∧ s_4 in "Encoding encoding"then
 [ mytype(towords.parameter.(types.parse(headdict, s))_1 + "encodingstate")]
 else empty:seq.mytype

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

function formatuse(m:mytype)seq.word"use" + print.m

function bindingfind(defines:seq.seq.word, s:seq.word)seq.seq.word
 if length.s = 0 then ["skip" + s]
 else if s_1 in "function Function"then bindingfind2(defines, 1, s)
 else if s_1 in "use Use"then empty:seq.seq.word
 else if s_1 = "Library"_1 then [ s]else ["skip" + s]

function bindingfind2(defines:seq.seq.word, i:int, key:seq.word)seq.seq.word
 if i > length.defines then ["skip" + key]
 else
  let d = defines_i
  let l = toint.d_2
   if subseq(d, 3, l + 2) = subseq(key, 1, l)then [ defines_i]
   else bindingfind2(defines, i + 1, key)

/function print5(s:symbol)seq.word let d = decode(mangledname.s)if isdefined.s &and(modname.s = mytype."internal"&or subseq(d, 1, 15)= decode("siQ7AeoftypeQ3A"_1))then"
&br"+ print2.s else""

/function print2(full:boolean, l:libsym)seq.word if full then"
&br"+ fsig.l +":"+ print.mytype.returntype.l + instruction.l else [ fsig.l]

/function print(l:libmod)seq.word"
&br 
&br"+ if parameterized.l then [ modname.l]+".T"else [ modname.l]+"
&br defines:"+ @(+, print2(modname.l ="$other"_1),"", defines.l)+"
&br exports:"+ @(+, print2(modname.l ="$other"_1),"", defines.l)

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
      let allsrc=groupparagraphs("module Module",getlibrarysrc.s_2)
 //
 let allsrc = @(+, gettext2(s_2), empty:seq.seq.seq.word, filelist) //
 let p1 = pass1(allsrc, exports, known.li, asset.mods.li)
 let p2 = pass2(symset.p1, toseq.roots.p1, known.li)
   print.p2 