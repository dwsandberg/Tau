Module main2

use codegen

use cvttoinst

use deepcopy.seq.word

use fileio

use format

use groupparagraphs

use libdescfunc

use libscope

use oseq.word

use pass1

use parse

use pass2

use prims

use process.liblib

use process.seq.word

use seq.liblib

use seq.libmod

use seq.libsym

use seq.mytype

use seq.seq.seq.word

use seq.symbol

use set.firstpass

use set.mytype

use set.seq.word

use set.symbol

use set.word

use stdlib

use symbol

use textio

use UTF8

Function findlibclause(a:seq.seq.word, i:int)seq.word 
 assert i < length.a report"No Library clause found"
  let s = a_i 
  if s_1 ="Library"_1 then s else findlibclause(a, i + 1)

function gettext2(libname:word, e:seq.word, a:word)seq.seq.seq.word 
 @(+, identity, empty:seq.seq.seq.word, groupparagraphs("module Module", gettext.[ merge([ libname]+"/"+ a +".ls")]))

/function print2(l:libsym)seq.word // print.l +"mn:"+ //""+ fsig.l + instruction.l

type libinfo is record known:symbolset, mods:seq.firstpass

known:symbolset, mods:set.firstpass

function addliblib(s:seq.word, a:libinfo, l:liblib)libinfo 
 if libname(l)_1 in s 
  then libinfo(@(+, tosymbol, known.a, defines.last.mods.l), tofirstpass.l + mods.a)
  else a

function loadlibs(dependentlibs:seq.word, i:int, time:int)int 
 if i > length.dependentlibs 
  then time 
  else let stamp = loadlibrary(dependentlibs_i)
  assert stamp ≥ time report"library"+ dependentlibs_i +"is out of date"+ toword.time + toword.stamp 
  loadlibs(dependentlibs, i + 1, stamp)

function subcompilelib(libname:word)seq.word 
 PROFILE.let a = gettext.[ merge([ libname]+"/"+ libname +".ls")]
  let s = findlibclause(a, 1)
  let u = findindex("uses"_1, s, 3)
  let e = findindex("exports"_1, s, 3)
  let dependentlibs = subseq(s, u + 1, e - 1)
  let filelist = subseq(s, 2, min(u - 1, e - 1))
  let exports = subseq(s, e + 1, length.s)
  let b = unloadlib.[ libname]
  let li = if libname in"newimp stdlib imp2"
   then libinfo(emptysymbolset, empty:seq.firstpass)
   else let discard5 = loadlibs(dependentlibs, 1, timestamp(loadedlibs_1))
   @(addliblib.dependentlibs, identity, libinfo(emptysymbolset, empty:seq.firstpass), loadedlibs)
  let allsrc = @(+, gettext2(s_2, exports), empty:seq.seq.seq.word, filelist)
  let p1 = pass1(allsrc, exports, known.li, asset.mods.li)
  let roots = roots.p1 
  let mods = mods.p1 
  let known2 = symset.p1 
  let intercode = pass2(symset.p1, toseq.roots.p1, known.li)
  let bc = codegen5(intercode, libname, liblib([ libname], libdesc(roots, intercode, mods, known2)))
  let z2 = createlib(bc, libname, dependentlibs)
  let save=@(+, bindingformat.symset.p1, empty:seq.seq.word, mods.p1)
  let name= merge("pass1/"+libname+"."+print.currenttime +".txt")
  let z= createfile( [name],save)
  {"OK"}

use timestamp

Function compilelib2(libname:word)seq.word 
 PROFILE.let p1 = process.subcompilelib.libname 
  if aborted.p1 
  then"COMPILATION ERROR:"+ space + message.p1 
  else let aa = result.p1 
  if subseq(aa, 1, 1)="OK"
  then aa 
  else"COMPILATION ERROR:"+ space + aa

Function main(arg:seq.int)outputformat 
 let args = towords.UTF8(arg + 10 + 10)
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

Function testcomp(s:seq.seq.word)seq.seq.word 
 let exports ="testit"
  let allsrc = groupparagraphs("module Module", s)
  let li = @(addliblib."stdlib", identity, libinfo(emptysymbolset, empty:seq.firstpass), loadedlibs)
  let r = pass1(allsrc, exports, known.li, asset.mods.li)
  @(+, bindingformat.symset.r, empty:seq.seq.word, mods.r)

Function firstPass(libname:word)seq.seq.word 
 let a = gettext.[ merge([ libname]+"/"+ libname +".ls")]
  let s = findlibclause(a, 1)
  let u = findindex("uses"_1, s, 3)
  let e = findindex("exports"_1, s, 3)
  let dependentlibs = subseq(s, u + 1, e - 1)
  let filelist = subseq(s, 2, min(u - 1, e - 1))
  let exports = subseq(s, e + 1, length.s)
  let li = if libname in"stdlib"
   then libinfo(emptysymbolset, empty:seq.firstpass)
   else let discard5 = loadlibs(dependentlibs, 1, timestamp(loadedlibs_1))
   @(addliblib.dependentlibs, identity, libinfo(emptysymbolset, empty:seq.firstpass), loadedlibs)
  let allsrc = @(+, gettext2(s_2, exports), empty:seq.seq.seq.word, filelist)
  let r = pass1(allsrc, exports, known.li, asset.mods.li)
  @(+, bindingformat.symset.r, empty:seq.seq.word, mods.r)

function moduleHeaderLines(s:seq.seq.word, i:int)seq.seq.word 
 if i > length.s 
  then empty:seq.seq.word 
  else let p = s_i 
  if length.p = 0 
  then ["skip"]+ moduleHeaderLines(s, i + 1)
  else if p_1 in"function Function type use"
  then empty:seq.seq.word 
  else [ if p_1 ="Library"_1 then p else"skip"+ p]+ moduleHeaderLines(s, i + 1)

function bindingformat(known:symbolset, m:firstpass)seq.seq.word 
 if length.rawsrc.m = 0 
  then empty:seq.seq.word 
  else let header = moduleHeaderLines(rawsrc.m, 2)
  let autouses = @(+, extractencoding, empty:seq.mytype, rawsrc.m)
  let uses = @(+, formatuse, empty:set.seq.word, toseq(asset.uses.m - asset.autouses))
  let dd = @(+, extractparsed(parameter.modname.m = mytype."T", known), empty:seq.seq.word, toseq.defines.m)
  // assert length.dd > 0 report"empty dd"+ print.modname.m + toword.length.toseq.defines.m // 
  // ["start defines"+ print.modname.m]+ dd + ["end defines"+ print.modname.m]+ // 
  // ["ENCODINGS"+ @(+, print,"", @(+, extractencoding, empty:seq.mytype, rawsrc.m))]+ // 
  @(+, bindingfind.dd, ["module"+ print.modname.m]+ header + alphasort.toseq.uses, subseq(rawsrc.m, length.header + 2, length.rawsrc.m))

function extractencoding(s:seq.word)seq.mytype 
 if length.s > 3 ∧ s_1 ="type"_1 ∧ s_4 in"Encoding encoding"
  then [ mytype(towords.parameter(types(parse(headerdict, s))_1)+"encodingstate")]
  else empty:seq.mytype

function extractparsed(abstract:boolean, known:symbolset, s:symbol)seq.seq.word 
 // assert not(name.s ="cindex"_1)report [ mangledname.s]+ if abstract then"abstract"else""// 
  let a = if abstract 
   then src.s 
   else let sy = lookupsymbol(known, mangledname.s)
   // assert false report [ mangledname.s]+ src.sy parsedfunc 7 = 2 wordfreq wordfreq boolean a b falseZstdlib // 
   src.sy 
  if length.a > 0 ∧ a_1 ="parsedfunc"_1 
  then let headlength = toint(a_2)+ 2 
   [ subseq(a, 1, headlength)+ mangledname.s + subseq(a, headlength + 1, length.a)]
  else empty:seq.seq.word

function formatuse(m:mytype)seq.word {"use"+ print.m }

function bindingfind2(defines:seq.seq.word, i:int, key:seq.word)seq.seq.word 
 if i > length.defines 
  then empty:seq.seq.word 
  else if getkey(defines_i)= key then [ defines_i]else bindingfind2(defines, i + 1, key)

function getkey(a:seq.word)seq.word 
 if a_1 in"function record sequence encoding Encoding Function"
  then a 
  else assert a_1 ="parsedfunc"_1 report"JKLL"+ a 
  subseq(a, 3, toint(a_2) - toint(a_4)+ 1)

function bindingfind(defines:seq.seq.word, s:seq.word)seq.seq.word 
 if length.s = 0 
  then ["skip"+ s]
  else if s_1 in"function Function"
  then let a = parsedresult.parse(headerdict, getheader.s)
   let b = bindingfind2(defines, 1, getkey.a)
   let c = if length.b = 0 
    then let headlength = toint(a_2)+ 2 
     [ subseq(a, 1, headlength)+"unknown"+ subseq(a, headlength + 1, length.a)]
    else b 
   let d = if s_1 in"Function"then ["Parsedfunc"+ subseq(c_1, 2, length(c_1))]else c 
   if d_1_(toint(d_1_2)+ 4)="stubZtest"_1 then ["skip"+ s]else d 
  else if s_1 in"use Use"
  then empty:seq.seq.word 
  else if s_1 ="Library"_1 then [ s]else ["skip"+ s]

function xx(s:seq.word)seq.word parsedresult.parse(headerdict, getheader.s)

function findexport(sq:seq.symbol, name:word, types:seq.mytype, i:int)seq.word 
 if i > length.sq 
  then"?"
  else let s = sq_i 
  if name.s = name ∧ paratypes.s = types then print.modname.s else findexport(sq, name, types, i + 1)

/function print5(s:symbol)seq.word let d = decode(mangledname.s)if isdefined.s &and(modname.s = mytype."internal"&or subseq(d, 1, 15)= decode("siQ7AeoftypeQ3A"_1))then"&br"+ print2.s else""

/function print2(full:boolean, l:libsym)seq.word if full then"&br"+ fsig.l +":"+ print.mytype.returntype.l + instruction.l else [ fsig.l]

/function print(l:libmod)seq.word"&br &br"+ if parameterized.l then [ modname.l]+".T"else [ modname.l]+"&br defines:"+ @(+, print2(modname.l ="$other"_1),"", defines.l)+"&br exports:"+ @(+, print2(modname.l ="$other"_1),"", defines.l)

