Module main

use codegen

use definestruct

use fileio

use format

use libdesc

use libdescfunc


use libscope

use pass0

use pass1a

use pass2a

use passcommon


use prims

use process.liblib

use process.pass1result

use process.seq.moddesc

use process.seq.word

use process.set.mod2desc

use seq.libdesc

use seq.liblib

use seq.libmod

use seq.libsym

use seq.libtype

use seq.mod2desc

use seq.moddesc

use seq.mytype

use seq.process.pass1result

use seq.seq.seq.word

use seq.seq.word

use seq.syminfo

use set.mod2desc

use set.syminfo

use set.libtype

use stdlib

use textio

use seq.word

use seq.seq.int

use seq.inst

use seq.int

use invertedseq.libsym

Function main(arg:seq.int)outputformat 
 let args = towords(arg + 10 + 10)
  let libname = args_1 
  let p = process.compilelib.libname 
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

Function loadlibrary(libname:word)int loadlib([ libname], 0)

Function bindings(libname:word)pass1result 
 let discard3 = length.mapping.libsymencoding 
  let ld = tolibdesc.libname 
  // let b = unloadlib.[ libname]// 
  let discard5 = loadlibs(dependentlibs.ld, 1, timestamp(libs_1))
  let templatesin = @(asliblib.dependentlibs.ld, identity, emptyliblib, libs)
  let ptext = process.pass0.ld 
  assert not.aborted.ptext report message.ptext 
  pass1a(true, result.ptext, YYY.templatesin, [ libname])

/Function pass(passno:int, libname:word)pass1result 
 let ld = tolibdesc.libname 
  // let b = unloadlib.[ libname]// 
  let discard5 = loadlibs(dependentlibs.ld, 1, timestamp(libs_1))
  let templatesin = @(asliblib.dependentlibs.ld, identity, emptyliblib, libs)
  let ptext = process.pass0.ld 
  assert not.aborted.ptext report message.ptext 
  let p1a = setprivate(exports.ld, pass1a(false, result.ptext, YYY.templatesin, [ libname]))
  if passno = 1 
  then p1a 
  else let p = waitforpass2.p1a 
  assert not.aborted.p report message.p 
  result.p

/use process.intercode2

/use seq.intercode2

function subcompilelib(libname:word)seq.word 
 PROFILE.let discard3 = length.mapping.libsymencoding 
  let ld = tolibdesc.libname 
  // if length.modules.ld = 1 ∧ length.src(modules(ld)_1)= 1 
  then interface([ name.ld], exports.ld, dependentlibs.ld)
  else // let b = unloadlib.[ libname]
  let discard5 = loadlibs(dependentlibs.ld, 1, timestamp(libs_1))
  let templatesin = @(asliblib.dependentlibs.ld, identity, emptyliblib, libs)
  let ptext = process.pass0.ld 
  if aborted.ptext 
  then message.ptext 
  else let p1a = setprivate(exports.ld, pass1a(false, result.ptext, YYY.templatesin, [ libname]))
  // let p = waitforpass2.p1a if aborted.p then message.p else let y1 = codegen5.result.p // 
  let intercode =pass2.p1a
  let y1 = codegen5(intercode,libname ,libdesc(p1a,intercode))
  let z2 = createlib(y1, libname, dependentlibs.ld)
  {"OK"}

/function waitforpass2(a:pass1result)process.pass1result 
 NOINLINE.let p = process.pass2.a 
  if aborted.p then p else p

function asliblib(s:seq.word, a:liblib, l:liblib)liblib 
 if libname(l)_1 in s then a + l else a

Function compilelib(libname:word)seq.word 
 let p1 = process.subcompilelib.libname 
  if aborted.p1 
  then"COMPILATION ERROR:"+ space + message.p1 
  else let aa = result.p1 
  if subseq(aa, 1, 1)="OK"
  then aa 
  else"COMPILATION ERROR:"+ space + aa

function loadlibs(dependentlibs:seq.word, i:int, time:int)int 
 if i > length.dependentlibs 
  then time 
  else let stamp = loadlibrary(dependentlibs_i)
  assert stamp ≥ time report"library"+ dependentlibs_i +"is out of date"+ toword.time + toword.stamp 
  loadlibs(dependentlibs, i + 1, stamp)

Function run(libname:word, modname:word, funcname:word)seq.word 
 let aa = compilelib.libname 
  if subseq(aa, 1, 1)="OK"
  then let p2 = process.execute.mangle(funcname, mytype.[ modname], empty:seq.mytype)
   if aborted.p2 then message.p2 else result.p2 
  else aa

function +(a:liblib, b:liblib)liblib liblib(libname.a + libname.b, types.a + types.b, mods.a + mods.b)

function emptyliblib liblib liblib("empty", empty:seq.libtype, empty:seq.libmod)

function YYY(a:liblib)seq.mod2desc 
 let z2 = template(mytype."x$types", empty:seq.syminfo, empty:seq.syminfo, types.a)
  @(+, totemplate, empty:seq.mod2desc, mods.a)+ z2

function totemplate(s:libmod)mod2desc 
 let n = mytype.if parameterized.s then"T"+ modname.s else [ modname.s]
  template(n, toseq.@(+, syminfo, empty:set.syminfo, defines.s), toseq.@(+, syminfo, empty:set.syminfo, exports.s), empty:seq.libtype)

Function newcode(pass1result)seq.syminfo export

Function parsesyminfo(modname:mytype, text:seq.word)syminfo export

