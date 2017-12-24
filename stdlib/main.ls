Module main

use codegen2

use constant

use fileresult

use format

use libdesc

use libscope

use options.seq.word

use pass0

use pass1a

use pass2a

use passcommon

use persistant2

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

use seq.seq.seq.word

use seq.syminfo

use set.mod2desc

use set.syminfo

use stdlib

Function main(arg:seq.int)int 
 let args = towords(arg + 10 + 10)
  let libname = args_1 
  // create non empty changed file to force compiling of library // 
  let discard2 = createfile([ merge([ libname]+"/changed")], ["library src has been changed"])
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
  let z = createfile("test.html", [ htmlheader + processpara.output])
  0

Function loadlibrary(libname:word)int loadlib([ libname], 0)

Function bindings(libname:word)pass1result 
 let discard3 = length.mapping.libsymencoding + length.constantmapping 
  let ld = tolibdesc.libname 
  // let b = unloadlib.[ libname]// 
  let discard5 = loadlibs(dependentlibs.ld, 1, timestamp(libs_1))
  let templatesin = @(asliblib.dependentlibs.ld, identity, emptyliblib, libs)
  let ptext = process.pass0.ld 
  assert not.aborted.ptext report message.ptext 
  pass1a(true, result.ptext, YYY.templatesin, [ libname])

Function pass(passno:int,libname:word) pass1result
   let ld = tolibdesc.libname 
  // let b = unloadlib.[ libname]// 
  let discard5 = loadlibs(dependentlibs.ld, 1, timestamp(libs_1))
  let templatesin = @(asliblib.dependentlibs.ld, identity, emptyliblib, libs)
  let ptext = process.pass0.ld 
  assert not.aborted.ptext report message.ptext 
  let p1a = pass1a(false, result.ptext, YYY.templatesin, [ libname])
  if passno=1 then p1a
  else 
  let p = waitforpass2.setprivate(exports.ld, p1a)
  assert not.aborted.p report message.p
    result.p


function subcompilelib(libname:word)seq.word 
 PROFILE.let discard3 = length.mapping.libsymencoding + length.constantmapping 
  let ld = tolibdesc.libname 
  if length.modules.ld = 1 ∧ length.src(modules(ld)_1)= 1 
  then interface([ name.ld], exports.ld, dependentlibs.ld)
  else if not.checklibchange.libname 
  then let discard = loadlibs(dependentlibs.ld, 1, timestamp(libs_1))
   let discard2 = loadlibrary.libname 
   {"OK"} 
  else let b = unloadlib.[ libname]
  let discard5 = loadlibs(dependentlibs.ld, 1, timestamp(libs_1))
  let templatesin = @(asliblib.dependentlibs.ld, identity, emptyliblib, libs)
  let ptext = process.pass0.ld 
  if aborted.ptext 
  then message.ptext 
  else let p1a = pass1a(false, result.ptext, YYY.templatesin, [ libname])
  let p = waitforpass2.setprivate(exports.ld, p1a)
  if aborted.p 
  then message.p 
  else let y1 = codegen5.result.p 
  let z2 = createlib(y1, libname, dependentlibs.ld)
  let discard4 = createfile([ merge([ libname]+"/changed")], [""])
  {"OK"}
  
function waitforpass2(a:pass1result) process.pass1result
PROFILE.let p = process.pass2.a
  if aborted.p then p else p 
  
use options.process.pass1result


use codegen2

function asliblib(s:seq.word, a:liblib, l:liblib)liblib 
 if libname(l)_1 in s then a + l else a

Function compilelib(libname:word)seq.word 
  PROFILE.let p1 = process.subcompilelib.libname 
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

function checklibchange(libname:word)boolean 
 let n = [ merge([ libname]+"/changed")]
  fileexists.n ∧ length.getfile.n > 3

Function run(libname:word, modname:word, funcname:word)seq.word 
 let aa = compilelib.libname 
  if subseq(aa, 1, 1)="OK"
  then let p2 = process.execute.mangle(funcname, mytype.[ modname], empty:seq.mytype)
   if aborted.p2 then message.p2 else result.p2 
  else aa

/Function reverse(s:seq.seq.word)seq.seq.word @(+,_.s, empty:seq.seq.word, arithseq(length.s, 0-1, length.s))

function +(a:liblib, b:liblib)liblib liblib(libname.a + libname.b, types.a + types.b, mods.a + mods.b)

Function emptyliblib liblib liblib("empty", empty:seq.libtype, empty:seq.libmod)

Function YYY(a:liblib)seq.mod2desc 
 let z2 = template(mytype."x$types", empty:seq.syminfo, empty:seq.syminfo, types.a)
  @(+, totemplate, empty:seq.mod2desc, mods.a)+ z2

function totemplate(s:libmod)mod2desc 
 let n = mytype.if parameterized.s then"T"+ modname.s else [ modname.s]
  template(n, toseq.@(+, syminfo, empty:set.syminfo, defines.s), toseq.@(+, syminfo, empty:set.syminfo, exports.s), empty:seq.libtype)

Function newcode(pass1result)seq.syminfo export

