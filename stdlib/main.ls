Module main

use stdlib

use definestruct

use libdescfunc

use codegen

use fileio

use format

use libdesc



use libscope

use pass0

use pass1a

use pass2

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

function loadlibs(dependentlibs:seq.word, i:int, time:int)int 
 if i > length.dependentlibs 
  then time 
  else let stamp = loadlibrary(dependentlibs_i)
  assert stamp ≥ time report"library"+ dependentlibs_i +"is out of date"+ toword.time + toword.stamp 
  loadlibs(dependentlibs, i + 1, stamp)
  
    function gettext2(libname:word, e:seq.word, a:word)seq.seq.seq.word
 @(+, identity, empty:seq.seq.seq.word, groupparagraphs("module Module", gettext.[ merge([ libname]+"/"+ a +".ls")]))

use other

use groupparagraphs

use set.firstpass

use deepcopy.seq.word

function subcompilelib(libname:word)seq.word 
  PROFILE.
 let a = gettext.[ merge( [libname]+"/"+ libname +".ls")]
  let s = findlibclause(a, 1)
  let u = findindex("uses"_1, s, 3)
  let e = findindex("exports"_1, s, 3)
  let dependentlibs = subseq(s, u + 1, e - 1)
  let filelist = subseq(s, 2, min(u - 1, e - 1))
  let exports = subseq(s, e + 1, length.s)
 let b = unloadlib.[libname] 
let discard3 = length.mapping.libsymencoding 
  let discard5 = loadlibs(dependentlibs, 1, timestamp(loadedlibs_1))
  let templatesin = @(asliblib.dependentlibs, identity, emptyliblib, if libname="stdlib"_1 then empty:seq.liblib else loadedlibs)
    let ptext = process.pass0.tolibdesc.libname  
  if aborted.ptext 
  then message.ptext 
  else 
              let r= setprivate(exports,pass1a(false, result.ptext, YYY.templatesin,getlibtypes.mods.templatesin))
    let compiled= @(+, tonewsymbol.alltypes.r, emptysymbolset,  compiled.r) 
   let knownsymbols = @(+, tonewsymbol2.alltypes.r, compiled, newcode.r ) 
  let roots = @(∪, roots.asset.@(+, hasErecord, empty:seq.syminfo, newcode.r), empty:set.word, mods.r)
  let mods=  @(+, tofirstpass, empty:seq.firstpass, mods.r)
  let known2=@(+,todesc.alltypes.r,knownsymbols,toseq.alltypes.r)
   let intercode=pass2(knownsymbols,toseq.roots, compiled)
 //  assert not( libname="test4"_1) report print.intercode //
  // let zz=if libname="stdlib"_1 then 
             let allsrc = @(+, gettext2(s_2, exports), empty:seq.seq.seq.word, filelist)
               let p1=pass1(allsrc,exports,emptysymbolset,asset.empty:seq.firstpass)
              assert false report @(+,mangledname,"",toseq(@(&cup,defines,empty:set.symbol,mods)-@(&cup,defines,empty:set.symbol,mods.p1)) )
             "XX"
           else "" //
  let bc = codegen5(intercode,libname ,liblib([ libname],libdesc(roots,intercode,mods,known2)))
  let z2 = createlib(bc, libname, dependentlibs)
  "OK"

function tonewsymbol2(alltypes:set.libtype,q:syminfo)    symbol
   let p =process.tonewsymbol(alltypes ,q ) 
  assert not.aborted.p report  [mangled.q]+message.p 
   result.p
  
use set.symbol

use process.symbol

use cvttoinst.ls

Function compilelib(libname:word)seq.word 
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
  let discard5 = loadlibs(dependentlibs.ld, 1, timestamp(loadedlibs_1))
  let templatesin = @(asliblib.dependentlibs.ld, identity, emptyliblib, loadedlibs)
  let ptext = process.pass0.ld 
  assert not.aborted.ptext report message.ptext 
   pass1a(true, result.ptext, YYY.templatesin,getlibtypes.mods.templatesin)
   
function getlibtypes(s:seq.libmod) seq.libtype
    toseq.asset.getlibtypes.@(+,defines,empty:seq.libsym,s)

use set.libtype

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

/use process.intercode

/use seq.intercode

use convertlibtyp

use seq.firstpass


Function pass2(r:pass1result) intercode
   let compiled= @(+, tonewsymbol.alltypes.r, emptysymbolset,  compiled.r) 
   let knownsymbols = @(+, tonewsymbol.alltypes.r, compiled, newcode.r ) 
  let roots = toseq.@(∪, roots.asset.@(+, hasErecord, empty:seq.syminfo, newcode.r), empty:set.word, mods.r)
  pass2(knownsymbols,roots, compiled)
  
use buildtree

use newsymbol

use set.word
  
/function waitforpass2(a:pass1result)process.pass1result 
 NOINLINE.let p = process.pass2.a 
  if aborted.p then p else p

function asliblib(s:seq.word, a:liblib, b:liblib)liblib 
 if libname(b)_1 in s then   liblib(libname.a + libname.b,  mods.a + mods.b) else a



Function run(libname:word, modname:word, funcname:word)seq.word 
 let aa = compilelib.libname 
  if subseq(aa, 1, 1)="OK"
  then let p2 = process.execute.mangle(funcname, mytype.[ modname], empty:seq.mytype)
   if aborted.p2 then message.p2 else result.p2 
  else aa


function emptyliblib liblib liblib("empty",  empty:seq.libmod)

function YYY(a:liblib)seq.mod2desc 
  @(+, totemplate, empty:seq.mod2desc, mods.a)

function totemplate(s:libmod)mod2desc 
 let n = mytype.if parameterized.s then"T"+ modname.s else [ modname.s]
  template(n, toseq.@(+, syminfo, empty:set.syminfo, defines.s), toseq.@(+, syminfo, empty:set.syminfo, exports.s), empty:seq.libtype)

Function newcode(pass1result)seq.syminfo export

Function parsesyminfo(modname:mytype, text:seq.word)syminfo export

