module libdescfunc

use blockseq.word

use buildtree

use constant

use graph.word

use libscope

use passcommon

use seq.arc.word

use seq.func

use seq.int

use seq.libmod

use seq.libsym

use seq.mod2desc

use seq.mytype

use seq.syminfo

use set.libsym

use set.libtype

use set.syminfo

use set.word

use stdlib

use tree.word

function roots2(m:mod2desc)set.word 
 if isprivate.m 
  then empty:set.word 
  else @(+, mangled, empty:set.word, toseq.export.m + toseq.defines.m)

function findelement(syms:set.libsym, s:syminfo)seq.libsym 
 findelement(syms, libsym(returntype.s, mangled.s,""))

function map(lib:word, syms:set.libsym, l:mod2desc)seq.libmod 
 if isprivate.l 
  then empty:seq.libmod 
  else if isabstract.modname.l 
  then [ libmod(isabstract.modname.l, abstracttype.modname.l, @(+, tolibsym4, empty:seq.libsym, toseq.defines.l), @(+, tolibsym4, empty:seq.libsym, toseq.export.l), lib)]
  else [ libmod(isabstract.modname.l, abstracttype.modname.l, @(+, findelement.syms, empty:seq.libsym, toseq.defines.l), @(+, findelement.syms, empty:seq.libsym, toseq.export.l), lib)]

function tolibsym4(s:syminfo)libsym 
 decode(encode(libsym(returntype.s, mangled.s, instruction.s), libsymencoding), libsymencoding)

function ?(a:libsym, b:libsym)ordering fsig.a ? fsig.b

function findelement(syms:set.libsym, l:libsym)seq.libsym toseq.findelement(l, syms)

Function libdesc(r:pass1result)liblib 
 let lib = libname(r)_1 
  let funcs = @(+, tolibsym(constantmapping, lib), empty:seq.libsym, code.r)
  let syms = funcs 
  let roots = @(∪, roots2, empty:set.word, mods.r)
  let reach = reachable(newgraph.@(+, findrefarcs, empty:seq.arc.word, syms), toseq.roots)
  let syms2 = @(+, select.reach, empty:seq.libsym, syms)
  let othermod = libmod(false,"$other"_1, syms2, empty:seq.libsym, lib)
  let allmods = @(+, map(lib, asset.syms), empty:seq.libmod, mods.r)+ othermod 
  liblib(libname.r, toseq(@(∪, libtypes.alltypes.r, empty:set.libtype, allmods) - existingtypes.r), allmods)

Function libtypes(s:set.libtype, a:libmod)set.libtype 
 @(∪, libtypes.s, empty:set.libtype, exports.a + defines.a)

function select(s:set.word, l:libsym)seq.libsym 
 if fsig.l in s 
  then if isabstract.modname.tosyminfo.fsig.l then empty:seq.libsym else [ l]
  else empty:seq.libsym

function findrefs(a:seq.word, i:int, result:set.word)set.word 
 if i > length.a 
  then result 
  else if a_i ="USECALL"_1 
  then findrefs(a, i + 1, result)
  else if a_i in"FREF FREFB"
  then findrefs(a, i + 2, result + a_(i + 1))
  else if a_i in"CALL CALLB"then findrefs(a, i + 3, result + a_(i + 2))else findrefs(a, i + 2, result)

function findrefarcs(s:libsym)seq.arc.word 
 @(+, arc.fsig.s, empty:seq.arc.word, toseq.findrefs(instruction.s, 1, empty:set.word))

