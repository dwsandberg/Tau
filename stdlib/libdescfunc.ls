module libdescfunc

use libscope

use oseq.word

use passcommon

use seq.inst

use seq.int

use seq.libmod

use seq.libsym

use seq.libtype

use seq.mod2desc

use seq.mytype

use seq.seq.int

use seq.syminfo

use set.int

use set.libsym

use set.libtype

use set.syminfo

use set.word

use stdlib

/use set.mytype



function roots2(m:mod2desc)set.word 
 if isprivate.m then empty:set.word else @(+, mangled, empty:set.word, toseq.export.m)


Function libdesc(r:pass1result,intercode:intercode)liblib 
 let roots = @(∪, roots2, empty:set.word, mods.r)
   libdesc(roots,intercode,libname(r)_1, mods.r,alltypes.r,existingtypes.r)
 
Function libdesc(roots:set.word,intercode:intercode,lib:word,mods:seq.mod2desc,
alltypes:set.libtype,existingtypes:set.libtype) liblib
  let rootindices = asset.@(+, toinstindex(roots, intercode), empty:seq.int, defines.intercode)
  let a = close(intercode, rootindices, rootindices)
  let syms = @(+, tolibsym(intercode), empty:seq.libsym, toseq.a)
  let othermod = libmod(false,"$other"_1, syms, empty:seq.libsym, lib)
  let allmods = @(+, map(lib, asset.syms), empty:seq.libmod, mods)+ othermod 
  liblib([lib], toseq(@(∪, libtypes.alltypes, empty:set.libtype, allmods) - existingtypes), allmods)

function toinstindex(a:set.word, d:intercode, i:int)seq.int 
 if mangledname(coding(d)_i)in a then [ i]else empty:seq.int

function close(d:intercode, toprocess:set.int, old:set.int)set.int 
 let a = asset.@(+, simpleonly.d, empty:seq.int, toseq.toprocess) - old 
  let new = asset.@(+, filter.d, empty:seq.int, toseq.a) - old 
  if isempty.new then old else close(d, new, old ∪ new)

function simpleonly(d:intercode, i:int)seq.int 
 // returns body for simple function otherwise and empty sequence // 
  let body = codes(d)_i 
  if length.body > 30 
  then empty:seq.int 
  else let flags = flags(coding(d)_i)
  if"SIMPLE"_1 in flags ∨"INLINE"_1 in flags 
  then body 
  else empty:seq.int

function filter(d:intercode, i:int)seq.int 
 let inst = coding(d)_i 
  let name = mangledname.inst 
  if name in"SET WORD WORDS DEFINE LOCAL LIT PARAM IDXUC LIT ELSEBLOCK RECORD THENBLOCK if"
  then empty:seq.int 
  else if name in"CONSTANT FREF"
  then let a = if name ="CONSTANT"_1 
    then asset.findcalls(towords.inst, 2,"")
    else asset.[ towords(inst)_2]
   if isempty.a 
   then empty:seq.int 
   else let result = @(+, toinstindex(a, d), empty:seq.int, arithseq(length.coding.d, 1, 1))
   assert length.toseq.a = length.result report"Did not find all function embedded in CONSTANT"+ toseq.a 
   result 
  else [ i]

function findcalls(a:seq.word, i:int, result:seq.word)seq.word 
 if i > length.a 
  then result 
  else findcalls(a, i + 2, result + if a_i ="FREF"_1 then [ a_(i + 1)]else"")

function astext(s:seq.inst, i:int)seq.word 
 let f = towords(s_i)
  if f_1 ="CONSTANT"_1 
  then subseq(f, 2, length.f)
  else if f_1 ="PARAM"_1 
  then"PARAM"+ toword(-toint(f_2) - 1)
  else if f_1 in"ELSEBLOCK THENBLOCK DEFINE"
  then""
  else f

function astext5(s:seq.inst, d:seq.int)seq.word @(+, astext.s,"", d)

function tolibsym(d:intercode, i:int)seq.libsym 
  let a = coding(d)_i 
  if mangledname.a in"CONSTANT EQL RECORD"∨"builtin"_1 in flags.a 
  then empty:seq.libsym 
  else let inst = if"STATE"_1 in flags.a 
   then [ mangledname.a, toword.nopara.a,"STATE"_1,"1"_1]
   else let body = simpleonly(d, i)
  if length.body > 0 
  then  "USECALL"+ astext5(coding.d, codes(d)_i)
    else [ mangledname.a, toword.nopara.a]
  [ libsym(returntype.a, mangledname.a, inst)]
  

function map(lib:word, syms:set.libsym, l:mod2desc)seq.libmod 
 if isprivate.l 
  then empty:seq.libmod 
  else if isabstract.modname.l 
  then [ libmod(isabstract.modname.l, abstracttype.modname.l, @(+, tolibsym4, empty:seq.libsym, toseq.defines.l), @(+, tolibsym4, empty:seq.libsym, toseq.export.l), lib)]
  else [ libmod(isabstract.modname.l, abstracttype.modname.l, @(+, findelement.syms, empty:seq.libsym, toseq.defines.l), @(+, findelement.syms, empty:seq.libsym, toseq.export.l), lib)]

function tolibsym4(s:syminfo)libsym 
 decode(encode(libsym(returntype.s, mangled.s, instruction.s), libsymencoding), libsymencoding)

function ?(a:libsym, b:libsym)ordering fsig.a ? fsig.b

function findelement(syms:set.libsym, s:syminfo)seq.libsym 
 toseq.findelement(libsym(returntype.s, mangled.s,""), syms)

Function libtypes(s:set.libtype, a:libmod)set.libtype 
 @(∪, libtypes.s, empty:set.libtype, exports.a + defines.a)

