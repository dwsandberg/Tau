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

function astext(nopara:int, s:seq.inst, i:int)seq.word 
 let f = towords(s_i)
  if f_1 ="CONSTANT"_1 
  then subseq(f, 2, length.f)
  else if f_1 ="PARAM"_1 then"PARA"+ toword(toint(f_2)+ nopara + 2)else f

function astext5(nopara:int, s:seq.inst, d:seq.int)seq.word @(+, astext(nopara, s),"", d)

function tolibsym(coding:seq.inst, codes:seq.seq.int, i:int)seq.libsym 
 // Converting func to lib symbol.In the libsym, if the inst field begins with"USECALL"then the rest of inst the intermediate representation. Otherwise the inst is the code that should be added after the parameters. For example ;"USECALL PARA 2 PARA 1 ADD 2"and"ADD 2"are equivalent representations of a function.// 
  let a = coding_i 
  if mangledname.a in"CONSTANT EQL RECORD"∨"builtin"_1 in flags.a 
  then empty:seq.libsym 
  else let inst = if"STATE"_1 in flags.a 
   then [ mangledname.a, toword.nopara.a,"STATE"_1,"1"_1]
   else if"SIMPLE"_1 in flags.a 
   then let nopara = nopara.a 
    let x = astext5(nopara, coding, codes_i)
    let verysimple = nopara = 0 ∨ nopara = 1 ∧ subseq(x, 1, 2)="PARA 1"∨ nopara = 2 ∧ subseq(x, 1, 4)="PARA 2 PARA 1"∨ nopara = 3 ∧ subseq(x, 1, 6)="PARA 3 PARA 2 PARA 1"∨ nopara = 4 ∧ subseq(x, 1, 8)="PARA 4 PARA 3 PARA 2 PARA 1"
    if verysimple ∧ not("PARA"_1 in subseq(x, nopara * 2 + 1, length.x))∧ not("SET"_1 in x)
    then subseq(x, nopara * 2 + 1, length.x)
    else"USECALL"+ x 
   else if"INLINE"_1 in flags.a ∧ length(codes_i)< 10 
   then"USECALL"+ astext5(nopara.a, coding, codes_i)
   else [ mangledname.a, toword.nopara.a]
  [ libsym(returntype.a, mangledname.a, inst)]

function roots2(m:mod2desc)set.word 
 if isprivate.m then empty:set.word else @(+, mangled, empty:set.word, toseq.export.m)

function toinstindex(a:set.word, d:intercode, i:int)seq.int 
 if mangledname(coding(d)_i)in a then [ i]else empty:seq.int

Function libdesc(r:pass1result,intercode:intercode)liblib 
 let roots = @(∪, roots2, empty:set.word, mods.r)
  let rootindices = asset.@(+, toinstindex(roots, intercode), empty:seq.int, defines.intercode)
  let a = close(intercode, rootindices, rootindices)
  let syms = @(+, tolibsym(coding.intercode, codes.intercode), empty:seq.libsym, toseq.a)
  let lib = libname(r)_1 
  let othermod = libmod(false,"$other"_1, syms, empty:seq.libsym, lib)
  let allmods = @(+, map(lib, asset.syms), empty:seq.libmod, mods.r)+ othermod 
  liblib(libname.r, toseq(@(∪, libtypes.alltypes.r, empty:set.libtype, allmods) - existingtypes.r), allmods)

function simpleonly(d:intercode, i:int)seq.int 
 let inst = coding(d)_i 
  if"SIMPLE"_1 in flags.inst then codes(d)_i else empty:seq.int

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

function close(d:intercode, toprocess:set.int, old:set.int)set.int 
 let a = asset.@(+, simpleonly.d, empty:seq.int, toseq.toprocess) - old 
  let new = asset.@(+, filter.d, empty:seq.int, toseq.a) - old 
  if isempty.new then old else close(d, new, old ∪ new)

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

