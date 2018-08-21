module libdescfunc

/run newimp test1

use newsymbol

use libscope

use intercode

use cvttoinst

use oseq.word

use other

use seq.firstpass

use seq.inst

use seq.int

use seq.libmod

use seq.libsym

use seq.libtype

use seq.mytype

use seq.seq.int

use seq.symbol

use set.int

use set.libsym

use set.mytype

use set.seq.word

use set.symbol

use set.word

use stdlib

Function libdesc(roots:set.word, intercode:intercode, lib:word, mods:seq.firstpass, known:symbolset)liblib 
 let b = @(∪, gathertypes.known, empty:set.mytype, toseq.roots)
  let c = closetypes(known, @(+, print, empty:set.seq.word, toseq.b), empty:set.seq.word)
  let typesyms = @(+, typelibsyms.known, empty:seq.libsym, toseq.c)
  // assert false report @(+, filterT.known,"", toseq.c)// 
  let rootindices = asset.@(+, toinstindex(roots, intercode), empty:seq.int, defines.intercode)
  let a = close(intercode, rootindices, rootindices)
  let syms = @(+, tolibsym.intercode, empty:seq.libsym, toseq.a)
  let allmods = @(map(lib, known), identity, mapresult(asset.syms, empty:seq.libmod), mods)
  liblib([ lib], empty:seq.libtype, mods.allmods + libmod(false,"$other"_1, toseq.syms.allmods + typesyms, empty:seq.libsym, lib))

@(+, print,"", toseq.asset.@(+, exports, empty:seq.libsym, allmods))

function filterT(known:symbolset, m:seq.word)seq.word 
 {"&br"+ m + print2(known_mangle(merge("sizeoftype:"+ m), mytype."internal", empty:seq.mytype))+"&br"+ m + print2(known_mangle(merge("typedesc:"+ m), mytype."internal", empty:seq.mytype))}

function typelibsyms(known:symbolset, m:seq.word)seq.libsym 
 let sizesym = known_mangle(merge("sizeoftype:"+ m), mytype."internal", empty:seq.mytype)
  let sym = known_mangle(merge("typedesc:"+ m), mytype."internal", empty:seq.mytype)
  if isdefined.sym ∧ isdefined.sizesym 
  then [ tolibsym4.sym, tolibsym4.sizesym]
  else if isdefined.sym 
  then [ tolibsym4.sym]
  else if isdefined.sizesym then [ tolibsym4.sizesym]else empty:seq.libsym

function filterX(known:symbolset, typ:seq.word)seq.seq.word 
 let a = known_mangle(merge("typedesc:"+ typ), mytype."internal", empty:seq.mytype)
  if isdefined.a then [ typ]+ typesused(src.a, 2, 2)else empty:seq.seq.word

function closetypes(known:symbolset, newtypes:set.seq.word, processed:set.seq.word)set.seq.word 
 let a = asset.@(+, filterX.known, empty:seq.seq.word, toseq.newtypes)
  let b = a - processed 
  if isempty.b then processed else closetypes(known, b, processed ∪ b)

function getsubtypes(typ:seq.word)seq.seq.word 
 if length.typ = 1 
  then [ typ]
  else // assert typ in ["seq.int","seq.seq.int","seq.seq.word","seq.word","seq.alphaword"]report typ // 
   [ typ]+ getsubtypes.subseq(typ, 3, length.typ)

function typesused(w:seq.word, i:int, start:int)seq.seq.word 
 if i + 1 > length.w 
  then if start > i then empty:seq.seq.word else getsubtypes.subseq(w, start, i)
  else if w_(i + 1)="."_1 
  then typesused(w, i + 2, start)
  else getsubtypes.subseq(w, start, i)+ typesused(w, i + 1, i + 1)

function gathertypes(known:symbolset, mangledname:word)set.mytype 
 let sym = known_mangledname 
  @(+, replaceT.parameter.modname.sym, asset.[ resulttype.sym], paratypes.sym)

let a = @(∪, gathertypes, empty:set.mytype, roots)@(+, print,"", toseq.a)

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
  if name in"SET WORD WORDS DEFINE LOCAL LIT PARAM IDXUC LIT ELSEBLOCK RECORD THENBLOCK if CONTINUE LOOPBLOCK FINISHLOOP FIRSTVAR"
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
  else if f_1 in"SET WORD WORDS LOCAL LIT PARAM RECORD FREF"
  then f 
  else [ f_1]

function astext5(s:seq.inst, d:seq.int)seq.word @(+, astext.s,"", d)

function tolibsym(d:intercode, i:int)seq.libsym 
 let a = coding(d)_i 
  if mangledname.a in"CONSTANT EQL RECORD"∨"builtin"_1 in flags.a 
  then empty:seq.libsym 
  else let inst = if"STATE"_1 in flags.a 
   then [ mangledname.a,"STATE"_1,"EXTERNAL"_1]
   else let body = simpleonly(d, i)
   if length.body > 0 
   then  astext5(coding.d, codes(d)_i)+ flags.a 
   else"EXTERNAL"
  [ libsym(returntype.a, mangledname.a, inst)]

type mapresult is record syms:set.libsym, mods:seq.libmod

type mapresult2 is record syms:set.libsym, libsyms:seq.libsym

function map(lib:word, known:symbolset, r:mapresult, l:firstpass)mapresult 
 if not.exportmodule.l 
  then r 
  else if isabstract.modname.l 
  then mapresult(syms.r, mods.r + libmod(true, abstracttype.modname.l, @(+, tolibsym4, empty:seq.libsym, toseq.defines.l), @(+, tolibsym4, empty:seq.libsym, toseq.exports.l), lib))
  else let e = @(findelement.known, identity, mapresult2(syms.r, empty:seq.libsym), toseq.exports.l)
  mapresult(syms.e, mods.r + libmod(false, abstracttype.modname.l, empty:seq.libsym, libsyms.e, lib))

function tolibsym4(s:symbol)libsym libsym(resulttype.s, mangledname.s, src.s)

function findelement(syms:set.libsym, s:symbol)seq.libsym 
 toseq.findelement(libsym(resulttype.s, mangledname.s,""), syms)

function findelement(known:symbolset, r:mapresult2, s:symbol)mapresult2 
 // assert not.iscomplex.modname.s ∨ mangledname.s in"Q3CZrealzseqZTZT inZintzseqZTZTzseq inZwordzseqzseqZTZTzseq inZwordzseqZTZTzseq"report"MMM"+ print2.s // 
  let z = findelement(libsym(resulttype.s, mangledname.s,""), syms.r)
  if isempty.z 
  then let t1 = known_mangledname.s 
   let t = tolibsym4.t1 
   assert src.t1 in ["EXTERNAL"]report "ERR33"+ print2.t1 
   mapresult2(syms.r + t, libsyms.r + t)
  else // assert not.iscomplex.modname.s report"ERR11"+ fsig.z_1 + returntype.z_1 + instruction.z_1 // 
  // let toadd = if iscomplex.modname.s then libsym(mytype.returntype.z_1, mangle(name.s, modname.s, @(+, replaceT.modname.s, empty:seq.mytype, paratypes.s)), instruction.z_1)else z_1 // 
  mapresult2(syms.r, libsyms.r + z_1)

function ?(a:libsym, b:libsym)ordering fsig.a ? fsig.b

/type libsym is record fsig:word, returntype:seq.word, instruction:seq.word

Function tosymbol(ls:libsym)symbol 
 let d = codedown.fsig.ls 
  let modname = mytype(d_2)
  let paratypes = @(+, mytype, empty:seq.mytype, subseq(d, 3, length.d))
  symbol(mangle(d_1_1, modname, paratypes), mytype.returntype.ls, @(+, replaceT.parameter.modname, empty:seq.mytype, paratypes), d_1_1, modname, instruction.ls)

Function tofirstpass(m:libmod)firstpass 
 firstpass(mytype.if parameterized.m then"T"+ modname.m else [ modname.m], empty:seq.mytype, @(+, tosymbol, empty:set.symbol, defines.m), @(+, tosymbol, empty:set.symbol, exports.m), empty:seq.symbol, empty:set.symbol, false)

Function tofirstpass(l:liblib)seq.firstpass @(+, tofirstpass, empty:seq.firstpass, mods.l)

/type liblib is record libname:seq.word, types:seq.libtype, mods:seq.libmod, timestamp:int, readonly:boolean /type libmod is record parameterized:boolean, modname:word, defines:seq.libsym, exports:seq.libsym, library:word /type firstpass is record modname:mytype, uses:seq.mytype, defines:set.symbol, exports:set.symbol, unboundexports:seq.symbol, unbound:set.symbol, exportmodule:boolean

