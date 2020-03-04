Module libdescfunc


use intercode

use libscope

use otherseq.word


use seq.firstpass

use seq.inst


use seq.libmod

use seq.libsym

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

use symbol


Function libdesc(roots:set.word, intercode:intercode, mods:seq.firstpass, known:symbolset)seq.libmod 
 // assert false report @(seperator([ encodeword.[ 10]]+"---"), print2,"", @(+, filter, empty:seq.symbol, toseq(known)))// 
   let rootindices = asset.@(+, toinstindex(roots, intercode), empty:seq.int, defines.intercode)
  let a = close(intercode, rootindices, rootindices)
  let syms = @(+, tolibsym.intercode, empty:seq.libsym, toseq.a)
  // assert false report check.syms // 
  let allmods = @(map.known, identity, mapresult3(asset.syms, empty:seq.libmod), mods)
   mods.allmods + libmod(false,"$other"_1, toseq.syms.allmods , empty:seq.libsym,empty:seq.mytype)

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
  then let funcnames = if name ="CONSTANT"_1 
    then asset.findcalls(towords.inst, 2,"")
    else asset.[ towords(inst)_2]
   if isempty.funcnames 
   then empty:seq.int 
   else // not all functions appearing in CONSTANT and FREF will have indices in intercode // 
   @(+, toinstindex(funcnames, d), empty:seq.int, arithseq(length.coding.d, 1, 1))
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
   if length.body > 0 then astext5(coding.d, codes(d)_i)+ flags.a else"EXTERNAL"
  [ libsym(returntype.a, mangledname.a, inst)]

type mapresult3 is record syms:set.libsym, mods:seq.libmod

type mapresult32 is record syms:set.libsym, libsyms:seq.libsym

function map(known:symbolset, r:mapresult3, l:firstpass)mapresult3 
 if not.exportmodule.l 
  then r 
  else if isabstract.modname.l 
  then mapresult3(syms.r, mods.r + libmod(true, abstracttype.modname.l, 
          @(+, tolibsym4, empty:seq.libsym, toseq.defines.l), @(+, tolibsym4, empty:seq.libsym, toseq.exports.l),uses.l))
  else 
  let d = @(findelement.known, identity, mapresult32(syms.r, empty:seq.libsym), toseq.exports.l)
  let e = @(findelement.known, identity, mapresult32(syms.d, empty:seq.libsym), toseq.exports.l)
  mapresult3(syms.e, mods.r + libmod(false, abstracttype.modname.l, libsyms.d, libsyms.e,empty:seq.mytype))

function tolibsym4(s:symbol)libsym 
 let src = if length.src.s > 0 ∧ src(s)_1 ="parsedfunc"_1 
   then subseq(src.s, toint(src(s)_2)+ 3, length.src.s)
   else src.s 
  assert not("parsedfunc"_1 in src)report src 
  libsym(resulttype.s, mangledname.s, src)

function findelement(known:symbolset, r:mapresult32, s:symbol)mapresult32 
 let z = findelement(libsym(resulttype.s, mangledname.s,""), syms.r)
  if isempty.z 
  then let t1 = lookupsymbol(known, mangledname.s)
   let t = tolibsym4.t1 
   // assert src.t1 in ["EXTERNAL"]report"ERR33"+ print2.t1 // 
   mapresult32(syms.r + t, libsyms.r + t)
  else mapresult32(syms.r, libsyms.r + z_1)



Function tofirstpass(m:libmod)firstpass 
 firstpass(mytype.if parameterized.m then"T"+ modname.m else [ modname.m], uses.m, @(+, tosymbol, empty:set.symbol, defines.m), @(+, tosymbol, empty:set.symbol, exports.m), empty:seq.symbol, empty:set.symbol, false)

Function tofirstpass(l:liblib)seq.firstpass @(+, tofirstpass, empty:seq.firstpass, mods.l)

