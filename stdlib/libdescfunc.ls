Module libdescfunc

use cvttoinst

use intercode

use libscope

use oseq.word

use pass1

use seq.firstpass

use seq.inst

use seq.int

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

/function print2(l:libsym)seq.word print.l + instruction.l

Function libdesc(roots:set.word, intercode:intercode, mods:seq.firstpass, known:symbolset)seq.libmod 
 // assert false report @(seperator([ encodeword.[ 10]]+"---"), print2,"", @(+, filter, empty:seq.symbol, toseq(known)))// 
  let b = @(∪, gathertypes.known, empty:set.mytype, toseq.roots)
  let c = closetypes(known, @(+, print, empty:set.seq.word, toseq.b), empty:set.seq.word)
  // assert false report @(seperator(","), identity,"", toseq.c)// 
  let typesyms = @(+, typelibsyms.known, empty:seq.libsym, toseq.c)
  // assert false report @(seperator."&br", print2,"", typesyms)// 
  let rootindices = asset.@(+, toinstindex(roots, intercode), empty:seq.int, defines.intercode)
  let a = close(intercode, rootindices, rootindices)
  let syms = @(+, tolibsym.intercode, empty:seq.libsym, toseq.a)
  // assert false report check.syms // 
  let allmods = @(map.known, identity, mapresult3(asset.syms, empty:seq.libmod), mods)
  assert true report // @(+, print,"", toseq.syms.allmods)// 
   @(+, print,"", toseq.asset.@(+, usestypes, empty:seq.mytype, toseq.syms.allmods))
  mods.allmods + libmod(false,"$other"_1, toseq.syms.allmods + typesyms, empty:seq.libsym)

/function check(syms:seq.libsym)seq.word let x = findelement(libsym(mytype."X","wordencodingZstdlib"_1,""), syms)assert length.x = 1 report"??""CODE"+ instruction.x_1

/function filter(s:symbol)seq.symbol if subseq(src.s, 1, 2)="record erecord"then [ s]else empty:seq.symbol

/if"LIT"_1 in src.s &or"FREF"_1 in src.s then empty:seq.symbol else [ s]

function usestypes(s:libsym)seq.mytype 
 let d = codedown.fsig.s 
  let x = @(+, mytype, [ mytype.returntype.s], subseq(d, 3, length.d))
  @(+, primtypes, empty:seq.mytype, x)

function primtypes(m:mytype)seq.mytype 
 let s = towords.m 
  if length.s = 1 
  then [ m]
  else @(+, mytype, empty:seq.mytype, @(+, +."T", [ [ s_1]], subseq(s, 2, length.s)))
  
  

function typelibsyms(known:symbolset, m:seq.word)seq.libsym 
 let sym = lookuptypedesc2(known,  m)
  if isdefined.sym 
  then [ tolibsym4.sym]
  else   empty:seq.libsym

function filterX(known:symbolset, typ:seq.word)seq.seq.word 
 if typ_1 ="erecord"_1 
  then // erecord contains funky types so do not look in up // 
   assert length.typ > 2 report"JKL"+ typ 
   [ subseq(typ, 3, length.typ)]
  else let d = lookuptypedesc2(known,  typ)
  let src = src.d 
  // assert length(src)= 0 &or(src)_1 in"WORDS record"report typ +"XX"+ print2.d // 
  if length.src = 0 ∨ not(src_1 in"WORDS record")
  then [ typ]
  else [ typ]+ @(+, getsubtypes.1, empty:seq.seq.word, componenttypes(src, 1, empty:seq.seq.word,""))

function getsubtypes(i:int, typ:seq.word)seq.seq.word 
 // converts"int seq stack seq"to ["int","seq.int","stack.seq.int","seq.stack.seq.int"// 
  if i > length.typ then empty:seq.seq.word else [ print.mytype.subseq(typ, 1, i)]+ getsubtypes(i + 1, typ)

function componenttypes(s:seq.word, i:int, types:seq.seq.word, part:seq.word)seq.seq.word 
 if i ≥ length.s 
  then if s_1 in"WORDS"then types +([ s_i]+ part)else types 
  else if s_1 in"sequence record"
  then // example format sequence cseq 2 T seq 2 int len 2 T element // 
   if i = 1 
   then componenttypes(s, 2, types, part)
   else let typelen = toint(s_(i + 1))
   componenttypes(s, i + 1 + typelen, types + subseq(s, i + 2, i + 2 + typelen - 1), part)
  else if i = 1 
  then componenttypes(s, 4, types, part)
  else // example format WORDS 7 2 seq.libsym seq.libmod // 
  assert s_1 in"WORDS"report"unexpected type format"
  if s_(i + 1)="."_1 
  then componenttypes(s, i + 2, types, [ s_i]+ part)
  else componenttypes(s, i + 1, types +([ s_i]+ part),"")

function closetypes(known:symbolset, newtypes:set.seq.word, processed:set.seq.word)set.seq.word 
 let a = asset.@(+, filterX.known, empty:seq.seq.word, toseq.newtypes)
  let b = a - processed 
  if isempty.b then processed else closetypes(known, b, processed ∪ b)

function gathertypes(known:symbolset, mangledname:word)set.mytype 
 let sym = lookupsymbol(known, mangledname)
  let x = @(+, replaceT.parameter.modname.sym, asset.[ resulttype.sym], paratypes.sym)
  let z = @(seperator.",", towords,"", toseq.x)
  x

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
  then mapresult3(syms.r, mods.r + libmod(true, abstracttype.modname.l, @(+, tolibsym4, empty:seq.libsym, toseq.defines.l), @(+, tolibsym4, empty:seq.libsym, toseq.exports.l)))
  else let d = @(findelement.known, identity, mapresult32(syms.r, empty:seq.libsym), toseq.exports.l)
  let e = @(findelement.known, identity, mapresult32(syms.d, empty:seq.libsym), toseq.exports.l)
  mapresult3(syms.e, mods.r + libmod(false, abstracttype.modname.l, libsyms.d, libsyms.e))

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

/function ?(a:libsym, b:libsym)ordering fsig.a ? fsig.b

Function tosymbol(ls:libsym)symbol 
 let d = codedown.fsig.ls 
  let modname = mytype(d_2)
  let paratypes = @(+, mytype, empty:seq.mytype, subseq(d, 3, length.d))
  symbol(mangle(d_1_1, modname, paratypes), mytype.returntype.ls, @(+, replaceT.parameter.modname, empty:seq.mytype, paratypes), d_1_1, modname, instruction.ls)

Function tofirstpass(m:libmod)firstpass 
 firstpass(mytype.if parameterized.m then"T"+ modname.m else [ modname.m], empty:seq.mytype, @(+, tosymbol, empty:set.symbol, defines.m), @(+, tosymbol, empty:set.symbol, exports.m), empty:seq.symbol, empty:set.symbol, false)

Function tofirstpass(l:liblib)seq.firstpass @(+, tofirstpass, empty:seq.firstpass, mods.l)

