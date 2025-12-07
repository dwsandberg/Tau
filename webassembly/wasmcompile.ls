Module wasmcompile

use objectio.addrsym

use seq.addrsym

use bits

use seq1.blkele

use stack.blkele

use seq.byte

use process.seq.byte

use seq.seq.byte

use seq.char

use encoding.coverage

use file

use funcidx

use knownWfunc

use seq1.localinfo

use sort.localinfo

use set.localmap

use seq1.mytype

use printfunc

use standard

use seq.symbol

use symbol1

use set.symdef

use wasm

use wasm2

use encoding.wfunc

use seq.wfunc

use seq1.word

use set.seq.word

use seq1.wtype

use stack.wtype

type coverage is towfunc:seq.word

function =(a:coverage, b:coverage) boolean towfunc.a = towfunc.b

function hash(a:coverage) int hash.towfunc.a

function reportcoverage(knownfuncs:seq.wfunc) seq.word
let a =
 for acc = empty:set.seq.word, f ∈ knownfuncs do acc + %.sym.f,
 acc
let b =
 for acc = empty:set.seq.word, p ∈ encodingdata:coverage do acc + towfunc.p,
 acc
for txt = "", l ∈ toseq(a \ b) do txt + l + "/br",
txt

function jsname(sym:symbol) seq.word "exports." + name.sym

Function wasmcompile(
alltypes:typedict
, prg4:set.symdef
, roots:seq.symbol
, outname:filename
, imports:seq.symbol
, info:boolean
, initprofile:seq.symbol
, libname:word
) seq.file
let discard68 = encode.coverage."???"
let discard67 = startencodings
let imp =
 for acc = empty:seq.seq.byte, @e ∈ imports
 do
  let discard = addf(alltypes, @e, empty:seq.byte),
  acc + importfunc(typeidx64(alltypes, @e), "imports" sub 1, wordname.@e),
 acc
let knownfuncs = knownWfunc(alltypes, libname)
{create functions that will be exported}
let exp =
 for acc = empty:seq.seq.byte, @e ∈ roots do acc + exportfunc(funcidx.@e, last.jsname.@e),
 acc
{define functions with hand coded webassembly definitions}
let discard100 =
 [
  processbodyfunc.alltypes
  , handleerrorfunc(alltypes, libname)
  , reclaimspacefunc.alltypes
  , allocatefunc.alltypes
  , addencodingfunc.alltypes
  , set2zero.alltypes
  , addf(
   alltypes
   , symbol(internalmod, "profiledata", typeptr)
   , funcbody(
    [i32]
    , if isempty.initprofile then const64.getoffset("", libname) + return
    else
     const64.3
     + Wcall.allocatesym
     + localtee
     + LEBu.0
     + const64.0
     + Wstore(typeint, 0)
     + Wlocal.0
     + const64.1
     + Wstore(typeint, 8)
     + Wlocal.0
     + Wcall.symbol(moduleref."* initialize", "profileData", typeptr)
     + Wstore(typeint, 16)
     + Wlocal.0
     + i64extendi32u
     + return
   )
  )
  , addf(
   alltypes
   , symbol(internalmod, "addresssymbols", typeptr)
   , funcbody(
    [i64]
    , if isempty.initprofile then const64.getoffset("", libname) + return
    else
     Wcall.symbol(internalmod, "vector2", seqof.typebyte)
     + Wcall.symbol(moduleref."* webProfileSupport", "decodeaddrsym", [seqof.typebyte], typeptr)
     + return
   )
  )
 ]
{define depended functions}
let discardt = dependentfunc(alltypes, knownfuncs, prg4, n.imports + 1, libname)
let elements =
 for acc = empty:seq.addrsym, p ∈ elementdata
 do acc + addrsym(n.acc + 2, funcidx2symbol(p + 1)),
 topackedbyteobject.outbytes:addrsym(acc)
let discardff =
 addf(
  alltypes
  , symbol(internalmod, "vector2", seqof.typebyte)
  , funcbody([i64], const64.allocateconstspace("." sub 1, elements) + return)
 )
{define function to initialize words}
let startfuncidx = funcidx.symbol(moduleref."* core", "initwords3", typeint)
let mustbedonelast =
 addf(
  alltypes
  , symbol(moduleref."* core", "initwords3", typeint)
  , initwordsbody(initprofile, libname)
 )
{create the wasm file}
assert startfuncidx < n.encodingdata:wfunc report "internal error:startfuncidx exceeds number of functions",
createwasm(imp, exp + exportmemory."memory" sub 1, dataseg, startfuncidx, outname, info)

function topackedbyteobject(x:seq.byte) seq.int
for acc = [1, n.x], acc2 = 0x0, shift = 0, b ∈ x
do
 let newacc2 = acc2 ∨ bits.toint.b << shift,
 if shift = 56 then next(acc + toint.newacc2, 0x0, 0)
 else next(acc, newacc2, shift + 8),
if shift > 0 then acc + toint.acc2 else acc

function dependentfunc(
alltypes:typedict
, knownfuncs:seq.wfunc
, prg:set.symdef
, idx:int
, libname:word
) int
{Do not consider function indices less that idx /br
get the symbols of functions that has been referenced but do not have a definition}
let k = nobodies.idx,
if isempty.k then {no functions that do not have definitions}0
else
 for notused = to:encoding.wfunc(1), sym ∈ k
 do
  if name.module.sym ∈ "$$sequence" then seqsymdef(alltypes, sym)
  else if name.module.sym ∈ "$$record" then recordsymdef(alltypes, sym)
  else
   let code = getCode(prg, sym),
   if isempty.code then
    let ele = lookup(knownfuncs, wfunc(alltypes, sym, empty:seq.byte)),
    if isempty.ele ∧ module.sym = internalmod ∧ name.sym ∉ "set" then
     if name.sym ∈ "vector2 addresssymbols" then notused
     else
      let c = decodeword.name.sym
      let d = decodeword."processX" sub 1
      assert subseq(c, 1, n.d) = d report "HHHX:(sym)",
      let typeidx = toint.encodeword(c << n.d),
      encode.wfunc(alltypes, sym, processXbody.typeidx, funcidx.sym)
    else
     assert not.isempty.ele report "dependentfunc:no definition for::(sym):::" + name.sym
     let bodycode =
      if isempty.ele then const64.0
      else
       let discard2 = encode.coverage.%.sym.ele sub 1
       for code2 = empty:seq.byte, j ∈ arithseq(nopara.sym, 1, 0) do code2 + Wlocal.j,
       code2 + code.ele sub 1,
     encode.wfunc(alltypes, sym, funcbody(empty:seq.wtype, bodycode + return), funcidx.sym)
   else
    let p1 = process.generatefuncbody(alltypes, knownfuncs, code, sym, libname)
    assert not.aborted.p1 report "generatefuncbody error for::(library.module.sym)::(sym)/br:(code)/br:(message.p1):(stacktrace)",
    encode.wfunc(alltypes, sym, result.p1, funcidx.sym),
 dependentfunc(alltypes, knownfuncs, prg, idx + n.k, libname)

type localinfo is type:wtype, leb:seq.byte, no:int

type localmap is name:word, localinfo:localinfo

Export type:localmap

function >1(a:localmap, b:localmap) ordering name.a >1 name.b

function getlocalinfo(a:set.localmap, w:word) localinfo
let t = lookup(a, localmap(w, localinfo(f64, empty:seq.byte, 0)))
assert not.isempty.t report "unknown local" + w + stacktrace,
localinfo.t sub 1

function >1(a:localinfo, b:localinfo) ordering no.a >1 no.b

function addlocal(map:set.localmap, name:word, type:wtype) set.localmap
let no = n.map,
map + localmap(name, localinfo(type, LEBu.no, no))

function Wlocal(l:localinfo) seq.byte [localget] + leb.l

function Wdefine(l:localinfo) seq.byte [localset] + leb.l

function Wtee(l:localinfo) seq.byte [localtee] + leb.l

type blkele is code:seq.byte, sym:symbol

function generatefuncbody(
alltypes:typedict
, knownfuncs:seq.wfunc
, code:seq.symbol
, forsym:symbol
, libname:word
) seq.byte
let localmap =
 for acc = empty:set.localmap, @e ∈ paratypes.forsym
 do addlocal(acc, toword(n.acc + 1), wtype64(alltypes, @e)),
 acc
for
 lastfref = Lit.0
 , last = Lit.0
 , typestk = empty:stack.wtype
 , blkstk = empty:stack.blkele
 , curblk = empty:seq.byte
 , localtypes = localmap
 , sym ∈ code
do
 let kind = kind.sym,
 if kind = klocal then
  let t = getlocalinfo(localtypes, wordname.sym),
  next(last, sym, push(typestk, type.t), blkstk, curblk + Wlocal.t, localtypes)
 else if kind = kconstantrecord then
  let this = const64.getoffset(sym, libname),
  next(last, sym, push(typestk, i64), blkstk, curblk + this, localtypes)
 else if kind = kreal then
  let val = bits.value.sym
  let this =
   for acc = [f64const], @i = 1, @e ∈ constantseq(8, 0)
   do next(acc + tobyte(val >> (8 * @i - 8) ∧ bits.255), @i + 1),
   acc,
  next(last, sym, push(typestk, f64), blkstk, curblk + this, localtypes)
 else if kind = kfref then
  let newcode = const64.tableindex.basesym.sym,
  next(last, sym, push(typestk, i64), blkstk, curblk + newcode, localtypes)
 else if kind = ktrue then next(last, sym, push(typestk, i32), blkstk, curblk + const32.1, localtypes)
 else if kind = kfalse then next(last, sym, push(typestk, i32), blkstk, curblk + const32.0, localtypes)
 else if kind = kword then
  next(
   last
   , sym
   , push(typestk, i64)
   , blkstk
   , curblk + const64.value.wordconst.wordname.sym
   , localtypes
  )
 else if kind = kwords then
  next(
   last
   , sym
   , push(typestk, i64)
   , blkstk
   , curblk + const64.getoffset(worddata.sym, libname)
   , localtypes
  )
 else if kind = kint then
  let this = [i64const] + LEBs.value.sym,
  next(last, sym, push(typestk, i64), blkstk, curblk + this, localtypes)
 else if kind = kloop then
  let locals =
   for acc = localtypes, varno = firstvar.sym, t ∈ paratypes.sym
   do next(addlocal(acc, toword.varno, wtype64(alltypes, t)), varno + 1),
   acc,
  next(
   last
   , sym
   , push(pop(typestk, nopara.sym), wtype64(alltypes, resulttype.sym))
   , push(blkstk, blkele(curblk, sym))
   , empty:seq.byte
   , locals
  )
 else if kind = ksequence then
  next(
   last
   , sym
   , push(pop(typestk, nopara.sym), i64)
   , blkstk
   , curblk + Wcall.seqsym(nopara.sym, top.typestk)
   , localtypes
  )
 else if kind = krecord then
  next(
   last
   , sym
   , push(pop(typestk, nopara.sym), i64)
   , blkstk
   , curblk + Wcall.recordsym(alltypes, sym)
   , localtypes
  )
 else if kind = kstart then
  next(
   last
   , sym
   , push(typestk, wtype64(alltypes, resulttype.sym))
   , push(blkstk, blkele(curblk, sym))
   , empty:seq.byte
   , localtypes
  )
 else if kind = kcontinue then
  next(
   last
   , sym
   , pop(typestk, nopara.sym)
   , push(blkstk, blkele(curblk, sym))
   , empty:seq.byte
   , localtypes
  )
 else if kind = kbr then
  {BlockBr}
  assert top.typestk = i32 report "BR type check fail:(printcode.curblk)/br:(code)",
  next(last, sym, pop.typestk, push(blkstk, blkele(curblk, sym)), empty:seq.byte, localtypes)
 else if kind = kexit then
  assert top.typestk = top.pop.typestk report
   "Exit type problem STK::(for l = "", e ∈ toseq.typestk do l + %.e,
   l)/br:(printcode.curblk)",
  next(last, sym, pop.typestk, push(blkstk, blkele(curblk, sym)), empty:seq.byte, localtypes)
 else if kind = kendblock then
  for blkhead = n.toseq.blkstk, e ∈ reverse.toseq.blkstk
  while kind.sym.e ∉ [kloop, kstart]
  do blkhead - 1
  let blks = subseq(toseq.blkstk, blkhead, n.toseq.blkstk)
  let isloop = kind.sym.blks sub 1 = kloop
  let setloopvar =
   if not.isloop then empty:seq.byte
   else
    for
     acc = empty:seq.byte
     , idx = no.getlocalinfo(localtypes, toword.firstvar.sym.blks sub 1)
     , e ∈ paratypes.sym.blks sub 1
    do next(Wdefine.idx + acc, idx + 1),
    acc
  let blockcode =
   for acc = empty:seq.byte, i = 1, a ∈ blks << 1
   do
    let kinda = kind.sym.a
    let z =
     if kinda = kexit then code.a + brX(n.blks - i - (if isloop then 0 else 1))
     else if kinda = kcontinue then code.a + setloopvar + br + LEBu(n.blks - 1 - i)
     else
      assert kinda = kbr report "BLOKP:(sym.a)",
      code.a + brif + LEBu(brt.sym.a - 1) + brX(brf.sym.a - 1),
    next([block, (asbytes.void) sub 1] + acc + z + END, i + 1),
   acc << 2,
  let newcode =
   code.blks sub 1
   + if isloop then
    setloopvar
    + [block]
    + asbytes.wtype64(alltypes, resulttype.sym.blks sub 1)
    + [loop, {void}tobyte.0x40]
    + blockcode
    + unreachable
    + END
   else [block] + asbytes.top.typestk + blockcode,
  next(last, sym, typestk, pop(blkstk, n.blks), newcode, localtypes)
 else if kind = kdefine then
  let t = addlocal(localtypes, wordname.sym, top.typestk),
  next(last, sym, pop.typestk, blkstk, curblk + Wdefine.no.getlocalinfo(t, wordname.sym), t)
 else if sym = symbol(internalmod, "set", [typeptr, typeint], typeptr)
 ∨ sym = symbol(internalmod, "set", [typeptr, typeptr], typeptr) then
  let l1 = addlocal(localtypes, "i64tmp" sub 1, i64)
  let telement = getlocalinfo(l1, "i64tmp" sub 1)
  let l2 = addlocal(l1, "tmp1" sub 1, i64)
  let tseq = getlocalinfo(l2, "tmp1" sub 1),
  let cc =
   Wdefine.telement
   + Wdefine.tseq
   + Wlocal.tseq
   + i32wrapi64
   + Wlocal.telement
   + Wstore(typeint, 0)
   + Wlocal.tseq
   + const64.8
   + i64add,
  next(last, sym, pop(typestk, 1), blkstk, curblk + cc, l2)
 else if name.module.sym ∈ "$global" then
  next(
   last
   , sym
   , push(typestk, i64)
   , blkstk
   , curblk + const64.allocateconstspace(merge.fullname.sym, [0])
   , localtypes
  )
 else if sym = symbol(internalmod, ">1", [typeint, typeint], typeref."ordering standard.") then
  let l1 = addlocal(localtypes, "tmp1" sub 1, i64)
  let t1 = getlocalinfo(l1, "tmp1" sub 1)
  let l2 = addlocal(l1, "i64tmp" sub 1, i64)
  let t2 = getlocalinfo(l2, "i64tmp" sub 1),
  let cc =
   Wdefine.t2
   + Wdefine.t1
   + Wlocal.t1
   + Wlocal.t2
   + i64gts
   + Wlocal.t1
   + Wlocal.t2
   + i64ges
   + i32add
   + i64extendi32s,
  next(last, sym, pop.typestk, blkstk, curblk + cc, l2)
 else if sym = symbol(internalmod, ">1", [typereal, typereal], typeref."ordering standard.") then
  let l1 = addlocal(localtypes, "tmp1f" sub 1, f64)
  let t1 = getlocalinfo(l1, "tmp1f" sub 1)
  let l2 = addlocal(l1, "f64tmp" sub 1, f64)
  let t2 = getlocalinfo(l2, "f64tmp" sub 1),
  let cc =
   Wdefine.t2
   + Wdefine.t1
   + Wlocal.t1
   + Wlocal.t2
   + f64gt
   + Wlocal.t1
   + Wlocal.t2
   + f64ge
   + i32add
   + i64extendi32s,
  next(last, sym, push(pop(typestk, 2), i64), blkstk, curblk + cc, l2)
 else if wordname.sym = "allocatespace" sub 1 then next(last, sym, typestk, blkstk, curblk + Wcall.allocatesym + i64extendi32u, localtypes)
 else if kind.sym = kidxNB then
  let l1 = addlocal(localtypes, "tmp1" sub 1, i64)
  let tidx = getlocalinfo(l1, "tmp1" sub 1)
  let l2 = addlocal(l1, "i64tmp" sub 1, i64)
  let tseq = getlocalinfo(l2, "i64tmp" sub 1)
  let theseqtype = basetype((paratypes.sym) sub 1, alltypes)
  {seqtype will be a basetype}
  let seqparameter = parameter.theseqtype
  let elementtype =
   if seqparameter ∈ [typeint, typereal, typeboolean, typebyte] then seqparameter
   else typeptr
  let type2 = [i32, f64, i64] sub findindex([typeboolean, typereal], elementtype),
  let cc = idxNB777(tseq, tidx, type2, parameter.theseqtype),
  next(last, sym, push(pop(typestk, 2), type2), blkstk, curblk + cc, l2)
 else if kind.sym = kcreatethreadZ then
  let psym =
   basesym(
    if kind.lastfref = kfref then lastfref
    else
     let tmp = fullconstantcode.last,
     tmp sub (n.tmp - 1)
   )
  let typeidx = typeidx64(alltypes, psym)
  let sym2 = symbol(internalmod, [merge("processX" + toword.typeidx)], [typeptr], typeint),
  let l1 = addlocal(localtypes, "tmp1" sub 1, i64),
  next(
   last
   , sym
   , push(pop(typestk, nopara.sym), i64)
   , blkstk
   , curblk
   + Wcall.recordsym(alltypes, sym)
   + f64converti64s
   + const32.tableindex.sym2
   + f64converti32s
   + Wcall.callprocessfunc
   + i64truncf64s
   , l1
  )
 else if wordname.sym = "createthreadY" sub 1 ∧ name.module.sym ∈ "builtin" then
  let typeidx =
   typeindex(top(typestk, nopara.sym - 3), wtype64(alltypes, parameter.para.module.sym))
  let sym2 = symbol(internalmod, [merge("processX" + toword.typeidx)], [typeptr], typeint)
  let l1 = addlocal(localtypes, "tmp1" sub 1, i64),
  let nocopy =
   {only need to deepcopy structures}
   if basetype(parameter.para.module.sym, alltypes) ∈ [typereal, typeint, typeboolean] then
    let t1 = getlocalinfo(l1, "tmp1" sub 1),
    Wdefine.t1 + Wlocal.t1 + Wlocal.t1 + i32wrapi64 + const64.0 + Wstore(typeint, 0)
   else empty:seq.byte,
  next(
   last
   , sym
   , push(pop(typestk, nopara.sym), i64)
   , blkstk
   , curblk
   + Wcall.recordsym(alltypes, sym)
   + nocopy
   + f64converti64s
   + const32.tableindex.sym2
   + f64converti32s
   + Wcall.callprocessfunc
   + i64truncf64s
   , l1
  )
 else
  let paratypes =
   for acc = empty:seq.wtype, @e ∈ paratypes.sym do acc + wtype64(alltypes, @e),
   acc
  assert paratypes = top(typestk, n.paratypes) report
   "type missmatch:(sym):(for acc = "", @e ∈ top(typestk, n.paratypes) do acc + %.@e,
   acc)/:(for acc = "", @e ∈ paratypes do acc + %.@e,
   acc)/br:(for acc = "", @e ∈ code do acc + %.@e,
   acc)"
  let ele = lookup2(knownfuncs, wfunc(alltypes, sym, empty:seq.byte)),
  let this =
   if not.isempty.ele then
    let discard2 = encode.coverage.%.sym.ele sub 1,
    code.ele sub 1
   else Wcall.sym,
  next(
   last
   , sym
   , push(pop(typestk, n.paratypes), wtype64(alltypes, resulttype.sym))
   , blkstk
   , curblk + this
   , localtypes
  )
assert not.isempty.typestk report "generatefuncbody:did not expect empty stack:(code):(toseq.typestk)"
{assert name.forsym /nin"set3zero"report"kkk:(forsym):(printcode(curblk+return))/p
(printcode(set2zero.alltypes))"}
let zk1 =
 for acc = empty:seq.localinfo, e ∈ toseq.localtypes do acc + localinfo.e,
 acc
let zk =
 for acc = empty:seq.wtype, e ∈ sort.zk1 do acc + type.e,
 acc,
funcbody(zk << nopara.forsym, curblk + return)

function idxNB777(tseq:localinfo, tidx:localinfo, type2:wtype, paratype:mytype) seq.byte
let packedlist = [typebyte, typepacked2, typepacked3, typepacked4, typepacked5, typepacked6]
let maybepacked = findindex(packedlist, paratype)
let std =
 if type2 = i64 then [i64load, tobyte.3] + LEBu.8
 else if type2 = f64 then [f64load, tobyte.3] + LEBu.8
 else
  assert type2 = i32 report "unexpected type",
  [i64load, tobyte.3] + LEBu.8 + i32wrapi64
{get seq type}
Wdefine.tidx
 + load64(Wtee.tseq, 0)
 + {does seq type eq 0?}const64.0
 + [i64eq, IF]
 + asbytes.type2
 + {standard sequence}Wlocal.tseq
 + Wlocal.tidx
 + const64.8
 + [i64mul, i64add, i32wrapi64]
 + std
 + ELSE
 + (if maybepacked ≤ n.packedlist then
 load64(Wlocal.tseq, 0)
 + const64.1
 + [i64eq, IF]
 + asbytes.type2
 + if maybepacked = 1 then
  {index packed byte sequence}Wlocal.tseq
  + Wlocal.tidx
  + [i64add, i32wrapi64, i64load8u, tobyte.0]
  + LEBu.15
  + ELSE
 else
  {index packed seq}
  {(tdx * maybepacked+2-maybepacked)*8 tdx *(maybepacked *8)+(2-maybepacked)*8}
  Wlocal.tseq
  + Wlocal.tidx
  + const64.maybepacked
  + i64mul
  + const64(2 - maybepacked)
  + i64add
  + const64.8
  + [i64mul, i64add, ELSE]
else empty:seq.byte)
 + {call function to get sequence element}Wlocal.tseq
 + Wlocal.tidx
 + load32(Wlocal.tseq, 0)
 + (if type2 = i32 then Wcallindirect.typeindex([i64, i64], i64) + i32wrapi64
else Wcallindirect.typeindex([i64, i64], type2))
 + if maybepacked ≤ n.packedlist then [END, END] else [END]

function brX(i:int) seq.byte if i = 0 then empty:seq.byte else [br] + LEBu.i

function Wstore(typ:mytype, offset:int) seq.byte
let t =
 if typ = typeint then [i64store, tobyte.3]
 else if typ = typereal then [f64store, tobyte.3]
 else
  assert typ = typeboolean report "PROBLEM",
  [i64extendi32s, i64store, tobyte.3],
t + LEBu.offset

function recordsymdef(alltypes:typedict, sym:symbol) encoding.wfunc
let t1 = nopara.sym
let cc = const64.nopara.sym + Wcall.allocatesym + Wdefine.t1
for acc = cc, idx = 0, typ ∈ paratypes.sym
do next(acc + Wlocal.t1 + Wlocal.idx + Wstore(typ, idx * 8), idx + 1),
encode.wfunc(
 alltypes
 , sym
 , funcbody([i32, i64, f64, i32], acc + Wlocal.t1 + [i64extendi32u, return])
 , funcidx.sym
)

function seqsym(nopara:int, typ:wtype) symbol
assert typ ∈ [i64, i32, f64] report "KL:(typ)",
symbol(
 moduleref."* $$sequence"
 , "$$sequence"
 , constantseq(nopara, if typ = i64 then typeint else if typ = f64 then typereal else typeboolean)
 , typeint
)

function seqsymdef(alltypes:typedict, sym:symbol) encoding.wfunc
let typ = (paratypes.sym) sub 1
let nopara = nopara.sym
let s = nopara
let cc =
 const64(nopara + 2)
 + Wcall.allocatesym
 + localtee
 + LEBu.s
 + const64.0
 + Wstore(typeint, 0)
 + Wlocal.s
 + const64.nopara
 + Wstore(typeint, 8)
for acc = cc, idx ∈ arithseq(nopara, 1, 0)
do acc + Wlocal.s + Wlocal.idx + Wstore(typ, 8 * idx + 16)
assert typ ∈ [typeint, typereal, typeboolean] report "seqsymdef:(typ):(printcode.acc)"
let t =
 wfunc(alltypes, sym, funcbody([i32], acc + Wlocal.s + i64extendi32u + return), funcidx.sym),
encode.t

function processXbody(functypeidx:int) seq.byte
let list = towtypelist.functypeidx
let rt = last.list
let struct = Wlocal.0 + i32wrapi64
let funccall =
 for code = empty:seq.byte, offset = 24, ptyp ∈ list >> 1
 do
  let newcode =
   if ptyp = i64 then struct + i64load + tobyte.3 + LEBu.offset
   else if ptyp = f64 then struct + f64load + tobyte.3 + LEBu.offset
   else
    assert ptyp = i32 report "ErrorX",
    struct + i32load + tobyte.2 + LEBu.offset,
  next(code + newcode, offset + 8),
 code + struct + i32load + tobyte.2 + LEBu.16 + Wcallindirect.functypeidx,
funcbody(
 [i64]
 , if rt = i64 then funccall
 else if rt = f64 then funccall + i64reinterpretf64
 else
  assert rt = i32 report "unknown type processbody",
  funccall + i64extendi32u
) 