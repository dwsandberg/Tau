Module wasmcompile

use otherseq.word

use bits

use seq.blkele

use stack.blkele

use seq.byte

use seq.seq.byte

use process.cccreturn

use seq.char

use encoding.coverage

use funcidx

use knownWfunc

use set.local5map

use otherseq.localinfo

use otherseq.mytype

use printfunc

use standard

use seq.symbol

use set.symbol

use symbol2

use set.symdef

use wasm

use wasm2

use encoding.wfunc

use otherseq.wfunc

use set.seq.word

use seq.wtype

use stack.wtype

type coverage is towfunc:seq.word

function =(a:coverage, b:coverage)boolean towfunc.a = towfunc.b

function hash(a:coverage)int hash.towfunc.a

function reportcoverage(knownfuncs:seq.wfunc)seq.word
let a = for acc = empty:set.seq.word, f ∈ knownfuncs do acc + print.sym.f /for(acc)
let b = 
 for acc = empty:set.seq.word, p ∈ encodingdata:coverage do acc + towfunc.p /for(acc)
for txt = "", l ∈ toseq(a \ b)do txt + l + EOL /for(txt)


Function jsname(sym:symbol)seq.word"exports." + name.sym

use otherseq.symbol

use file

use seq.file

function %(s:symbol) seq.word print.s

Function wasmcompile(alltypes:typedict, prg4:set.symdef, roots:seq.symbol,
 o:seq.word,imports:seq.symbol)seq.file
let discard68 = encode.coverage."???"
let discard67 = startencodings
let imp = 
 for acc = empty:seq.seq.byte, @e ∈ imports do
   let discard = addf(alltypes, @e, empty:seq.byte)
  acc + importfunc(typeidx32(alltypes, @e), first."imports", wordname.@e)
 /for(acc)
 let knownfuncs = knownWfunc(alltypes)
{create functions that will be exported}
let exp = 
 for acc = empty:seq.seq.byte
 , @e ∈ roots
 do
  acc + exportfunc(funcidx.@e, last.jsname.@e)
 /for(acc)
{define  functions with hand coded webassembly definitions }
let discard100=[processbodyfunc.alltypes,handleerrorfunc.alltypes,reclaimspacefunc.alltypes
,allocatefunc.alltypes, getinstancefunc.alltypes, addencodingfunc.alltypes]
{define depended functions}
let discardt = dependedfunc(alltypes, knownfuncs, prg4, length.imports + 1)
{define function to initialize words}
let startfuncidx = funcidx.symbol(moduleref."* core", "initwords3", typeint)
let mustbedonelast = 
 addf(alltypes, symbol(moduleref."* core", "initwords3", typeint), initwordsbody)
let forlater = 
 "Successful compile  /p"
 + for txt = "", p ∈ encodingdata:wfunc do txt + toword.funcidx.p + print.sym.p + EOL /for(txt)
 + for txt = " /br+table+ /br", i = 2, idx ∈ elementdata do next(txt + toword.i + toword.idx + EOL, i + 1)/for(txt)
{create the wasm file}
assert startfuncidx < length.encodingdata:wfunc
report"internal error:startfuncidx exceeds number of functions"
for bodies = empty:seq.seq.byte
, funcs2 = empty:seq.seq.byte
, p ∈ sort.encodingdata:wfunc << length.imports
do next(bodies + code.p, funcs2 + LEBu.typeidx.p)/for(
let fn=filename.o
[
file(fn
 ,createwasm(imp, funcs2, exp + exportmemory."memory"_1, bodies, dataseg, elementdata, startfuncidx))
,file(filename("+"+ dirpath.fn +merge([name.fn]+"info" )+".html"),reportcoverage.knownfuncs+forlater)])


Function dependedfunc(alltypes:typedict, knownfuncs:seq.wfunc, prg:set.symdef, idx:int)int
{Do not consider function indices less that idx} 
{get the symbols of functions that has been referenced but do not
have a definition}
let k = nobodies.idx 
if isempty.k then { no functions  that do not have definitions  } 0
else
for notused = to:encoding.wfunc(1), sym ∈ k do
 if name.module.sym ∈ "$$sequence"then seqsymdef(alltypes, sym)
 else if name.module.sym ∈ "$$record"then recordsymdef(alltypes, sym)
 else 
  let code = removeoptions.getCode(prg, sym)
  if isempty.code then
   let ele = lookup(knownfuncs, wfunc(alltypes, sym, empty:seq.byte))
   if isempty.ele ∧ module.sym = internalmod ∧ name.sym ∉ "set"then
     let c = decodeword.name.sym
     let d = decodeword.first."processX"
     assert subseq(c, 1, length.d) = d report"HHHX" + print.sym
     let typeidx = toint.encodeword(c << length.d)
     encode.wfunc(alltypes, sym, processXbody.typeidx, funcidx.sym)
   else
    assert not.isempty.ele report"dependedfunc:no definition for:" + print.sym + ":::" + name.sym
    let bodycode = 
     if isempty.ele then const64.0
     else
      let discard2 = encode.coverage.print.sym.first.ele
      for code2 = empty:seq.byte, j ∈ arithseq(nopara.sym, 1, 0)do code2 + Wlocal.j /for(code2 + code.first.ele)
    encode.wfunc(alltypes, sym, funcbody(empty:seq.wtype, bodycode + return), funcidx.sym)
  else
   let map = 
    for acc = empty:set.local5map, @e ∈ paratypes.sym do addlocal(acc, toword(cardinality.acc + 1), wtype64(alltypes, @e))/for(acc)
   let p1 = process.ccc(alltypes, knownfuncs, code, map)
   assert not.aborted.p1
   report"ccc fail3:" + print.sym + "libX:" + library.module.sym + EOL + print.code + EOL
   + message.p1
   + stacktrace
   encode.wfunc(alltypes
   , sym
   , funcbody(localtypes.result.p1 << nopara.sym, code.result.p1 + return)
   , funcidx.sym
   )
/for( dependedfunc(alltypes, knownfuncs, prg, idx + length.k ))

type localinfo is type:wtype, leb:seq.byte, no:int

{???? local5map should be changed to localmap but problem occurs with conflict of localmap in codegen}

type local5map is name:word, localinfo:localinfo

Export type:local5map

function ?(a:local5map, b:local5map)ordering name.a ? name.b

function getlocalinfo(a:set.local5map, w:word)localinfo
let t = lookup(a, local5map(w, localinfo(f64, empty:seq.byte, 0)))
assert not.isempty.t report"unknown local" + w + stacktrace
localinfo.t_1

function print(l:localinfo)seq.word print.asbytes.type.l + print.leb.l + %.no.l

function ?(a:localinfo, b:localinfo)ordering no.a ? no.b

Function addlocal(map:set.local5map, name:word, type:wtype)set.local5map
let no = cardinality.map
map + local5map(name, localinfo(type, LEBu.no, no))

function Wlocal(l:localinfo)seq.byte[localget] + leb.l

function Wdefine(l:localinfo)seq.byte[localset] + leb.l

function Wtee(l:localinfo)seq.byte[localtee] + leb.l

type cccreturn is code:seq.byte, localtypes:seq.wtype

type blkele is code:seq.byte, sym:symbol

Function ccc(alltypes:typedict, knownfuncs:seq.wfunc, code:seq.symbol, local5map:set.local5map)cccreturn
for typestk = empty:stack.wtype
, blkstk = empty:stack.blkele
, curblk = empty:seq.byte
, localtypes = local5map
, sym ∈ code
do
 if islocal.sym then
  let t = getlocalinfo(localtypes, wordname.sym)
  next(push(typestk, type.t), blkstk, curblk + Wlocal.t, localtypes)
 else if sym = symbol(internalmod, "set", typeptr, typeint, typeptr)
 ∨ sym = symbol(internalmod, "set", typeptr, typeptr, typeptr)then
  let l1 = addlocal(localtypes, "i64tmp"_1, i64)
  let telement = getlocalinfo(l1, "i64tmp"_1)
  let l2 = addlocal(l1, "tmp1"_1, i64)
  let tseq = getlocalinfo(l2, "tmp1"_1)
  let cc = 
   Wdefine.telement + Wdefine.tseq + Wlocal.tseq + i32wrapi64 + Wlocal.telement + Wstore(typeint, 0)
   + Wlocal.tseq
   + const64.8
   + i64add
  next(pop(typestk, 1), blkstk, curblk + cc, l2)
 else if isrecordconstant.sym then
  let this = const64.getoffset.sym
  next(push(typestk, i64), blkstk, curblk + this, localtypes)
 else if isconst.sym then
  if inmodule(sym, "$real")then
   let val = bits.value.sym
   let this = 
    for acc = [f64const], @i = 1, @e ∈ constantseq(8, 0)do next(acc + tobyte(val >> (8 * @i - 8) ∧ bits.255), @i + 1)/for(acc)
   next(push(typestk, f64), blkstk, curblk + this, localtypes)
  else if isFref.sym then
   let newcode = const64.tableindex.basesym.sym
   {assert not.isFref.sym report"FR2"+print.sym+"X"+%.length.elementdata}
   next(push(typestk, i64), blkstk, curblk + newcode, localtypes)
  else if sym = Littrue then next(push(typestk, i32), blkstk, curblk + const32.1, localtypes)
  else if sym = Litfalse then next(push(typestk, i32), blkstk, curblk + const32.0, localtypes)
  else if isword.sym then
   next(push(typestk, i64), blkstk, curblk + const64.value.wordconst.wordname.sym, localtypes)
  else if iswordseq.sym then
   next(push(typestk, i64), blkstk, curblk + const64.getoffset.wordsconst.worddata.sym, localtypes)
  else
   assert inmodule(sym, "$int")report"NOt HANDLE" + print.sym
   let this = [i64const] + LEBs.value.sym
   next(push(typestk, i64), blkstk, curblk + this, localtypes)
 else if inmodule(sym, "$global")then
  next(push(typestk, i64)
  , blkstk
  , curblk + const64.allocateconstspace(merge.fullname.sym, [0])
  , localtypes
  )
 else if sym = symbol(internalmod, "?", typeint, typeint, typeref."ordering standard.")then
  let l1 = addlocal(localtypes, "tmp1"_1, i64)
  let t1 = getlocalinfo(l1, "tmp1"_1)
  let l2 = addlocal(l1, "i64tmp"_1, i64)
  let t2 = getlocalinfo(l2, "i64tmp"_1)
  let cc = 
   Wdefine.t2 + Wdefine.t1 + Wlocal.t1 + Wlocal.t2 + i64gts + Wlocal.t1 + Wlocal.t2 + i64ges + i32add
   + i64extendi32s
  next(pop.typestk, blkstk, curblk + cc, l2)
 else if sym = symbol(internalmod, "?", typereal, typereal, typeref."ordering standard.")then
  let l1 = addlocal(localtypes, "tmp1f"_1, f64)
  let t1 = getlocalinfo(l1, "tmp1f"_1)
  let l2 = addlocal(l1, "f64tmp"_1, f64)
  let t2 = getlocalinfo(l2, "f64tmp"_1)
  let cc = 
   Wdefine.t2 + Wdefine.t1 + Wlocal.t1 + Wlocal.t2 + f64gt + Wlocal.t1 + Wlocal.t2 + f64ge + i32add
   + i64extendi32s
  next(push(pop(typestk, 2), i64), blkstk, curblk + cc, l2)
 else if wordname.sym = "allocatespace"_1 then
  {assert false report"here2"}
  next(typestk, blkstk, curblk + Wcall.allocatesym + i64extendi32u, localtypes)
 else if wordname.sym = "callidx"_1 ∧ isInternal.sym then
  let l1 = addlocal(localtypes, "tmp1"_1, i64)
  let tidx = getlocalinfo(l1, "tmp1"_1)
  let l2 = addlocal(l1, "i64tmp"_1, i64)
  let tseq = getlocalinfo(l2, "i64tmp"_1)
  let cc = Wdefine.tidx + Wtee.tseq + Wlocal.tidx + Wlocal.tseq + i32wrapi64 + i32load + tobyte.2 + LEBu.0
  if resulttype.sym = typeboolean then
   next(push(pop(typestk, 2), i32)
   , blkstk
   , curblk + cc + Wcallindirect.typeindex([i64, i64], i64) + i32wrapi64
   , l2
   )
  else if resulttype.sym = typereal then
   next(push(pop(typestk, 2), f64)
   , blkstk
   , curblk + cc + Wcallindirect.typeindex([i64, i64], f64)
   , l2
   )
  else next(pop.typestk, blkstk, curblk + cc + Wcallindirect.typeindex([i64, i64], i64), l2)
 else if isloopblock.sym then
  let locals = 
   for acc = localtypes, varno = firstvar.sym, t ∈ paratypes.sym do next(addlocal(acc, toword.varno, wtype64(alltypes, t)), varno + 1)/for(acc)
  next(push(pop(typestk, nopara.sym), wtype64(alltypes, resulttype.sym))
  , push(blkstk, blkele(curblk, sym))
  , empty:seq.byte
  , locals
  )
 else if isSequence.sym then
  next(push(pop(typestk, nopara.sym), i64)
  , blkstk
  , curblk + Wcall.seqsym(nopara.sym, top.typestk)
  , localtypes
  )
 else if isRecord.sym then
  next(push(pop(typestk, nopara.sym), i64)
  , blkstk
  , curblk + Wcall.recordsym(alltypes, sym)
  , localtypes
  )
 else if isstart.sym then
  next(push(typestk, wtype64(alltypes, resulttype.sym))
  , push(blkstk, blkele(curblk, sym))
  , empty:seq.byte
  , localtypes
  )
 else if iscontinue.sym then
  next(pop(typestk, nopara.sym), push(blkstk, blkele(curblk, sym)), empty:seq.byte, localtypes)
 else if isbr.sym then
  {BlockBr}
  assert top.typestk = i32 report"BR type check fail" + printcode.curblk + EOL + print.code
  next(pop.typestk, push(blkstk, blkele(curblk, sym)), empty:seq.byte, localtypes)
 else if sym = Exit then
  assert top.typestk = top.pop.typestk
  report"Exit type problem STK:"
  + for l = "", e ∈ toseq.typestk do l + print.e /for(l)
  + EOL
  + printcode.curblk
  + EOL
  + print.code
  next(pop.typestk, push(blkstk, blkele(curblk, sym)), empty:seq.byte, localtypes)
 else if sym = EndBlock then
  let blks = getblock(toseq.blkstk, length.toseq.blkstk)
  let isloop = isloopblock.sym.blks_1
  let setloopvar = 
   if not.isloop then empty:seq.byte
   else
    for acc = empty:seq.byte
    , idx = no.getlocalinfo(localtypes, toword.firstvar.sym.blks_1)
    , e ∈ paratypes.sym.blks_1
    do next(Wdefine.idx + acc, idx + 1)/for(acc)
  let blockcode = 
   for acc = empty:seq.byte, i = 1, a ∈ blks << 1 do
    let z = 
     if sym.a = Exit then code.a + brX(length.blks - i - if isloop then 0 else 1 /if)
     else if iscontinue.sym.a then code.a + setloopvar + br + LEBu(length.blks - 1 - i)
     else
      assert isbr.sym.a report"BLOKP" + print.sym.a
      code.a + brif + LEBu(brt.sym.a - 1) + brX(brf.sym.a - 1)
    next([block, first.asbytes.void] + acc + z + END, i + 1)
   /for(acc)
   << 2
  let newcode = 
   code.first.blks
   + if isloop then
    setloopvar + [block] + asbytes.wtype64(alltypes, resulttype.sym.blks_1)
    + [loop, {void}tobyte.0x40]
    + blockcode
    + unreachable
    + END
   else[block] + asbytes.top.typestk + blockcode
  {assert subseq(keys.localtypes, 1, 2)/ne"1 2"report"XXC"+keys.localtypes+EOL+printcode.newcode+EOL+print
    .sym.blks_1+print.resulttype.sym}
  next(typestk, pop(blkstk, length.blks), newcode, localtypes)
 else if isdefine.sym then
  let idx = cardinality.localtypes
  next(pop.typestk, blkstk, curblk + Wdefine.idx, addlocal(localtypes, wordname.sym, top.typestk))
 else if wordname.sym = "createthreadY"_1 ∧ inmodule(sym, "builtin")then
  let typeidx = typeindex(top(typestk, nopara.sym - 3), wtype64(alltypes, parameter.para.module.sym))
  let sym2 = symbol(internalmod, [merge("processX" + toword.typeidx)], typeptr, typeint)
  let l1 = addlocal(localtypes, "tmp1"_1, i64)
  let nocopy = 
   {only need to deepcopy structures}
   if basetype(parameter.para.module.sym, alltypes) ∈ [typereal, typeint, typeboolean]then
    let t1 = getlocalinfo(l1, "tmp1"_1)
    Wdefine.t1 + Wlocal.t1 + Wlocal.t1 + i32wrapi64 + const64.0 + Wstore(typeint, 0)
   else empty:seq.byte
  next(push(pop(typestk, nopara.sym), i64)
  , blkstk
  , curblk + Wcall.recordsym(alltypes, sym) + nocopy + f64converti64s + const32.tableindex.sym2
  + f64converti32s
  + Wcall.callprocessfunc
  + i64truncf64s
  , l1
  )
 else
  let paratypes = 
   for acc = empty:seq.wtype, @e ∈ paratypes.sym do acc + wtype64(alltypes, @e)/for(acc)
  assert paratypes = top(typestk, length.paratypes)
  report"type missmatch" + print.sym
  + for acc = "", @e ∈ top(typestk, length.paratypes)do acc + print.@e /for(acc)
  + "/"
  + for acc = "", @e ∈ paratypes do acc + print.@e /for(acc)
  + " /br"
  + for acc = "", @e ∈ code do acc + print.@e /for(acc)
  let ele = lookup2(knownfuncs, wfunc(alltypes, sym, empty:seq.byte))
  let this = 
   if not.isempty.ele then
    let discard2 = encode.coverage.print.sym.first.ele
    code.first.ele
   else Wcall.sym
  next(push(pop(typestk, length.paratypes), wtype64(alltypes, resulttype.sym))
  , blkstk
  , curblk + this
  , localtypes
  )
/for(assert not.isempty.typestk report"ccc:did not expect empty stack" + print.code + print.typestk
let zk1 = 
 for acc = empty:seq.localinfo, e ∈ toseq.localtypes do acc + localinfo.e /for(acc)
let zk = for acc = empty:seq.wtype, e ∈ sort.zk1 do acc + type.e /for(acc)
cccreturn(curblk, zk))

function print(typestk:stack.wtype)seq.word
for l = "", e ∈ toseq.typestk do l + print.e /for(l)

function brX(i:int)seq.byte if i = 0 then empty:seq.byte else[br] + LEBu.i

function getblock(s:seq.blkele, i:int)seq.blkele
if isstartorloop.sym.s_i then subseq(s, i, length.s)else getblock(s, i - 1)

function print(local5map:set.local5map)seq.word
for l = "", e ∈ toseq.local5map do l + name.e + toword.no.localinfo.e + EOL /for(l)

function Wstore(typ:mytype, offset:int)seq.byte
let t = 
 if typ = typeint then[i64store, tobyte.3]
 else if typ = typereal then[f64store, tobyte.3]
 else
  assert typ = typeboolean report"PROBLEM"
  [i64extendi32s, i64store, tobyte.3]
t + LEBu.offset

function recordsymdef(alltypes:typedict, sym:symbol)encoding.wfunc
let t1 = nopara.sym
let cc = const64.nopara.sym + Wcall.allocatesym + Wdefine.t1
for acc = cc, idx = 0, typ ∈ paratypes.sym do next(acc + Wlocal.t1 + Wlocal.idx + Wstore(typ, idx * 8), idx + 1)/for(encode.wfunc(alltypes
, sym
, funcbody([i32, i64, f64, i32], acc + Wlocal.t1 + [i64extendi32u, return])
, funcidx.sym
))

function seqsym(nopara:int, typ:wtype)symbol
assert typ ∈ [i64, i32, f64]report"KL" + print.typ
symbol(moduleref."* $$sequence"
, "$$sequence"
, constantseq(nopara
, if typ = i64 then typeint else if typ = f64 then typereal else typeboolean
)
, typeint
)

function seqsymdef(alltypes:typedict, sym:symbol)encoding.wfunc
let typ = first.paratypes.sym
let nopara = nopara.sym
let s = nopara
let cc = 
 const64(nopara + 2) + Wcall.allocatesym + localtee + LEBu.s + const64.0 + Wstore(typeint, 0)
 + Wlocal.s
 + const64.nopara
 + Wstore(typeint, 8)
for acc = cc, idx ∈ arithseq(nopara, 1, 0)do acc + Wlocal.s + Wlocal.idx + Wstore(typ, 8 * idx + 16)/for(assert typ ∈ [typeint, typereal, typeboolean]report"seqsymdef" + print.typ + printcode.acc
let t = wfunc(alltypes, sym, funcbody([i32], acc + Wlocal.s + i64extendi32u + return), funcidx.sym)
encode.t)

function processXbody(functypeidx:int)seq.byte
let list = towtypelist.functypeidx
let rt = last.list
let struct = Wlocal.0 + i32wrapi64
let funccall = 
 for code = empty:seq.byte, offset = 24, ptyp ∈ list >> 1 do
  let newcode = 
   if ptyp = i64 then struct + i64load + tobyte.3 + LEBu.offset
   else if ptyp = f64 then struct + f64load + tobyte.3 + LEBu.offset
   else
    assert ptyp = i32 report"ErrorX"
    struct + i32load + tobyte.2 + LEBu.offset
  next(code + newcode, offset + 8)
 /for(code + struct + i32load + tobyte.2 + LEBu.16 + Wcallindirect.functypeidx)
funcbody([i64]
, if rt = i64 then funccall
else if rt = f64 then funccall + i64reinterpretf64
else
 assert rt = i32 report"unknown type processbody"
 funccall + i64extendi32u
)

