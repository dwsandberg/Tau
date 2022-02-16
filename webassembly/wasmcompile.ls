#!/bin/bash tau stdlib webassembly testX test87

testgraph test89

module wasmcompile

use UTF8

use bits

use funcidx

use knownWfunc

use printfunc

use real

use standard

use symbol2

use wasm

use wasm2

use wasmconstant

use seq.Icode

use seq.blkele

use stack.blkele

use seq.blkele2

use seq.byte

use process.cccreturn

use seq.char

use encoding.coverage

use otherseq.localinfo

use seq.localinfo

use set.localmap

use otherseq.mytype

use seq.mytype

use seq.real

use seq.symbol

use set.symbol

use set.symdef

use encoding.wfunc

use otherseq.wfunc

use seq.wfunc

use otherseq.word

use stack.word

use encoding.wtype

use seq.wtype

use stack.wtype

use process.seq.Icode

use seq.seq.byte

use seq.encodingpair.coverage

use otherseq.encodingpair.wfunc

use seq.encodingpair.wfunc

use set.seq.word

use seq.seq.seq.byte

use IO2

type coverage is towfunc:seq.word

function =(a:coverage, b:coverage)boolean towfunc.a = towfunc.b

function hash(a:coverage)int hash.towfunc.a

function assignencoding(a:coverage)int nextencoding.a

function reportcoverage(knownfuncs:seq.wfunc)seq.word
let a = for acc = empty:set.seq.word, f ∈ knownfuncs do acc + print.sym.f /for(acc)
let b = 
 for acc = empty:set.seq.word, p ∈ encoding:seq.encodingpair.coverage do acc + towfunc.data.p /for(acc)
for txt = "", l ∈ toseq(a \ b)do txt + l + EOL /for(txt)

function importsare(knownfuncs:seq.wfunc, prg:set.symdef)set.symbol
for used = empty:seq.symbol, d ∈ toseq.prg do
 if name.module.sym.d ∈ "inputoutput"then
  for used2 = used, sym2 ∈ code.d do
   if isconst.sym2 ∨ isspecial.sym2 ∨ print.resulttype.sym2 ∉ ["real", "jsbytes"]
   ∨ module.sym2 ≠ internalmod then
    used2
   else used2 + sym2
  /for(used2)
 else used
/for(for used2 = asset.used, d2 ∈ knownfuncs do used2 - sym.d2 /for(used2))

Function jsname(sym:symbol)seq.word"exports." + name.sym

Function wasmcompile(alltypes:typedict, prg4:set.symdef, rootsin:seq.symbol, libname:seq.word)seq.word
let discard68 = encode.coverage."???"
let discard67 = startencodings
let knownfuncs = knownWfunc.alltypes
let imports = [abortfunc, callprocessfunc] + toseq.importsare(knownfuncs, prg4)
let roots = 
 toseq.asset(rootsin
 + symbol(moduleref."webassembly inputoutput", "allocatespace3", typereal, typereal)
 + symbol(moduleref."webassembly inputoutput"
 , "resume"
 , [typereal, typereal, typereal, typereal, typereal, typereal]
 , typereal
 )
 + symbol(moduleref."webassembly inputoutput", "blockseqtype", typereal)
 + symbol(moduleref."webassembly inputoutput", "jsmakepair", typereal,typereal,typereal)
 )
let imp = 
 for acc = empty:seq.seq.byte, @e ∈ imports do
  let discard0 = funcidx.@e
  let discard = addf(alltypes, @e, empty:seq.byte)
  acc + importfunc(typeidx32(alltypes, @e), first."imports", wordname.@e)
 /for(acc)
{create functions that will be exported}
let exp = 
 for acc = [exportprocessbody.alltypes, exporthandleerror.alltypes, exportreclaimspace.alltypes]
 , @e ∈ roots
 do
  acc + exportfunc(funcidx.@e, last.jsname.@e)
 /for(acc)
{assert false report for txt="", x /in roots do txt+print.x+EOL /for(txt)}
{define some support functions}
let descard100 = [allocatefunc.alltypes, getinstancefunc.alltypes, addencodingfunc.alltypes]
{look for exports that must be interpreted}
 let jsHTTP = 
 symbol(internalmod
 , "jsHTTP"
 , [typereal, typereal, typereal, typereal, typereal, typereal, typereal, typereal]
 , typereal
 )
let zzzzz = 
 for txt = "", sym ∈ roots do
  let code = getCode(prg4, sym)
  if  jsHTTP  /in getCode(prg4, sym) then
   {assert name.sym /nin"testpretty22"report print.code}
   interpret(alltypes, knownfuncs, sym, getCode(prg4, sym))
  else txt
 /for(txt)
{define depended functions}
let discardt = dependedfunc(alltypes, knownfuncs, prg4, length.imports + 1)
{define function to initialize words}
let startfuncidx = funcidx.symbol(moduleref."webassembly core", "initwords3", typeint)
let mustbedonelast = 
 addf(alltypes
 , symbol(moduleref."webassembly core", "initwords3", typeint)
 , initwordsbody
 )
{create the wasm file}
let discard = 
 for bodies = empty:seq.seq.byte
 , funcs2 = empty:seq.seq.byte
 , p ∈ sort.encoding:seq.encodingpair.wfunc << length.imports
 do next(bodies + code.data.p, funcs2 + LEB.typeidx.data.p)/for(createfile(libname + ".wasm"
 , createwasm(imp, funcs2, exp + exportmemory."memory"_1, bodies, dataseg, elementdata, startfuncidx)
 ))
if true then""
else
 {reportcoverage.knownfuncs+}zzzzz + EOL
 + for txt = "", p ∈ encoding:seq.encodingpair.wfunc do txt + toword.funcidx.data.p + print.sym.data.p + EOL /for(txt)
 + for txt = " /br+table+ /br", i = 2, idx ∈ elementdata do next(txt + toword.i + toword.idx + EOL, i + 1)/for(txt)

/use seq.encodingpair.efuncidx

/use encoding.efuncidx

Function dependedfunc(alltypes:typedict, knownfuncs:seq.wfunc, prg:set.symdef, i:int)int
let k = nobodies.i
for notused = to:encoding.wfunc(1), sym ∈ k do
 if name.module.sym ∈ "$$sequence"then seqsymdef(alltypes, sym)
 else if name.module.sym ∈ "$$record"then recordsymdef(alltypes, sym)
 else if name.module.sym ∈ "$$Icall"then
  encode.wfunc(alltypes, sym, $$Icallbody(alltypes, toint.name.sym), funcidx.sym)
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
    assert not.isempty.ele 
    report"dependedfunc:no definition for:" + print.sym + ":::" + name.sym
    let bodycode = 
     if isempty.ele then const64.0
     else
      let discard2 = encode.coverage.print.sym.first.ele
      for code2 = empty:seq.byte, j ∈ arithseq(nopara.sym, 1, 0)do code2 + Wlocal.j /for(code2 + code.first.ele)
    encode.wfunc(alltypes, sym, funcbody(empty:seq.wtype, bodycode + return), funcidx.sym)
  else
   let map = 
    for acc = empty:set.localmap, @e ∈ paratypes.sym do addlocal(acc, toword(cardinality.acc + 1), wtype64(alltypes, @e))/for(acc)
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
/for(if length.k = 0 then 0 else dependedfunc(alltypes, knownfuncs, prg, i + length.k)/if)

type localinfo is type:wtype, leb:seq.byte, no:int

type localmap is name:word, localinfo:localinfo

Export type:localmap

function ?(a:localmap, b:localmap)ordering name.a ? name.b

function getlocalinfo(a:set.localmap, w:word)localinfo
let t = lookup(a, localmap(w, localinfo(f64, empty:seq.byte, 0)))
assert not.isempty.t report"unknown local" + w + stacktrace
localinfo.t_1

function print(l:localinfo)seq.word print.asbytes.type.l + print.leb.l + print.no.l

function ?(a:localinfo, b:localinfo)ordering no.a ? no.b

Function addlocal(map:set.localmap, name:word, type:wtype)set.localmap
let no = cardinality.map
map + localmap(name, localinfo(type, LEB.no, no))

function Wlocal(l:localinfo)seq.byte[localget] + leb.l

function Wdefine(l:localinfo)seq.byte[localset] + leb.l

function Wtee(l:localinfo)seq.byte[localtee] + leb.l

function interpret(alltypes:typedict, knownfuncs:seq.wfunc, sym:symbol, symcode:seq.symbol)seq.word
let stacktype = addabstract(typeref."stack stack stdlib", typeint)
let map = 
 for acc = empty:set.localmap, @e ∈ paratypes.sym do addlocal(acc, toword(cardinality.acc + 1), wtype64(alltypes, @e))/for(acc)
let p1 = process.createcode2interpert(alltypes, knownfuncs, removeoptions.symcode, map, nopara.sym)
assert not.aborted.p1
report"ccc fail:" + print.sym + "lib:" + library.module.sym + EOL + print.symcode + EOL
+ message.p1
+ stacktrace
{assert name.sym /nin"test5"report print.sym+print.symcode+EOL+EOL+for txt="", pc=1, ele /in result.p1 do next(
txt+toword.pc+decodeop.tobyte.(toint.ele mod 256)+toword.(toint.ele / 256)+EOL, pc+1)/for(txt)}
let tmp = for acc = empty:seq.int, ele ∈ result.p1 do acc + toint.ele /for(acc)
let Emptystack = const64.getoffset.Constant2.[Lit.0, Lit.0, Record.[typeint, typeint]]
let code = 
 const64.constintseq.tmp + const64.1 + Emptystack + Emptystack
 + Wcall.symbol(moduleref."webassembly inputoutput"
 , "interpert"
 , [seqof.typeint, typeint, stacktype, seqof.typeint]
 , stacktype
 )
 + return
let discard = encode.wfunc(alltypes, sym, funcbody(empty:seq.wtype, code), funcidx.sym)
print.sym + EOL + print.symcode

type cccreturn is code:seq.byte, localtypes:seq.wtype

type blkele is code:seq.byte, sym:symbol

type r10 is map:set.localmap, code:seq.byte

Function ccc(alltypes:typedict, knownfuncs:seq.wfunc, code:seq.symbol, localmap:set.localmap)cccreturn
for typestk = empty:stack.wtype
, blkstk = empty:stack.blkele
, curblk = empty:seq.byte
, localtypes = localmap
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
   {assert not.isFref.sym report"FR2"+print.sym+"X"+print.length.elementdata}
   next(push(typestk, i64), blkstk, curblk + newcode, localtypes)
  else if sym = Littrue then next(push(typestk, i32), blkstk, curblk + const32.1, localtypes)
  else if sym = Litfalse then next(push(typestk, i32), blkstk, curblk + const32.0, localtypes)
  else if isword.sym then
   next(push(typestk, i64), blkstk, curblk + const64.value.wordconst.wordname.sym, localtypes)
  else if iswordseq.sym then
   next(push(typestk, i64), blkstk, curblk + const64.getoffset.wordsconst.worddata.sym, localtypes)
  else
   assert inmodule(sym, "$int")report"NOt HANDLE" + print.sym
   let this = [i64const] + LEBsigned.value.sym
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
 else if wordname.sym = "callidx"_1 ∧ inmodule(sym, "internal")then
  let l1 = addlocal(localtypes, "tmp1"_1, i64)
  let tidx = getlocalinfo(l1, "tmp1"_1)
  let l2 = addlocal(l1, "i64tmp"_1, i64)
  let tseq = getlocalinfo(l2, "i64tmp"_1)
  let cc = Wdefine.tidx + Wtee.tseq + Wlocal.tidx + Wlocal.tseq + i32wrapi64 + i32load + tobyte.2 + LEB.0
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
     else if iscontinue.sym.a then code.a + setloopvar + br + LEB(length.blks - 1 - i)
     else
      assert isbr.sym.a report"BLOKP" + print.sym.a
      code.a + brif + LEB(brt.sym.a - 1) + brX(brf.sym.a - 1)
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
  {assert subseq(keys.localtypes, 1, 2)/ne"1 2"report"XXC"+keys.localtypes+EOL+printcode.newcode+EOL+print.
sym.blks_1+print.resulttype.sym}
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

function brX(i:int)seq.byte if i = 0 then empty:seq.byte else[br] + LEB.i

function getblock(s:seq.blkele, i:int)seq.blkele
if isstartorloop.sym.s_i then subseq(s, i, length.s)else getblock(s, i - 1)

function print(localmap:set.localmap)seq.word
for l = "", e ∈ toseq.localmap do l + name.e + toword.no.localinfo.e + EOL /for(l)

function Wstore(typ:mytype, offset:int)seq.byte
let t = 
 if typ = typeint then[i64store, tobyte.3]
 else if typ = typereal then[f64store, tobyte.3]
 else
  assert typ = typeboolean report"PROBLEM"
  [i64extendi32s, i64store, tobyte.3]
t + LEB.offset

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
symbol(moduleref."$$sequence"
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
 const64(nopara + 2) + Wcall.allocatesym + localtee + LEB.s + const64.0 + Wstore(typeint, 0) + Wlocal.s
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
   if ptyp = i64 then struct + i64load + tobyte.3 + LEB.offset
   else if ptyp = f64 then struct + f64load + tobyte.3 + LEB.offset
   else
    assert ptyp = i32 report"ErrorX"
    struct + i32load + tobyte.2 + LEB.offset
  next(code + newcode, offset + 8)
 /for(code + struct + i32load + tobyte.2 + LEB.16 + Wcallindirect.functypeidx)
funcbody([i64]
, if rt = i64 then funccall
else if rt = f64 then funccall + i64reinterpretf64
else
 assert rt = i32 report"unknown type processbody"
 funccall + i64extendi32u
)

function typeidx(alltypes:typedict, sym:symbol)int
let paratypes = 
 for acc = empty:seq.wtype, @e ∈ paratypes.sym do acc + wtype64(alltypes, @e)/for(acc)
let rt = wtype64(alltypes, resulttype.sym)
typeindex(paratypes, rt)

function $$Icallbody(alltypes:typedict, functypeidx:int)seq.byte
let stacktype = addabstract(typeref."stack stack stdlib", typeint)
let undertop = 
 symbol(moduleref("stdlib stack", typeint)
 , "undertop"
 , [stacktype, typeint]
 , typeint
 )
let poppush = 
 symbol(moduleref."stdlib inputoutput"
 , "poppush"
 , [stacktype, typeint, typeint]
 , stacktype
 )
let list = towtypelist.functypeidx
let funccall = 
 for code = empty:seq.byte, idx = length.list - 2, ptyp ∈ list >> 1 do
  let newcode = code + Wlocal.0 + const64.idx + Wcall.undertop
  next(if ptyp = i64 then newcode
  else if ptyp = f64 then newcode + f64reinterpreti64
  else
   assert ptyp = i32 report"ErrorX"
   newcode + i32wrapi64
  , idx - 1
  )
 /for(code + Wlocal.1 + i32wrapi64 + Wcallindirect.functypeidx)
let rt = last.list
let resulttoi64 = 
 if rt = i64 then funccall
 else if rt = f64 then funccall + i64reinterpretf64
 else
  assert rt = i32 report"unknown type processbody"
  funccall + i64extendi32u
assert true report printcode(Wlocal.0 + const64(length.list - 1) + resulttoi64 + Wcall.poppush)
funcbody([i64], Wlocal.0 + const64(length.list - 1) + resulttoi64 + Wcall.poppush)

type Icode is toint:int

function Icode(inst:byte, op:int)Icode Icode(toint.inst + op * 256)

function Icode(inst:byte)Icode Icode.toint.inst

type blkele2 is pc:int, sym:symbol

Function createcode2interpert(alltypes:typedict, knownfuncs:seq.wfunc, code:seq.symbol, localmap:set.localmap, nopara:int)seq.Icode
for blkstk = empty:seq.blkele2, curblk = empty:seq.Icode, localtypes = nopara, sym ∈ code do
 if islocal.sym then next(blkstk, curblk + Icode(localget, value.sym - 1), localtypes)
 else if isrecordconstant.sym then next(blkstk, curblk + Icode(i64const, getoffset.sym), localtypes)
 else if isconst.sym then
  if inmodule(sym, "$real")then
   if value.sym = 0 then next(blkstk, curblk + Icode(i64const, 0), localtypes)
   else
    assert casttoreal.value.sym ∈ [1.0, 8.0, 0.125,64.0]
    report"REAL" + print(3, casttoreal.value.sym) + print.value.sym
    next(blkstk, curblk + Icode(f64const, intpart(casttoreal.value.sym * 1000.0)), localtypes)
  else if isFref.sym then next(blkstk, curblk + Icode(i64const, tableindex.basesym.sym), localtypes)
  else if sym = Littrue then next(blkstk, curblk + Icode(i64const, 1), localtypes)
  else if sym = Litfalse then next(blkstk, curblk + Icode(i64const, 0), localtypes)
  else if isword.sym then next(blkstk, curblk + Icode(i64const, value.wordconst.wordname.sym), localtypes)
  else if iswordseq.sym then
   next(blkstk, curblk + Icode(i64const, getoffset.wordsconst.worddata.sym), localtypes)
  else
   assert inmodule(sym, "$int")report"NOt HANDLE" + print.sym
   {assert value.sym /ge 0 report"neg constant"}
   next(blkstk, curblk + Icode(i64const, value.sym), localtypes)
 else if isSequence.sym then
  let seqsym = seqsym(nopara.sym, wtype64(alltypes, parameter.resulttype.sym))
  next(blkstk, curblk + Icall(alltypes, seqsym), localtypes)
 else if isRecord.sym then next(blkstk, curblk + Icall(alltypes, recordsym(alltypes, sym)), localtypes)
 else if isstart.sym then next(blkstk + blkele2(length.curblk + 1, sym), curblk, localtypes)
 else if isloopblock.sym then
  let newcode = 
   for acc = curblk, localno ∈ arithseq(nopara.sym, -1, firstvar.sym + nopara.sym - 2)do acc + Icode(localset, localno)/for(acc)
  next(blkstk + blkele2(length.newcode + 1, sym), newcode, localtypes)
 else if sym = Exit then next(blkstk + blkele2(length.curblk + 2, sym), curblk + Icode.br, localtypes)
 else if isbr.sym then
  next(blkstk + blkele2(length.curblk + 3, sym), curblk + Icode.brif + Icode.br, localtypes)
 else if sym = EndBlock then
  let newcode = 
   for targets = empty:seq.int, newcode = curblk, idx ∈ arithseq(length.blkstk, -1, length.blkstk)
   while sym.blkstk_idx = Exit ∨ isbr.sym.blkstk_idx ∨ iscontinue.sym.blkstk_idx
   do let this = blkstk_idx
   let newtargets = [pc.this + 1] + targets
   next(newtargets
   , if iscontinue.sym.this then newcode
   else if sym.this = Exit then subseq(newcode, 1, pc.this - 2) + Icode(br, last.newtargets)
   else
    subseq(newcode, 1, pc.this - 3)
    + [Icode(brif, newtargets_(brt.sym.this)), Icode(br, newtargets_(brf.sym.this))]/if
   + subseq(newcode, pc.this, length.newcode)
   )
   /for(newcode + Icode(tobyte.0, idx))
  next(subseq(blkstk, 1, toint.last.newcode / 256 - 1), newcode >> 1, localtypes)
 else if iscontinue.sym then
  let seq = 
   for acc = 0, idx ∈ arithseq(length.blkstk, -1, length.blkstk)while not.isloopblock.sym.blkstk_idx do acc /for(blkstk_idx)
  let newcode = 
   for acc = curblk, localno ∈ arithseq(nopara.sym.seq, -1, firstvar.sym.seq + nopara.sym.seq - 2)do acc + Icode(localset, localno)/for(acc + Icode(br, pc.seq + 1))
  {assert false report"XXX"+print.sym+print.firstvar.sym.seq}
  next(blkstk + blkele2(length.newcode + 1, sym), newcode, localtypes)
 else if isdefine.sym then
  next(blkstk, curblk + Icode(localset, toint.wordname.sym - 1), max(toint.wordname.sym, localtypes))
 else if print.sym ∈ ["internal:bitcast(ptr)int", "internal:bitcast(int)ptr"]then
  next(blkstk, curblk, localtypes)
 else  if sym = symbol(internalmod, "callidx", seqof.typeint, typeint, typeint)
 /or sym = symbol(internalmod, "callidx", seqof.typeptr, typeint, typeint)then
  let typ = 
   symbol(moduleref."$$Icall"
   , [toword.typeindex([i64, i64], i64)]
   , typeint
   , typeint
   , typeint
   )
  next(blkstk, curblk + Icode(tobyte.254, tableindex.funcidx.typ), localtypes)
 else if sym = symbol(moduleref("builtin",typeint),"assert",seqof.typeword,typeint)
 /or sym = symbol(moduleref("builtin",typeptr),"assert",seqof.typeword,typeptr)
  /or ( {module.sym=internalmod /and} name.sym /in "idxseq fld packedindex processisaborted
  getseqlength getseqtype") then
  next(blkstk, curblk + Icall(alltypes, sym), localtypes)
 else 
  let ele = lookup2(knownfuncs, wfunc(alltypes, sym, empty:seq.byte))
  let this = 
   if not.isempty.ele  then
    if length.code.first.ele=0 then empty:seq.Icode
    else 
    assert length.code.first.ele = 1 report"/br ------not length one------- /br"+print.sym+
      printcode.code.first.ele
    [Icode.first.code.first.ele]
   else Icall(alltypes, sym)
  next(blkstk, curblk + this, localtypes)
/for([Icode(tobyte.0, localtypes - nopara)] + curblk + Icode.return)

function Icall(alltypes:typedict, sym:symbol)seq.Icode
let typ = 
 tableindex.funcidx.symbol(moduleref."$$Icall", [toword.typeindex(alltypes, sym)], typeint, typeint, typeint)
[Icode(if name.sym ∈ "jsHTTP"then tobyte.255 else call
, tableindex.funcidx.sym
)
, Icode(tobyte.0, typ)
] 