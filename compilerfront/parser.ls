Module parser

use PEGrules

use UTF8

use seq.char

use mytype

use seq1.mytype

use seq.mytype

use set.mytype

use pretty

use standard

use seq1.symbol

use seq.symbol

use set.symbol

use symbol1

use symboldict

use seq1.word

use seq.word

use seq.bindinfo

use token

use seq.token

type commonType is types:set.mytype, outText:boolean, input:seq.word

type bindinfo is dict:symboldict, code:seq.symbol, types:seq.mytype, text:seq.word

Function parser(
input:seq.word
, dict:symboldict
, types:set.mytype
, outText:boolean
) seq.symbol
{OPTION XPROFILE}
let b = bindinfo(dict, empty:seq.symbol, empty:seq.mytype, "")
let tokens = totokens.input
let r = parse(packed.tokens, b, commonType(types, outText, input))
assert status.r ∈ "Match" report errormessage("syntax error", recoverInfo(pop.stk.r, tokens, i.top.stk.r, 1)),
code.result.r

function toAttribute(b:bindinfo, w:seq.word) bindinfo
bindinfo(dict.b, empty:seq.symbol, empty:seq.mytype, w)

function toAttribute(b:bindinfo, t:seq.token) bindinfo
for w = "", e ∈ t do w + toword.e,
bindinfo(dict.b, empty:seq.symbol, empty:seq.mytype, w)

function errormessage(message:seq.word, rinfo:recoverInfo) seq.word
let input = input.rinfo
let place = place.rinfo
let ending = recoveryEnding.rinfo
let pp = prettyNoChange(towords.subseq(input, 1, place - 1) + ending)
for idx = n.pp, remove = ending, addback = "", go = not.isempty.ending, e ∈ reverse.pp
while go
do
 if e = last.remove then next(idx - 1, remove >> 1, addback, n.remove > 1)
 else
  assert true report "ERR DEBUG" + showZ.remove + "/p" + showZ.pp,
  if e ∈ "/literal:(escapeformat)" then next(idx - 1, remove, [e] + addback, go)
  else if e
  ∈ "/keyword /br
  ," then next(idx - 1, remove, addback, go)
  else next(idx - 1, remove, addback, false)
let t = ":(red.message)/br:(subseq(pp, 1, idx))"
for unprocessed = "", e ∈ subseq(input, place, min(place + 10, n.input - 1))
do unprocessed + toword.e,
(if not.isempty.t ∧ last.t ∈ "/keyword" then t >> 1 + addback else t + addback)
 + "/br:(red.message)/br"
 + if isempty.unprocessed then "at end but expecting::(ending)"
else "Replaced:(dq(if place + 11 < n.input then unprocessed + "…" else unprocessed))with:(ending)to parse."

Function binary(R0:bindinfo, firsttoken:token, R1:bindinfo) bindinfo
let op = toword.firsttoken,
bindinfo(dict.R0, code.R0 + code.R1, types.R0 + types.R1, text.R0 + text.R1 + op + %.n.code.R1)

Function binaryops(
static:commonType
, R0:bindinfo
, R1:bindinfo
, rinfo:recoverInfo
) bindinfo
let input = input.rinfo
let place = place.rinfo
let parsestk = stk.rinfo,
if isempty.text.R1 then R0
else
 let dict = dict.R0
 for arg1code = code.R0, arg1type = types.R0, start = 1, ops = text.R1, arg2type ∈ types.R1
 do
  let types = arg1type + arg2type
  let op = [ops sub 1]
  let len = toint.ops sub 2,
  let arg2code = subseq(code.R1, start, start + len - 1),
  if op sub 1 ∈ "∧ ∨" ∧ types = [typeboolean, typeboolean] ∧ not.outText.static then
   let code =
    if op = "∧" then ifthenelse(arg1code, arg2code, [Litfalse], typeboolean)
    else ifthenelse(arg1code, [Littrue], arg2code, typeboolean),
   next(code, [typeboolean], start + len, ops << 2)
  else
   let idx = findindex("≠ ≥ ≤ ∉", op sub 1)
   let f =
    if idx > 4 then [lookupbysig(static, dict, [op sub 1], types, rinfo)]
    else
     let f1 = lookupbysig(static, dict, ["= < > ∈" sub idx], types, rinfo),
     if outText.static then [symbol(module.f1, op, paratypes.f1, resulttype.f1)]
     else [f1, NotOp],
   next(arg1code + arg2code + f, [resulttype.f sub 1], start + len, ops << 2),
 bindinfo(dict, arg1code, arg1type, "")

function strExp(
static:commonType
, R0:bindinfo
, str:seq.word
, forcecode:boolean
, expcode:seq.symbol
, exptype:mytype
, rinfo:recoverInfo
) bindinfo
let t = seqof.typeword,
if isempty.expcode then
 if isempty.code.R0 then
  if forcecode then bindinfo(dict.R0, [Words(text.R0 + str)], [t], "")
  else bindinfo(dict.R0, code.R0, types.R0, text.R0 + str)
 else if isempty.str then R0
 else
  let f = lookupbysig(static, dict.R0, "+", [t, t], rinfo),
  bindinfo(dict.R0, code.R0 + Words.str + f, [t], "")
else
 let f = lookupbysig(static, dict.R0, "+", [t, t], rinfo)
 let codeexp =
  if exptype = t then expcode
  else
   let cvt = lookupbysig(static, dict.R0, "%", [exptype], rinfo)
   assert resulttype.cvt = seqof.typeword report errormessage("Expected function:(cvt)to have return type of seq.word", rinfo),
   expcode + cvt,
 if isempty.code.R0 ∧ isempty.text.R0 ∧ not.outText.static then bindinfo(dict.R0, codeexp, [t], "")
 else
  let code1 = if isempty.code.R0 then [Words.text.R0] else code.R0,
  bindinfo(dict.R0, code1 + codeexp + f, [t], "")

Function ifExp(
static:commonType
, R0:bindinfo
, cond:bindinfo
, thenpart:bindinfo
, rinfo:recoverInfo
) bindinfo
assert(types.cond) sub 1 = typeboolean report errormessage("cond of if must be boolean but is:((types.cond) sub 1)", rinfo)
assert isempty.types.R0 ∨ types.R0 = types.thenpart report errormessage("then and else types are different", rinfo),
bindinfo(dict.R0, code.R0 + code.cond + Br2(1, 2) + code.thenpart + Exit, types.thenpart, "")

function ifExp(
static:commonType
, cond:bindinfo
, thenpart:bindinfo
, elseifpart:bindinfo
, elsepart:bindinfo
, rinfo:recoverInfo
) bindinfo
let t = ifExp(static, toAttribute(cond, ""), cond, thenpart, rinfo)
assert types.thenpart = types.elsepart
 ∧ (isempty.types.elseifpart ∨ types.elseifpart = types.thenpart) report errormessage("then and else types are different", rinfo),
bindinfo(
 dict.cond
 , [Start.(types.thenpart) sub 1]
 + code.t
 + code.elseifpart
 + (if outText.static then code.elsepart + EndBlock else code.elsepart + Exit + EndBlock)
 , types.elsepart
 , ""
)

function declarePara(d:symboldict, names:seq.word, types:seq.mytype) bindinfo
for dict = d, no = 1, t ∈ types do next(dict + Local(names sub no, t, no), no + 1),
bindinfo(dict, empty:seq.symbol, empty:seq.mytype, "")

function lookupbysig(
static:commonType
, dict:symboldict
, name:seq.word
, paratypes:seq.mytype
, rinfo:recoverInfo
) symbol
let sym3 =
 if n.name = 1 then symbol(internalmod, name, paratypes, typeint)
 else symbol4(internalmod, name sub 1, resolvetype(static, name << 1, rinfo), paratypes, typeint)
let f0 = lookupbysig(dict, sym3)
let f =
 if n.f0 < 2 then f0
 else
  for bound = empty:set.symbol, unbound = empty:set.symbol, sy ∈ toseq.f0
  do if isunbound.sy then next(bound, unbound + sy) else next(bound + sy, unbound),
  if isempty.bound ∧ not.isempty.unbound then{Allow multiple unbound with same signature}subseq(unbound, 1, 1)
  else bound
assert not.isempty.f report
 if n.name = 1 ∧ name sub 1 ∈ "if else then for" then errormessage("Syntax error", rinfo)
 else
  errormessage(
   "cannot find 1:(if n.name = 1 then name else [name sub 1, ":" sub 1] + name << 1)(:(for acc = "", @e ∈ paratypes do acc + %.@e + ",",
   acc >> 1))"
   , rinfo
  )
assert n.f = 1 report
 errormessage(
  "found more than one:(for acc = "", @e ∈ toseq.f do acc + library.module.@e + "." + %.@e,
  acc)"
  , rinfo
 )
let discard =
 for acc = 0, sym2 ∈ requires(dict, f sub 1)
 do
  let xxx = lookupbysig(dict, sym2)
  assert not.isempty.xxx ∨ isAbstract.module.f sub 1 report errormessage("using symbol:(f sub 1)requires unbound:(sym2)", rinfo),
  0,
 0,
f sub 1

Function addpara(
static:commonType
, name:seq.word
, ptype:bindinfo
, rinfo:recoverInfo
) bindinfo
let b = ptype
let paratype = resolvetype(static, text.ptype, rinfo)
assert isempty.lookupbysig(dict.b, name) ∨ name = ":" report errormessage("duplciate symbol::(name)", rinfo),
bindinfo(dict.b, empty:seq.symbol, [paratype], name)

Function addpara(
static:commonType
, b:bindinfo
, name:seq.word
, ptype:bindinfo
, rinfo:recoverInfo
) bindinfo
let paratype = resolvetype(static, text.ptype, rinfo)
assert isempty.lookupbysig(dict.b, name) ∨ name = ":" report errormessage("duplciate symbol::(name)", rinfo),
bindinfo(
 dict.b + Local(name sub 1, paratype, n.text.b + 1)
 , empty:seq.symbol
 , empty:seq.mytype
 , text.b + name
)

Function seqExp(static:commonType, R:bindinfo, rinfo:recoverInfo) bindinfo
let types = types.R
assert for acc = true, @e ∈ types do acc ∧ types sub 1 = @e,
acc report errormessage("types do not match in build", rinfo),
bindinfo(dict.R, code.R + Sequence(types sub 1, n.types), [seqof.types sub 1], "")

Function letExp(static:commonType, R:bindinfo, exp:bindinfo, rinfo:recoverInfo) bindinfo
let name = text.R
assert isempty.lookupbysig(dict.R, name) report errormessage("duplicate symbol::(name)", rinfo)
let newdict = dict.R + Local(name sub 1, (types.exp) sub 1, cardinality.dict.R),
bindinfo(newdict, code.R + code.exp + Define(name sub 1, cardinality.dict.R), types.exp, name)

Function bindlit2(static:commonType, R:bindinfo, rinfo:recoverInfo) bindinfo
assert not.isempty.text.R report "bindlit2"
let kind = hexOrDecimal?.(text.R) sub 1,
if kind ∈ "other" then
 let f = lookupbysig(static, dict.R, text.R, empty:seq.mytype, rinfo),
 bindinfo(dict.R, [f], [resulttype.f], "")
else
 let rt = if kind ∈ "word" then typeword else if kind ∈ "hex" then typebits else typeint,
 bindinfo(
  dict.R
  , [
   if outText.static then symbol(internalmod, text.R, empty:seq.mytype, rt)
   else
    let val = (text.R) sub 1,
    if kind ∈ "word" then Word.encodeword(decodeword.val << 1) else Lit.val
  ]
  , [rt]
  , ""
 )

Function unaryop(
static:commonType
, dict:symboldict
, rinfo:recoverInfo
, op:seq.word
, exp:bindinfo
) bindinfo
if op sub 1 = "process" sub 1 ∧ n.types.exp = 1 then
 let rt = resolvetype(types.static, %.(types.exp) sub 1) sub 1
 let processtype = processof.rt
 let dcws = deepcopyseqword,
 let newcode =
  [Fref.deepcopySym.rt, Fref.dcws, Fref.last.code.exp]
  + subseq(code.exp, 1, n.code.exp - 1)
  + [Lit.0, Fref.last.code.exp]
  + Record([typeint, typeint, typeint] + paratypes.last.code.exp + typeint + typeint)
  + symbol(builtinmod.rt, "createthreadZ", [typeptr], processtype),
 bindinfo(
  dict
  , if outText.static then code.exp + symbol(internalmod, "process", [rt], rt)
  else newcode
  , [processtype]
  , ""
 )
else if hexOrDecimal?.op sub 1 ∈ "hex decimal" ∧ n.code.exp = 1 then
 let dec =
  if outText.static then name.(code.exp) sub 1
  else
   assert kind.(code.exp) sub 1 = kint report errormessage("illformed real literal", rinfo),
   name.(code.exp) sub 1
 let makerealSymbol = symbol(moduleref."* real", "makereal", [seqof.typeword], typereal),
 bindinfo(dict, [Words(op + "." + dec), makerealSymbol], [typereal], "")
else
 let f = lookupbysig(static, dict, op, types.exp, rinfo),
 bindinfo(dict, code.exp + f, [resulttype.f], "")

function resolvetype(static:commonType, text:seq.word, rinfo:recoverInfo) mytype
let a = resolvetype(types.static, text)
assert not.isempty.a report errormessage("cannot resolve type:(text)", rinfo),
a sub 1

Function checktype(
static:commonType
, functype:bindinfo
, Declare:bindinfo
, exp:bindinfo
, rinfo:recoverInfo
) bindinfo
let returntype = resolvetype(static, text.functype, rinfo)
assert returntype = (types.exp) sub 1 report errormessage("function type of:(returntype)does not match expression type:((types.exp) sub 1)", rinfo),
bindinfo(dict.exp, mergeText(static, code.Declare, code.exp), empty:seq.mytype, "")

Function forSeqExp(
static:commonType
, accum0:bindinfo
, elename:seq.word
, theseq:bindinfo
, rinfo:recoverInfo
) bindinfo
let noseq = elename = "."
let oldnesting = lookupbysig(dict.accum0, "for")
let basetype = typebase.cardinality.dict.accum0
{we declare accumulators after all initial values are calculated since initial values may change size of symboldict. }
for accdict = dict.accum0, i = 1, name ∈ text.accum0
do
 assert isempty.lookupbysig(dict.accum0, [name]) report errormessage("duplicate symbol::(name)", rinfo)
 let z = Local(name, (types.accum0) sub i, cardinality.accdict),
 next(accdict + z, i + 1)
let seqtype =
 if noseq then seqof.typeint
 else
  let seqtype0 = (types.theseq) sub 1
  assert isempty.lookupbysig(accdict, elename) report errormessage("duplicate symbol::(elename)", rinfo),
  assert isseq.seqtype0 report errormessage("final expression in for list must be a sequence but it is of type::(seqtype0)", rinfo),
  seqtype0
{keep track so right next is used in nested fors}
let lastaccum = cardinality.accdict - 1
let elementSym = Local(elename sub 1, parameter.seqtype, lastaccum + 2)
let dict2 =
 accdict
 + Local(toword(lastaccum + 1), seqtype, lastaccum + 1)
 + elementSym
 + Local(toword(lastaccum + 3), typeint, lastaccum + 3)
 + Local(toword(lastaccum + 4), typeint, lastaccum + 4)
 + Local(toword(lastaccum + 2), typeint, lastaccum + 5)
let nextSym =
 symbol(moduleref("internallib $for", basetype), "next", types.accum0, basetype)
{assert not.noseq report %(types.accum0+parameter.seqtype)+"KLJ:"+text.accum0+elename}
bindinfo(
 addAccum(dict2, nextSym, basetype, oldnesting, elementSym)
 , if noseq then code.accum0 else code.accum0 + code.theseq
 , types.accum0 + parameter.seqtype
 , text.accum0 + elename
)

Function assertExp(
static:commonType
, cond:bindinfo
, exp:bindinfo
, rinfo:recoverInfo
) bindinfo
assert(types.cond) sub 1 = typeboolean report errormessage("condition in assert must be boolean in:", rinfo)
assert(types.exp) sub 1 = seqof.typeword report errormessage("report in assert must be seq of word in:", rinfo),
if outText.static then
 bindinfo(
  dict.cond
  , code.cond
  + code.exp
  + symbol(internalmod, "$assert", [typeboolean, seqof.typeword], typeint)
  , [typeint]
  , ""
 )
else
 let assertsym = symbol(internalmod, "assert", [seqof.typeword], typeint),
 bindinfo(
  dict.cond
  , [Start.typeint]
  + code.cond
  + Br2(1, 2)
  + Lit.0
  + Exit
  + code.exp
  + assertsym
  + Exit
  + EndBlock
  + Define("assert" sub 1, cardinality.dict.cond)
  , empty:seq.mytype
  , ""
 )

Function forbody(
static:commonType
, vars:bindinfo
, exitexp:bindinfo
, forbodyin:bindinfo
, rinfo:recoverInfo
) bindinfo
let textvars = text.vars
let codevars = code.vars
let typesvars = types.vars
let accumTypes = typesvars >> 1
let theseqtype = last.types.vars
let nowhile = code.exitexp = [Littrue]
let noseq = last.text.vars ∈ "."
let forbodytype = resulttype.lookupbysig(dict.vars, "for") sub 1
let forbody =
 if n.accumTypes = 1 ∧ forbodytype = (types.forbodyin) sub 1 then
  {handle next with single accumulator}
  bindinfo(dict.forbodyin, code.forbodyin >> 1, [accumTypes sub 1], text.forbodyin)
 else forbodyin
let actualbodytype = (types.forbody) sub 1
let checktypes =
 if (types.exitexp) sub 1 = typeboolean then
  {while type is OK. now check body type}
  if n.accumTypes > 1 then if forbodytype = actualbodytype then "" else "incorrect body type::(actualbodytype)"
  else if accumTypes sub 1 = actualbodytype then
   {body type is OK, now check to see if while clause is required}
   if noseq ∧ code.exitexp = [Littrue] then "While clause must be present and not equal to true when no sequence is specified."
   else ""
  else "Type of body expression:(actualbodytype)must match accumulator type:(accumTypes sub 1)"
 else "while expresssion type must be boolean"
assert isempty.checktypes report errormessage(checktypes, rinfo)
let newcode =
 if outText.static then
  codevars
  + code.exitexp
  + code.forbodyin
  + Words.text.vars
  + symbol(
   internalmod
   , "$fortext"
   , accumTypes
   + (if noseq then empty:seq.mytype else [theseqtype])
   + typeboolean
   + (types.forbody) sub 1
   + seqof.typeword
   , typeint
  )
 else
  let firstvar = toint.(%.parameter.forbodytype) sub 1
  let lastidx = Local(firstvar + n.accumTypes)
  let theseq = Local(value.lastidx + 2),
  let totallength = Local(value.lastidx + 3),
  if noseq then
   codevars
   + Loopblock(accumTypes, firstvar, typeint)
   + code.exitexp
   + Br2(2, 1)
   + Lit.0
   + Exit
   + code.forbody
   + (if n.accumTypes = 1 then [continue.1] else [Exit])
   + EndBlock
   + Define.value.totallength
  else
   let masterindex = Local(value.lastidx + 4)
   let reverse = name.module.last.codevars ∈ "seq1" ∧ name.last.codevars ∈ "reverse"
   let continue = if n.accumTypes = 1 then [masterindex, continue.2] else [Exit]
   let setElement =
    [
     lastidx
     , if reverse then Lit.-1 else Lit.1
     , PlusOp
     , Define.value.masterindex
     , theseq
     , masterindex
     , symIdxNB.theseqtype
     , Define(value.lastidx + 1)
    ],
   let part1 =
    if reverse then
     codevars >> 1
     + Define.value.theseq
     + theseq
     + GetSeqLength
     + Define.value.totallength
     + totallength
     + Lit.1
     + PlusOp
     + Loopblock(accumTypes + typeint, firstvar, typeint)
     + [lastidx, Lit.1, EqOp]
    else
     codevars
     + Define.value.theseq
     + theseq
     + GetSeqLength
     + Define.value.totallength
     + Lit.0
     + Loopblock(accumTypes + typeint, firstvar, typeint)
     + [lastidx, totallength, EqOp],
   part1
   + if nowhile then
    let seq? = last.code.forbody,
    [Br2(1, 2)]
    + Lit.0
    + Exit
    + setElement
    + code.forbody
    + continue
    + EndBlock
    + Define.value.totallength
   else
    [Br2(2, 1)]
    + setElement
    + code.exitexp
    + Br2(2, 1)
    + Lit.0
    + Exit
    + code.forbody
    + continue
    + EndBlock
    + Define.value.totallength,
bindinfo(restorenext.dict.vars, newcode, [typeint], "")

function mergeText(static:commonType, a:seq.symbol, b:seq.symbol) seq.symbol
if outText.static ∧ not.isempty.a ∧ not.isempty.b then a + b + symbol(internalmod, "$mergecode", [typeint, typeint], typeint)
else a + b

function endMark token totoken.encodeword.[char.254]

function firsttoken(r:recoverInfo) token (input.r) sub faili.r

function colon seq.word ":"

function genPEG(
seqElementType:token
, attributeType:bindinfo
, resultType:recoverInfo
, error:boolean
, common:commonType
, rinfo:recoverInfo
) seq.boolean
{commonName: common wordmap: colon totoken.colon sub 1, dq totoken.dq sub 1, totoken."$"sub 1}
[
 "Parser function Name(FPL)Type Declare' E" = checktype(common, $.3, $.4, $.5, rinfo)
 , "/ function Name Type Declare' E" = checktype(common, $.2, $.3, $.4, rinfo)
 , "String dq String' dq" = strExp(common, $.1, "", true, empty:seq.symbol, typeint, rinfo)
 , "* String' colon(E)"
 = strExp(common, $.0, "", true, code.$.1, (types.$.1) sub 1, rinfo)
 , "/ colon"
 = strExp(common, $.0, [toword.firsttoken.rinfo], false, empty:seq.symbol, typeint, rinfo)
 , "/ str2" = strExp(common, $.0, text.$.1, false, empty:seq.symbol, typeint, rinfo)
 , "+str2 ! dq ! colon any" = /All
 , "E Or" = $.1
 , "* EL', E" = bindinfo(dict.$.0, code.$.0 + code.$.1, types.$.0 + types.$.1, "")
 , "Or And Or'" = binaryops(common, $.1, $.2, rinfo)
 , "* Or' ∨ And" = binary($.0, firsttoken.rinfo, $.1)
 , "And Compare And'" = binaryops(common, $.1, $.2, rinfo)
 , "* And' ∧ Compare" = binary($.0, firsttoken.rinfo, $.1)
 , "Compare Sum Compare'" = binaryops(common, $.1, $.2, rinfo)
 , "* Compare' > Sum" = binary($.0, firsttoken.rinfo, $.1)
 , "Sum Product Sum'" = binaryops(common, $.1, $.2, rinfo)
 , "* Sum'+Product" = binary($.0, firsttoken.rinfo, $.1)
 , "Product Unary Product'" = binaryops(common, $.1, $.2, rinfo)
 , "* Product' * Unary" = binary($.0, firsttoken.rinfo, $.1)
 , "Unary-Unary" = unaryop(common, dict.$.1, rinfo, [toword.firsttoken.rinfo], $.1)
 , "/ Id.Unary" = unaryop(common, dict.$.1, {place-1?}rinfo, text.$.1, $.2)
 , "/{N}Unary"
 = (if outText.common then
  bindinfo(
   dict.$.2
   , [Words.text.$.1]
   + code.$.2
   + symbol(internalmod, "{", [seqof.typeword, (types.$.2) sub 1], (types.$.2) sub 1)
   , types.$.2
   , ""
  )
 else $.2)
 , "/ Power" = $.1
 , "Power Atom Power'" = binaryops(common, $.1, $.2, rinfo)
 , "* Power' sup Unary" = binary($.0, firsttoken.rinfo, $.1)
 , "Atom(E)"
 = (if outText.common then bindinfo(dict.$.1, code.$.1 + symbol(internalmod, "(", [typeint], typeint), types.$.1, "")
 else $.1)
 , "/[E EL']"
 = seqExp(common, bindinfo(dict.$.1, code.$.1 + code.$.2, types.$.1 + types.$.2, ""), rinfo)
 , "/ String" = $.1
 , "/ Declare Declare' E"
 = bindinfo(
  dict.$.0
  , mergeText(common, mergeText(common, code.$.1, code.$.2), code.$.3)
  , types.$.3
  , ""
 )
 , "/ if E then E IF else E" = ifExp(common, $.1, $.2, $.3, $.4, rinfo)
 , "/ Name(E EL')"
 = unaryop(
  common
  , dict.$.1
  , rinfo
  , text.$.1
  , bindinfo(dict.$.2, code.$.2 + code.$.3, types.$.2 + types.$.3, "")
 )
 , "/ Name" = bindlit2(common, $.1, rinfo)
 , "Name Id colon Type"
 = bindinfo(dict.$.1, empty:seq.symbol, empty:seq.mytype, text.$.1 + text.$.2)
 , "/ Id" = $.1
 , "Id ! dq any" = $.1
 , "comma?," = $.0
 , "/" = $.0
 , "* IF else if E then E" = ifExp(common, $.0, $.1, $.2, rinfo)
 , "Type Id.Type"
 = bindinfo(dict.$.2, empty:seq.symbol, empty:seq.mytype, text.$.1 + "." + text.$.2)
 , "/ Id" = $.1
 , "Declare let any = E comma?" = letExp(common, $.1, $.2, rinfo)
 , "/ assert E report E comma?" = assertExp(common, $.1, $.2, rinfo)
 , "/{N}comma?"
 = (if outText.common then
  bindinfo(
   dict.$.0
   , code.$.0 + Words.text.$.1 + symbol(internalmod, "{", [seqof.typeword], typeint)
   , empty:seq.mytype
   , ""
  )
 else $.0)
 , "/ for ForDeclare do E comma?"
 = forbody(common, $.1, bindinfo(dict.$.0, [Littrue], [typeboolean], ""), $.2, rinfo)
 , "/ for ForDeclare while E do E comma?" = forbody(common, $.1, $.2, $.3, rinfo)
 , "ForDeclare AccumList, any ∈ E" = forSeqExp(common, $.1, text.$.2, $.3, rinfo)
 , "/ AccumList" = forSeqExp(common, $.1, ".", $.1, rinfo)
 , "AccumList ! while any = E AccumList'"
 = bindinfo(dict.$.0, code.$.2 + code.$.3, types.$.2 + types.$.3, text.$.1 + text.$.3)
 , "* AccumList', any = E"
 = bindinfo(dict.$.0, code.$.0 + code.$.2, types.$.0 + types.$.2, text.$.0 + text.$.1)
 , "* Declare' Declare"
 = bindinfo(dict.$.1, mergeText(common, code.$.0, code.$.1), empty:seq.mytype, "")
 , "FPL FP FPL'" = declarePara(dict.$.1, text.$.1 + text.$.2, types.$.1 + types.$.2)
 , "* FPL', FP"
 = bindinfo(dict.$.0, empty:seq.symbol, types.$.0 + types.$.1, text.$.0 + text.$.1)
 , "FP any colon Type" = addpara(common, text.$.1, $.2, rinfo)
 , "/ Type" = addpara(common, $.0, ":", $.1, rinfo)
 , "* N{N}" = /All
 , "/ !}any" = /All
]

<<<< Below is auto generated code >>>>

/br Non-terminals:AccumList AccumList' And And' Atom Compare Compare' Declare Declare' E EL' FP FPL FPL' ForDeclare IF Id N Name Or Or' Parser Power Power' Product Product' String String' Sum Sum' Type Unary comma? str2 /br
Terminals:()*+,-.= >[]any assert colon do dq else for function if let report sup then while{}∈ ∧ ∨ /br
Parser ← function Name(FPL)Type Declare' E / function Name Type Declare' E /br
String ← dq String' dq /br
* String' ← colon(E)/ colon / str2 /br
+str2 ← ! dq ! colon any /br
E ← Or /br
* EL' ←, E /br
Or ← And Or' /br
* Or' ← ∨ And /br
And ← Compare And' /br
* And' ← ∧ Compare /br
Compare ← Sum Compare' /br
* Compare' ← > Sum /br
Sum ← Product Sum' /br
* Sum' ←+Product /br
Product ← Unary Product' /br
* Product' ← * Unary /br
Unary ←-Unary / Id.Unary /{N}Unary / Power /br
Power ← Atom Power' /br
* Power' ← sup Unary /br
Atom ←(E)/[E EL']/ String / Declare Declare' E / if E then E IF else E / Name(E EL')/ Name /br
Name ← Id colon Type / Id /br
Id ← ! dq any /br
comma? ←, / /br
* IF ← else if E then E /br
Type ← Id.Type / Id /br
Declare ← let any = E comma? / assert E report E comma? /{N}comma? / for ForDeclare do E comma? / for ForDeclare while E do E comma? /br
ForDeclare ← AccumList, any ∈ E / AccumList /br
AccumList ← ! while any = E AccumList' /br
* AccumList' ←, any = E /br
* Declare' ← Declare /br
FPL ← FP FPL' /br
* FPL' ←, FP /br
FP ← any colon Type / Type /br
* N ←{N}/ !}any

function action(
partno:int
, R:seq.bindinfo
, common:commonType
, rinfo:recoverInfo
) bindinfo
if partno = 2 then checktype(common, R sub (n.R - 2), R sub (n.R - 1), R sub n.R, rinfo)
else if partno = 3 then checktype(common, R sub (n.R - 2), R sub (n.R - 1), R sub n.R, rinfo)
else if partno = 4 then strExp(common, R sub n.R, "", true, empty:seq.symbol, typeint, rinfo)
else if partno = 5 then strExp(common, R sub (n.R - 1), "", true, code.R sub n.R, (types.R sub n.R) sub 1, rinfo)
else if partno = 6 then strExp(common, R sub n.R, [toword.firsttoken.rinfo], false, empty:seq.symbol, typeint, rinfo)
else if partno = 7 then strExp(common, R sub (n.R - 1), text.R sub n.R, false, empty:seq.symbol, typeint, rinfo)
else if partno = 9 then R sub n.R
else if partno = 10 then
 bindinfo(
  dict.R sub (n.R - 1)
  , code.R sub (n.R - 1) + code.R sub n.R
  , types.R sub (n.R - 1) + types.R sub n.R
  , ""
 )
else if partno = 11 then binaryops(common, R sub (n.R - 1), R sub n.R, rinfo)
else if partno = 12 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 13 then binaryops(common, R sub (n.R - 1), R sub n.R, rinfo)
else if partno = 14 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 15 then binaryops(common, R sub (n.R - 1), R sub n.R, rinfo)
else if partno = 16 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 17 then binaryops(common, R sub (n.R - 1), R sub n.R, rinfo)
else if partno = 18 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 19 then binaryops(common, R sub (n.R - 1), R sub n.R, rinfo)
else if partno = 20 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 21 then unaryop(common, dict.R sub n.R, rinfo, [toword.firsttoken.rinfo], R sub n.R)
else if partno = 22 then unaryop(common, dict.R sub (n.R - 1), {place-1?}rinfo, text.R sub (n.R - 1), R sub n.R)
else if partno = 23 then
 if outText.common then
  bindinfo(
   dict.R sub n.R
   , [Words.text.R sub (n.R - 1)]
   + code.R sub n.R
   + symbol(internalmod, "{", [seqof.typeword, (types.R sub n.R) sub 1], (types.R sub n.R) sub 1)
   , types.R sub n.R
   , ""
  )
 else R sub n.R
else if partno = 24 then R sub n.R
else if partno = 25 then binaryops(common, R sub (n.R - 1), R sub n.R, rinfo)
else if partno = 26 then binary(R sub (n.R - 1), firsttoken.rinfo, R sub n.R)
else if partno = 27 then
 if outText.common then
  bindinfo(
   dict.R sub n.R
   , code.R sub n.R + symbol(internalmod, "(", [typeint], typeint)
   , types.R sub n.R
   , ""
  )
 else R sub n.R
else if partno = 28 then
 seqExp(
  common
  , bindinfo(
   dict.R sub (n.R - 1)
   , code.R sub (n.R - 1) + code.R sub n.R
   , types.R sub (n.R - 1) + types.R sub n.R
   , ""
  )
  , rinfo
 )
else if partno = 29 then R sub n.R
else if partno = 30 then
 bindinfo(
  dict.R sub (n.R - 3)
  , mergeText(
   common
   , mergeText(common, code.R sub (n.R - 2), code.R sub (n.R - 1))
   , code.R sub n.R
  )
  , types.R sub n.R
  , ""
 )
else if partno = 31 then ifExp(common, R sub (n.R - 3), R sub (n.R - 2), R sub (n.R - 1), R sub n.R, rinfo)
else if partno = 32 then
 unaryop(
  common
  , dict.R sub (n.R - 2)
  , rinfo
  , text.R sub (n.R - 2)
  , bindinfo(
   dict.R sub (n.R - 1)
   , code.R sub (n.R - 1) + code.R sub n.R
   , types.R sub (n.R - 1) + types.R sub n.R
   , ""
  )
 )
else if partno = 33 then bindlit2(common, R sub n.R, rinfo)
else if partno = 34 then
 bindinfo(
  dict.R sub (n.R - 1)
  , empty:seq.symbol
  , empty:seq.mytype
  , text.R sub (n.R - 1) + text.R sub n.R
 )
else if partno = 35 then R sub n.R
else if partno = 36 then R sub n.R
else if partno = 37 then R sub n.R
else if partno = 38 then R sub n.R
else if partno = 39 then ifExp(common, R sub (n.R - 2), R sub (n.R - 1), R sub n.R, rinfo)
else if partno = 40 then
 bindinfo(
  dict.R sub n.R
  , empty:seq.symbol
  , empty:seq.mytype
  , text.R sub (n.R - 1) + "." + text.R sub n.R
 )
else if partno = 41 then R sub n.R
else if partno = 42 then letExp(common, R sub (n.R - 2), R sub (n.R - 1), rinfo)
else if partno = 43 then assertExp(common, R sub (n.R - 2), R sub (n.R - 1), rinfo)
else if partno = 44 then
 if outText.common then
  bindinfo(
   dict.R sub (n.R - 2)
   , code.R sub (n.R - 2)
   + Words.text.R sub (n.R - 1)
   + symbol(internalmod, "{", [seqof.typeword], typeint)
   , empty:seq.mytype
   , ""
  )
 else R sub (n.R - 2)
else if partno = 45 then
 forbody(
  common
  , R sub (n.R - 2)
  , bindinfo(dict.R sub (n.R - 3), [Littrue], [typeboolean], "")
  , R sub (n.R - 1)
  , rinfo
 )
else if partno = 46 then forbody(common, R sub (n.R - 3), R sub (n.R - 2), R sub (n.R - 1), rinfo)
else if partno = 47 then forSeqExp(common, R sub (n.R - 2), text.R sub (n.R - 1), R sub n.R, rinfo)
else if partno = 48 then forSeqExp(common, R sub n.R, ".", R sub n.R, rinfo)
else if partno = 49 then
 bindinfo(
  dict.R sub (n.R - 3)
  , code.R sub (n.R - 1) + code.R sub n.R
  , types.R sub (n.R - 1) + types.R sub n.R
  , text.R sub (n.R - 2) + text.R sub n.R
 )
else if partno = 50 then
 bindinfo(
  dict.R sub (n.R - 2)
  , code.R sub (n.R - 2) + code.R sub n.R
  , types.R sub (n.R - 2) + types.R sub n.R
  , text.R sub (n.R - 2) + text.R sub (n.R - 1)
 )
else if partno = 51 then
 bindinfo(
  dict.R sub n.R
  , mergeText(common, code.R sub (n.R - 1), code.R sub n.R)
  , empty:seq.mytype
  , ""
 )
else if partno = 52 then
 declarePara(
  dict.R sub (n.R - 1)
  , text.R sub (n.R - 1) + text.R sub n.R
  , types.R sub (n.R - 1) + types.R sub n.R
 )
else if partno = 53 then
 bindinfo(
  dict.R sub (n.R - 1)
  , empty:seq.symbol
  , types.R sub (n.R - 1) + types.R sub n.R
  , text.R sub (n.R - 1) + text.R sub n.R
 )
else if partno = 54 then addpara(common, text.R sub (n.R - 1), R sub n.R, rinfo)
else if partno = 55 then addpara(common, R sub (n.R - 1), ":", R sub n.R, rinfo)
else R sub 1

function mytable seq.tblEle
[
 {1}tblEle(NT.T'.2, totoken."?" sub 1, Match, Failure, "")
 , {2}tblEle(T', totoken."function" sub 1, NT.3, Fail, "function Name(FPL)Type E")
 , {3}tblEle(NT.88, totoken."Name" sub 1, T'.4, Fail, "Name(FPL)Type E")
 , {4}tblEle(T', totoken."(" sub 1, NT.5, NT.12, "(FPL)Type E")
 , {5}tblEle(NT.146, totoken."FPL" sub 1, T.6, T.10, "FPL)Type E")
 , {6}tblEle(T, totoken.")" sub 1, NT.7, T.10, ")Type E")
 , {7}tblEle(NT.100, totoken."Type" sub 1, NT.8, T.10, "Type E")
 , {8}tblEle(NT.145, totoken."Declare'" sub 1, NT.9, T.10, "E")
 , {9}tblEle(NT.27, totoken."E" sub 1, Reduce.2, T.10, "E")
 , {10}tblEle(T, totoken."function" sub 1, NT.11, Fail, "function Name Type E")
 , {11}tblEle(NT.88, totoken."Name" sub 1, NT.12, Fail, "Name Type E")
 , {12}tblEle(NT.100, totoken."Type" sub 1, NT.13, Fail, "Type E")
 , {13}tblEle(NT.145, totoken."Declare'" sub 1, NT.14, Fail, "E")
 , {14}tblEle(NT.27, totoken."E" sub 1, Reduce.3, Fail, "E")
 , {15}tblEle(T, totoken.dq sub 1, NT.16, Fail, "dq dq")
 , {16}tblEle(NT.T'.18, totoken."String'" sub 1, T.17, Fail, "dq")
 , {17}tblEle(T, totoken.dq sub 1, Reduce.4, Fail, "dq")
 , {18}tblEle(T', totoken.colon sub 1, T.19, NT.23, "colon(E)")
 , {19}tblEle(T, totoken."(" sub 1, NT.20, T'.22, "(E)")
 , {20}tblEle(NT.27, totoken."E" sub 1, T.21, T'.22, "E)")
 , {21}tblEle(T, totoken.")" sub 1, Reduce*(5, T'.18), T'.22, ")")
 , {22}tblEle(T', totoken.colon sub 1, Reduce*(6, T'.18), NT.23, "colon")
 , {23}tblEle(NT.!T.24, totoken."str2" sub 1, Reduce*(7, T'.18), Success*, "str2")
 , {24}tblEle(!T, totoken.dq sub 1, Fail, !T.25, "dq any")
 , {25}tblEle(!T, totoken.colon sub 1, Fail, MatchAny.26, "colon any")
 , {26}tblEle(MatchAny, totoken."?" sub 1, Discard*.!T.159, Fail, "any")
 , {27}tblEle(NT.30, totoken."Or" sub 1, Reduce.9, Fail, "Or")
 , {28}tblEle(T, totoken."," sub 1, NT.29, Success*, ", E")
 , {29}tblEle(NT.27, totoken."E" sub 1, Reduce*(10, T.28), Success*, "E")
 , {30}tblEle(NT.34, totoken."And" sub 1, NT.31, Fail, "And")
 , {31}tblEle(NT.T.32, totoken."Or'" sub 1, Reduce.11, Fail, "")
 , {32}tblEle(T, totoken."∨" sub 1, NT.33, Success*, "∨ And")
 , {33}tblEle(NT.34, totoken."And" sub 1, Reduce*(12, T.32), Success*, "And")
 , {34}tblEle(NT.38, totoken."Compare" sub 1, NT.35, Fail, "Compare")
 , {35}tblEle(NT.T.36, totoken."And'" sub 1, Reduce.13, Fail, "")
 , {36}tblEle(T, totoken."∧" sub 1, NT.37, Success*, "∧ Compare")
 , {37}tblEle(NT.38, totoken."Compare" sub 1, Reduce*(14, T.36), Success*, "Compare")
 , {38}tblEle(NT.42, totoken."Sum" sub 1, NT.39, Fail, "Sum")
 , {39}tblEle(NT.T.40, totoken."Compare'" sub 1, Reduce.15, Fail, "")
 , {40}tblEle(T, totoken.">" sub 1, NT.41, Success*, "> Sum")
 , {41}tblEle(NT.42, totoken."Sum" sub 1, Reduce*(16, T.40), Success*, "Sum")
 , {42}tblEle(NT.46, totoken."Product" sub 1, NT.43, Fail, "Product")
 , {43}tblEle(NT.T.44, totoken."Sum'" sub 1, Reduce.17, Fail, "")
 , {44}tblEle(T, totoken."+" sub 1, NT.45, Success*, "+Product")
 , {45}tblEle(NT.46, totoken."Product" sub 1, Reduce*(18, T.44), Success*, "Product")
 , {46}tblEle(NT.T'.50, totoken."Unary" sub 1, NT.47, Fail, "Unary")
 , {47}tblEle(NT.T.48, totoken."Product'" sub 1, Reduce.19, Fail, "")
 , {48}tblEle(T, totoken."*" sub 1, NT.49, Success*, "* Unary")
 , {49}tblEle(NT.T'.50, totoken."Unary" sub 1, Reduce*(20, T.48), Success*, "Unary")
 , {50}tblEle(T', totoken."-" sub 1, NT.51, NT.52, "-Unary")
 , {51}tblEle(NT.T'.50, totoken."Unary" sub 1, Reduce.21, NT.52, "Unary")
 , {52}tblEle(NT.!T.92, totoken."Id" sub 1, T.53, T'.55, "Id.Unary")
 , {53}tblEle(T, totoken."." sub 1, NT.54, T'.55, ".Unary")
 , {54}tblEle(NT.T'.50, totoken."Unary" sub 1, Reduce.22, T'.55, "Unary")
 , {55}tblEle(T', totoken."{" sub 1, NT.56, NT.59, "{}Unary")
 , {56}tblEle(NT.T.154, totoken."N" sub 1, T.57, NT.59, "}Unary")
 , {57}tblEle(T, totoken."}" sub 1, NT.58, NT.59, "}Unary")
 , {58}tblEle(NT.T'.50, totoken."Unary" sub 1, Reduce.23, NT.59, "Unary")
 , {59}tblEle(NT.60, totoken."Power" sub 1, Reduce.24, Fail, "Power")
 , {60}tblEle(NT.T'.64, totoken."Atom" sub 1, NT.61, Fail, "Atom")
 , {61}tblEle(NT.T.62, totoken."Power'" sub 1, Reduce.25, Fail, "")
 , {62}tblEle(T, totoken."sup" sub 1, NT.63, Success*, "sup Unary")
 , {63}tblEle(NT.T'.50, totoken."Unary" sub 1, Reduce*(26, T.62), Success*, "Unary")
 , {64}tblEle(T', totoken."(" sub 1, NT.65, T'.67, "(E)")
 , {65}tblEle(NT.27, totoken."E" sub 1, T.66, T'.67, "E)")
 , {66}tblEle(T, totoken.")" sub 1, Reduce.27, T'.67, ")")
 , {67}tblEle(T', totoken."[" sub 1, NT.68, NT.71, "[E]")
 , {68}tblEle(NT.27, totoken."E" sub 1, NT.69, NT.71, "E]")
 , {69}tblEle(NT.T.28, totoken."EL'" sub 1, T.70, NT.71, "]")
 , {70}tblEle(T, totoken."]" sub 1, Reduce.28, NT.71, "]")
 , {71}tblEle(NT.T.15, totoken."String" sub 1, Reduce.29, NT.72, "String")
 , {72}tblEle(NT.T'.104, totoken."Declare" sub 1, NT.73, T'.75, "Declare E")
 , {73}tblEle(NT.145, totoken."Declare'" sub 1, NT.74, T'.75, "E")
 , {74}tblEle(NT.27, totoken."E" sub 1, Reduce.30, T'.75, "E")
 , {75}tblEle(T', totoken."if" sub 1, NT.76, NT.82, "if E then E else E")
 , {76}tblEle(NT.27, totoken."E" sub 1, T.77, NT.82, "E then E else E")
 , {77}tblEle(T, totoken."then" sub 1, NT.78, NT.82, "then E else E")
 , {78}tblEle(NT.27, totoken."E" sub 1, NT.79, NT.82, "E else E")
 , {79}tblEle(NT.T.95, totoken."IF" sub 1, T.80, NT.82, "else E")
 , {80}tblEle(T, totoken."else" sub 1, NT.81, NT.82, "else E")
 , {81}tblEle(NT.27, totoken."E" sub 1, Reduce.31, NT.82, "E")
 , {82}tblEle(NT.88, totoken."Name" sub 1, T.83, Fail, "Name(E)")
 , {83}tblEle(T, totoken."(" sub 1, NT.84, NT.87, "(E)")
 , {84}tblEle(NT.27, totoken."E" sub 1, NT.85, NT.87, "E)")
 , {85}tblEle(NT.T.28, totoken."EL'" sub 1, T.86, NT.87, ")")
 , {86}tblEle(T, totoken.")" sub 1, Reduce.32, NT.87, ")")
 , {87}tblEle(NT.88, totoken."Name" sub 1, Reduce.33, Fail, "Name")
 , {88}tblEle(NT.!T.92, totoken."Id" sub 1, T.89, Fail, "Id colon Type")
 , {89}tblEle(T, totoken.colon sub 1, NT.90, NT.91, "colon Type")
 , {90}tblEle(NT.100, totoken."Type" sub 1, Reduce.34, NT.91, "Type")
 , {91}tblEle(NT.!T.92, totoken."Id" sub 1, Reduce.35, Fail, "Id")
 , {92}tblEle(!T, totoken.dq sub 1, Fail, MatchAny.93, "dq any")
 , {93}tblEle(MatchAny, totoken."?" sub 1, Reduce.36, Fail, "any")
 , {94}tblEle(T, totoken."," sub 1, Reduce.37, Reduce.38, ",")
 , {95}tblEle(T, totoken."else" sub 1, T.96, Success*, "else if E then E")
 , {96}tblEle(T, totoken."if" sub 1, NT.97, Success*, "if E then E")
 , {97}tblEle(NT.27, totoken."E" sub 1, T.98, Success*, "E then E")
 , {98}tblEle(T, totoken."then" sub 1, NT.99, Success*, "then E")
 , {99}tblEle(NT.27, totoken."E" sub 1, Reduce*(39, T.95), Success*, "E")
 , {100}tblEle(NT.!T.92, totoken."Id" sub 1, T.101, Fail, "Id.Type")
 , {101}tblEle(T, totoken."." sub 1, NT.102, NT.103, ".Type")
 , {102}tblEle(NT.100, totoken."Type" sub 1, Reduce.40, NT.103, "Type")
 , {103}tblEle(NT.!T.92, totoken."Id" sub 1, Reduce.41, Fail, "Id")
 , {104}tblEle(T', totoken."let" sub 1, MatchAny.105, T'.109, "let any = E")
 , {105}tblEle(MatchAny, totoken."?" sub 1, T.106, T'.109, "any = E")
 , {106}tblEle(T, totoken."=" sub 1, NT.107, T'.109, "= E")
 , {107}tblEle(NT.27, totoken."E" sub 1, NT.108, T'.109, "E")
 , {108}tblEle(NT.T.94, totoken."comma?" sub 1, Reduce.42, T'.109, "")
 , {109}tblEle(T', totoken."assert" sub 1, NT.110, T'.114, "assert E report E")
 , {110}tblEle(NT.27, totoken."E" sub 1, T.111, T'.114, "E report E")
 , {111}tblEle(T, totoken."report" sub 1, NT.112, T'.114, "report E")
 , {112}tblEle(NT.27, totoken."E" sub 1, NT.113, T'.114, "E")
 , {113}tblEle(NT.T.94, totoken."comma?" sub 1, Reduce.43, T'.114, "")
 , {114}tblEle(T', totoken."{" sub 1, NT.115, T'.118, "{}")
 , {115}tblEle(NT.T.154, totoken."N" sub 1, T.116, T'.118, "}")
 , {116}tblEle(T, totoken."}" sub 1, NT.117, T'.118, "}")
 , {117}tblEle(NT.T.94, totoken."comma?" sub 1, Reduce.44, T'.118, "")
 , {118}tblEle(T', totoken."for" sub 1, NT.119, Fail, "for ForDeclare do E")
 , {119}tblEle(NT.130, totoken."ForDeclare" sub 1, T'.120, Fail, "ForDeclare do E")
 , {120}tblEle(T', totoken."do" sub 1, NT.121, T.125, "do E")
 , {121}tblEle(NT.27, totoken."E" sub 1, NT.122, T.123, "E")
 , {122}tblEle(NT.T.94, totoken."comma?" sub 1, Reduce.45, T.123, "")
 , {123}tblEle(T, totoken."for" sub 1, NT.124, Fail, "for ForDeclare while E do E")
 , {124}tblEle(NT.130, totoken."ForDeclare" sub 1, T.125, Fail, "ForDeclare while E do E")
 , {125}tblEle(T, totoken."while" sub 1, NT.126, Fail, "while E do E")
 , {126}tblEle(NT.27, totoken."E" sub 1, T.127, Fail, "E do E")
 , {127}tblEle(T, totoken."do" sub 1, NT.128, Fail, "do E")
 , {128}tblEle(NT.27, totoken."E" sub 1, NT.129, Fail, "E")
 , {129}tblEle(NT.T.94, totoken."comma?" sub 1, Reduce.46, Fail, "")
 , {130}tblEle(NT.!T.136, totoken."AccumList" sub 1, T.131, Fail, "AccumList, any ∈ E")
 , {131}tblEle(T, totoken."," sub 1, MatchAny.132, NT.135, ", any ∈ E")
 , {132}tblEle(MatchAny, totoken."?" sub 1, T.133, NT.135, "any ∈ E")
 , {133}tblEle(T, totoken."∈" sub 1, NT.134, NT.135, "∈ E")
 , {134}tblEle(NT.27, totoken."E" sub 1, Reduce.47, NT.135, "E")
 , {135}tblEle(NT.!T.136, totoken."AccumList" sub 1, Reduce.48, Fail, "AccumList")
 , {136}tblEle(!T, totoken."while" sub 1, Fail, MatchAny.137, "while any = E")
 , {137}tblEle(MatchAny, totoken."?" sub 1, T.138, Fail, "any = E")
 , {138}tblEle(T, totoken."=" sub 1, NT.139, Fail, "= E")
 , {139}tblEle(NT.27, totoken."E" sub 1, NT.140, Fail, "E")
 , {140}tblEle(NT.T.141, totoken."AccumList'" sub 1, Reduce.49, Fail, "")
 , {141}tblEle(T, totoken."," sub 1, MatchAny.142, Success*, ", any = E")
 , {142}tblEle(MatchAny, totoken."?" sub 1, T.143, Success*, "any = E")
 , {143}tblEle(T, totoken."=" sub 1, NT.144, Success*, "= E")
 , {144}tblEle(NT.27, totoken."E" sub 1, Reduce*(50, T.141), Success*, "E")
 , {145}
 tblEle(NT.T'.104, totoken."Declare" sub 1, Reduce*(51, NT.145), Success*, "Declare")
 , {146}tblEle(NT.MatchAny.150, totoken."FP" sub 1, NT.147, Fail, "FP")
 , {147}tblEle(NT.T.148, totoken."FPL'" sub 1, Reduce.52, Fail, "")
 , {148}tblEle(T, totoken."," sub 1, NT.149, Success*, ", FP")
 , {149}tblEle(NT.MatchAny.150, totoken."FP" sub 1, Reduce*(53, T.148), Success*, "FP")
 , {150}tblEle(MatchAny, totoken."?" sub 1, T.151, NT.153, "any colon Type")
 , {151}tblEle(T, totoken.colon sub 1, NT.152, NT.153, "colon Type")
 , {152}tblEle(NT.100, totoken."Type" sub 1, Reduce.54, NT.153, "Type")
 , {153}tblEle(NT.100, totoken."Type" sub 1, Reduce.55, Fail, "Type")
 , {154}tblEle(T, totoken."{" sub 1, NT.155, !T.157, "{}")
 , {155}tblEle(NT.T.154, totoken."N" sub 1, T.156, !T.157, "}")
 , {156}tblEle(T, totoken."}" sub 1, Discard*.T.154, !T.157, "}")
 , {157}tblEle(!T, totoken."}" sub 1, All, MatchAny.158, "}any")
 , {158}tblEle(MatchAny, totoken."?" sub 1, Discard*.T.154, All, "any")
 , {159}tblEle(!T, totoken.dq sub 1, All, !T.160, "dq any")
 , {160}tblEle(!T, totoken.colon sub 1, All, MatchAny.161, "colon any")
 , {161}tblEle(MatchAny, totoken."?" sub 1, Discard*.!T.159, All, "any")
]

function =(seq.word, bindinfo) boolean true

function $(int) bindinfo empty:seq.bindinfo sub 1

use standard

use seq.tblEle

use seq1.frame

use stack.frame

use seq1.bindinfo

use PEGrules

type tblEle is action:state, match:token, Sstate:state, Fstate:state, recover:seq.word

function recoveryEnding(rinfo:recoverInfo) seq.word
for acc = "", frame ∈ reverse.toseq.stk.rinfo
do
 if action.Sstate.frame ∈ [T, T', NT] then acc + recover.mytable sub index.Sstate.frame
 else acc,
acc

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.bindinfo
, faili:int
, failresult:seq.bindinfo

type recoverInfo is stk:stack.frame, input:seq.token, place:int, faili:int

Function status(a:recoverInfo) word
if Sstate.top.stk.a ≠ Match then 'Failed
else if place.a = {length of input}faili.top.stk.a then 'Match
else 'MatchPrefix

Function result(a:recoverInfo) bindinfo
let t = result.top.stk.a,
t sub n.t

function parse(myinput0:seq.token, initAttr:bindinfo, common:commonType) recoverInfo
let myinput = packed(myinput0 + endMark)
let packedTable = packed.mytable
for
 rinfo = recoverInfo(empty:stack.frame, myinput, 0, 1)
 , stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = myinput sub 1
 , result = [initAttr]
 , faili = 1
 , failresult = [initAttr]
while toint.state > toint.Match
do
 let actionState = action.state,
 if actionState = Fail then
  {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
  let top = top.stk,
  if toint.action.Fstate.top ≥ toint.S' then
   let newi = i.top,
   next(
    rinfo
    , pop.stk
    , nextState.Fstate.top
    , newi
    , idxNB(myinput, newi)
    , result.top
    , faili.top
    , failresult.top
   )
  else
   next(
    rinfo
    , pop.stk
    , Fstate.top
    , faili.top
    , idxNB(myinput, faili.top)
    , failresult.top
    , faili.top
    , failresult.top
   )
 else if actionState = Success* then
  {goto Sstate.top.stk, pop.stk, keep result}
  let top = top.stk,
  next(rinfo, pop.stk, Sstate.top, i, inputi, result.top + result, faili.top, failresult.top)
 else if actionState = Discard* then
  let top = top.stk
  let newrinfo = if i > place.rinfo then recoverInfo(stk, myinput, i, faili) else rinfo,
  next(newrinfo, stk, nextState.state, i, inputi, result.top, i, result.top)
 else if actionState = All then
  let top = top.stk
  let att = [toAttribute(result sub n.result, subseq(myinput, i.top, i - 1))],
  next(rinfo, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
 else if actionState = Lambda then
  let newrinfo = if i > place.rinfo then recoverInfo(stk, myinput, i, faili) else rinfo
  let att = [action(reduceNo.state, result, common, newrinfo)],
  next(newrinfo, stk, nextState2.state, i, inputi, result + att, faili, failresult)
 else if actionState = Reduce then
  let top = top.stk
  let newrinfo =
   if i > place.rinfo ∨ faili ≠ faili.rinfo then recoverInfo(stk, myinput, i, faili)
   else rinfo,
  let att = [action(reduceNo.state, result, common, newrinfo)],
  next(newrinfo, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
 else if actionState = Reduce* then
  let newrinfo =
   if i > place.rinfo ∨ faili ≠ faili.rinfo then recoverInfo(stk, myinput, i, faili)
   else rinfo
  let att = [action(reduceNo.state, result, common, newrinfo)],
  let top = top.stk,
  next(newrinfo, stk, nextState.state, i, inputi, att, i, att)
 else if actionState = !Reduce then
  let top = top.stk
  let ini = idxNB(myinput, faili.top),
  next(rinfo, pop.stk, Fstate.top, faili.top, ini, failresult.top, faili.top, failresult.top)
 else if actionState = !Fail then
  let top = top.stk
  let ini = idxNB(myinput, i.top),
  next(rinfo, pop.stk, Sstate.top, i.top, ini, result.top, faili.top, failresult.top)
 else if actionState = T then
  let te = idxNB(packedTable, index.state),
  if inputi ≠ match.te then
   {fail}
   next(rinfo, stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(rinfo, stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
 else if actionState = !T then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then
   {fail}
   next(rinfo, stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
  else next(rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
 else if actionState = MatchAny then
  let te = idxNB(packedTable, index.state),
  if inputi = endMark then{fail}next(rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   let reslt = result + toAttribute(result sub n.result, [inputi])
   let ini = idxNB(myinput, i + 1),
   next(rinfo, stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
 else if actionState = T' then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then next(rinfo, stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else next(rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
 else
  {match non Terminal}
  let te = idxNB(packedTable, index.state)
  assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG:(state)"
  let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult)),
  let tmp = [toAttribute(result sub n.result, empty:seq.token)],
  next(rinfo, newstk, nextState.action.te, i, inputi, tmp, i, tmp),
recoverInfo(
 push(stk.rinfo, frame(state, state, place.rinfo, result, n.myinput, result))
 , input.rinfo
 , place.rinfo
 , faili.rinfo
) 