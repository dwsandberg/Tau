Module parser

use PEGrules

use UTF8

use seq.char

use mytype

use otherseq.mytype

use seq.mytype

use set.mytype

use pretty

use standard

use symbol

use otherseq.symbol

use seq.symbol

use set.symbol

use symboldict

use otherseq.word

use seq.word

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
let r = parse(packed.input, b, commonType(types, outText, input))
assert status.r ∈ "Match" report errormessage("syntax error", recoverInfo(pop.stk.r, input, i.top.stk.r)),
code.result.r

function toAttribute(b:bindinfo, w:seq.word) bindinfo
bindinfo(dict.b, empty:seq.symbol, empty:seq.mytype, w)

function errormessage(message:seq.word, rinfo:recoverInfo) seq.word
let input = input.rinfo
let place = place.rinfo
let ending = recoveryEnding.rinfo
let corrected = subseq(input, 1, place - 1) + ending
let pp = prettyNoChange.corrected
for idx = n.pp, remove = ending, addback = "", go = not.isempty.ending, e ∈ reverse.pp
while go
do
 if e ∈ "*>^(escapeformat)" then next(idx - 1, remove, [e] + addback, go)
 else if e = 1^remove then next(idx - 1, remove >> 1, addback, n.remove > 1)
 else if e
 ∈ "/keyword
 /br," then next(idx - 1, remove, addback, go)
 else next(idx - 1, remove, addback, false)
let t =
 "<* literal^(message) *>
 /br^(subseq(pp, 1, idx))"
let unprocessed = subseq(input, place, min(place + 10, n.input - 1)),
(if not.isempty.t ∧ 1^t ∈ "/keyword" then t >> 1 + addback else t + addback)
 + "/br <* literal^(message) *>
/br"
 + if isempty.unprocessed then "at end but expecting:^(ending)"
else "Replaced^(dq(if place + 11 < n.input then unprocessed + "…" else unprocessed)) with^(ending) to parse."

Function binary(R0:bindinfo, op:seq.word, R1:bindinfo) bindinfo
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
  let op = [1#ops]
  let len = toint.2#ops,
  let arg2code = subseq(code.R1, start, start + len - 1),
  if 1#op ∈ "∧ ∨" ∧ types = [typeboolean, typeboolean] ∧ not.outText.static then
   let code =
    if op = "∧" then ifthenelse(arg1code, arg2code, [Litfalse], typeboolean)
    else ifthenelse(arg1code, [Littrue], arg2code, typeboolean),
   next(code, [typeboolean], start + len, ops << 2)
  else
   let f =
    if op = "≠" then [lookupbysig(static, dict, "=", types, rinfo), NotOp]
    else if op = "∉" then [lookupbysig(static, dict, "∈", types, rinfo), NotOp]
    else if op = "≥" then [lookupbysig(static, dict, "<", types, rinfo), NotOp]
    else if op = "≤" then [lookupbysig(static, dict, ">", types, rinfo), NotOp]
    else [lookupbysig(static, dict, [1#op], types, rinfo)],
   next(arg1code + arg2code + f, [resulttype.1#f], start + len, ops << 2),
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
   assert resulttype.cvt = seqof.typeword report errormessage("Expected function^(cvt) to have return type of seq.word", rinfo),
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
assert 1#types.cond = typeboolean report errormessage("cond of if must be boolean but is^(1#types.cond)", rinfo)
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
assert types.thenpart = types.elsepart ∧ (isempty.types.elseifpart ∨ types.elseifpart = types.thenpart) report errormessage("then and else types are different", rinfo),
bindinfo(
 dict.cond
 , [Start.1#types.thenpart]
  + code.t
  + code.elseifpart
  + (if outText.static then code.elsepart + EndBlock else code.elsepart + Exit + EndBlock)
 , types.elsepart
 , ""
)

function declarePara(d:symboldict, names:seq.word, types:seq.mytype) bindinfo
for dict = d, no = 1, t ∈ types
do next(dict + Local(no#names, t, no), no + 1),
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
 else symbol4(internalmod, 1#name, resolvetype(static, name << 1, rinfo), paratypes, typeint)
let f0 = lookupbysig(dict, sym3)
let f =
 if n.f0 < 2 then f0
 else
  for acc = empty:set.symbol, sy ∈ toseq.f0
  do if isunbound.sy then acc else acc + sy,
  acc
assert not.isempty.f report
 if n.name = 1 ∧ 1#name ∈ "if else then for" then errormessage("Syntax error", rinfo)
 else
  errormessage(
   "cannot find 1^(if n.name = 1 then name else [1#name, 1#":"] + name << 1) (^(for acc = "", @e ∈ paratypes do acc + %.@e + ",",
   acc >> 1))"
   , rinfo
  )
assert n.f = 1 report
 errormessage(
  "found more than one^(for acc = "", @e ∈ toseq.f do acc + library.module.@e + "." + %.@e,
  acc)"
  , rinfo
 )
let discard =
 for acc = 0, sym2 ∈ requires(dict, 1#f)
 do
  let xxx = lookupbysig(dict, sym2)
  assert not.isempty.xxx ∨ isAbstract.module.1#f report errormessage("using symbol^(1#f) requires unbound^(sym2)", rinfo),
  0,
 0,
1#f

Function addpara(
static:commonType
, name:seq.word
, ptype:bindinfo
, rinfo:recoverInfo
) bindinfo
let b = ptype
let paratype = resolvetype(static, text.ptype, rinfo)
assert isempty.lookupbysig(dict.b, name) ∨ name = ":" report errormessage("duplciate symbol:^(name)", rinfo),
bindinfo(dict.b, empty:seq.symbol, [paratype], name)

Function addpara(
static:commonType
, b:bindinfo
, name:seq.word
, ptype:bindinfo
, rinfo:recoverInfo
) bindinfo
let paratype = resolvetype(static, text.ptype, rinfo)
assert isempty.lookupbysig(dict.b, name) ∨ name = ":" report errormessage("duplciate symbol:^(name)", rinfo),
bindinfo(
 dict.b + Local(1#name, paratype, n.text.b + 1)
 , empty:seq.symbol
 , empty:seq.mytype
 , text.b + name
)

Function seqExp(static:commonType, R:bindinfo, rinfo:recoverInfo) bindinfo
let types = types.R
assert for acc = true, @e ∈ types do acc ∧ 1#types = @e,
acc report errormessage("types do not match in build", rinfo),
bindinfo(dict.R, code.R + Sequence(1#types, n.types), [seqof.1#types], "")

Function letExp(static:commonType, R:bindinfo, exp:bindinfo, rinfo:recoverInfo) bindinfo
let name = text.R
assert isempty.lookupbysig(dict.R, name) report errormessage("duplicate symbol:^(name)", rinfo)
let newdict = dict.R + Local(1#name, 1#types.exp, cardinality.dict.R),
bindinfo(newdict, code.R + code.exp + Define(1#name, cardinality.dict.R), types.exp, name)

Function bindlit2(static:commonType, R:bindinfo, rinfo:recoverInfo) bindinfo
assert not.isempty.text.R report "bindlit2"
let kind = hexOrDecimal?.1#text.R,
if kind ∈ "other" then
 let f = lookupbysig(static, dict.R, text.R, empty:seq.mytype, rinfo),
 bindinfo(dict.R, [f], [resulttype.f], "")
else
 let rt = if kind ∈ "hex" then typebits else typeint,
 bindinfo(
  dict.R
  , [if outText.static then symbol(internalmod, text.R, rt) else Lit.1#text.R]
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
if 1#op = 1#"process" ∧ n.types.exp = 1 then
 let rt = 1#resolvetype(types.static, %.1#types.exp)
 let processtype = processof.rt
 let dcws = deepcopyseqword,
 let newcode =
  [Fref.deepcopySym.rt, Fref.dcws, Fref.1^code.exp]
   + subseq(code.exp, 1, n.code.exp - 1)
   + [Lit.0, Fref.1^code.exp]
   + Record([typeint, typeint, typeint] + paratypes.1^code.exp + typeint + typeint)
   + symbol(builtinmod.rt, "createthreadZ", typeptr, processtype),
 bindinfo(
  dict
  , if outText.static then code.exp + symbol(internalmod, "process", rt, rt) else newcode
  , [processtype]
  , ""
 )
else if hexOrDecimal?.1#op ∉ "other" ∧ n.code.exp = 1 then
 let dec =
  if outText.static then name.1#code.exp
  else
   assert isIntLit.1#code.exp report errormessage("illformed real literal", rinfo),
   name.1#code.exp,
 bindinfo(dict, [Words(op + "." + dec), makerealSymbol], [typereal], "")
else
 let f = lookupbysig(static, dict, op, types.exp, rinfo),
 bindinfo(dict, code.exp + f, [resulttype.f], "")

function resolvetype(static:commonType, text:seq.word, rinfo:recoverInfo) mytype
let a = resolvetype(types.static, text)
assert not.isempty.a report errormessage("cannot resolve type^(text)", rinfo),
1#a

Function checktype(
static:commonType
, functype:bindinfo
, Declare:bindinfo
, exp:bindinfo
, rinfo:recoverInfo
) bindinfo
let returntype = resolvetype(static, text.functype, rinfo)
assert returntype = 1#types.exp report errormessage("function type of^(returntype) does not match expression type^(1#types.exp)", rinfo),
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
 assert isempty.lookupbysig(dict.accum0, [name]) report errormessage("duplicate symbol:^(name)", rinfo)
 let z = Local(name, i#types.accum0, cardinality.accdict),
 next(accdict + z, i + 1)
let seqtype =
 if noseq then seqof.typeint
 else
  let seqtype0 = 1#types.theseq
  assert isempty.lookupbysig(accdict, elename) report errormessage("duplicate symbol:^(elename)", rinfo),
  assert isseq.seqtype0 report errormessage("final expression in for list must be a sequence but it is of type:^(seqtype0)", rinfo),
  seqtype0
{keep track so right next is used in nested fors}
let lastaccum = cardinality.accdict - 1
let elementSym = Local(1#elename, parameter.seqtype, lastaccum + 2)
let dict2 =
 accdict
  + Local(toword(lastaccum + 1), seqtype, lastaccum + 1)
  + elementSym
  + Local(toword(lastaccum + 3), typeint, lastaccum + 3)
  + Local(toword(lastaccum + 4), typeint, lastaccum + 4)
  + Local(toword(lastaccum + 2), typeint, lastaccum + 5)
let nextSym = symbol(moduleref("internallib $for", basetype), "next", types.accum0, basetype)
{assert not.noseq report % (types.accum0+parameter.seqtype)+" KLJ:"+text.accum0+elename}
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
assert 1#types.cond = typeboolean report errormessage("condition in assert must be boolean in:", rinfo)
assert 1#types.exp = seqof.typeword report errormessage("report in assert must be seq of word in:", rinfo),
if outText.static then
 bindinfo(
  dict.cond
  , code.cond
   + code.exp
   + symbol(internalmod, "$assert", typeboolean, seqof.typeword, typeint)
  , [typeint]
  , ""
 )
else
 let assertsym = symbol(internalmod, "assert", seqof.typeword, typeint),
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
   + Define(1#"assert", cardinality.dict.cond)
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
let theseqtype = 1^types.vars
let nowhile = code.exitexp = [Littrue]
let noseq = 1^text.vars ∈ "."
let forbodytype = resulttype.1#lookupbysig(dict.vars, "for")
let forbody =
 if n.accumTypes = 1 ∧ forbodytype = 1#types.forbodyin then
  {handle next with single accumulator}
  bindinfo(dict.forbodyin, code.forbodyin >> 1, [1#accumTypes], text.forbodyin)
 else forbodyin
let actualbodytype = 1#types.forbody
let checktypes =
 if 1#types.exitexp = typeboolean then
  {while type is OK. now check body type}
  if n.accumTypes > 1 then if forbodytype = actualbodytype then "" else "incorrect body type:^(actualbodytype)"
  else if 1#accumTypes = actualbodytype then
   {body type is OK, now check to see if while clause is required}
   if noseq ∧ code.exitexp = [Littrue] then "While clause must be present and not equal to true when no sequence is specified."
   else ""
  else "Type of body expression^(actualbodytype) must match accumulator type^(1#accumTypes)"
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
    + 1#types.forbody
    + seqof.typeword
   , typeint
  )
 else
  let firstvar = toint.1#%.parameter.forbodytype
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
   let reverse = name.module.1^codevars ∈ "otherseq" ∧ name.1^codevars ∈ "reverse"
   let continue = if n.accumTypes = 1 then [masterindex, continue.2] else [Exit]
   let setElement =
    [
     lastidx
     , if reverse then Lit.-1 else Lit.1
     , PlusOp
     , Define.value.masterindex
     , {let sequenceele = (idx)#seq} theseq
     , masterindex
     , symbol(builtinmod.theseqtype, "idxNB", seqof.theseqtype, typeint, theseqtype)
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
    let seq? = 1^code.forbody,
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
if outText.static ∧ not.isempty.a ∧ not.isempty.b then a + b + symbol(internalmod, "$mergecode", typeint, typeint, typeint)
else a + b

function slash word 1#"/"

function endMark word encodeword.[char.254]

function PEGgen(
seqElementType:word
, attributeType:bindinfo
, resultType:recoverInfo
, error:boolean
, common:commonType
, rinfo:recoverInfo
) seq.boolean
{commonName: common wordmap: carrot 1#"^", slash slash, dq 1#dq, 1#" $"}
[
 "Parser function Name (FPL) Type Declare' E" = checktype(common, $.3, $.4, $.5, rinfo)
 , "/ function Name Type Declare' E" = checktype(common, $.2, $.3, $.4, rinfo)
 , "/ Function Name (FPL) Type Declare' E" = checktype(common, $.3, $.4, $.5, rinfo)
 , "/ Function Name Type Declare' E" = checktype(common, $.2, $.3, $.4, rinfo)
 , "String dq String' dq"
 = strExp(common, $.1, "", true, empty:seq.symbol, typeint, rinfo)
 , "* String' carrot (E)" = strExp(common, $.0, "", true, code.$.1, 1#types.$.1, rinfo)
 , "/ carrot" = strExp(common, $.0, "^", false, empty:seq.symbol, typeint, rinfo)
 , "/ str2" = strExp(common, $.0, text.$.1, false, empty:seq.symbol, typeint, rinfo)
 , "+str2 ! dq ! carrot any" = /All
 , "E Or" = $.1
 , "* EL', E" = bindinfo(dict.$.0, code.$.0 + code.$.1, types.$.0 + types.$.1, "")
 , "Or And Or'" = binaryops(common, $.1, $.2, rinfo)
 , "* Or' ∨ And" = binary($.0, "∨", $.1)
 , "/ /or And" = binary($.0, "∨", $.1)
 , "/ ⊻ And" = binary($.0, "⊻", $.1)
 , "And Compare And'" = binaryops(common, $.1, $.2, rinfo)
 , "* And' ∧ Compare" = binary($.0, "∧", $.1)
 , "/ /and Compare" = binary($.0, "∧", $.1)
 , "Compare Sum Compare'" = binaryops(common, $.1, $.2, rinfo)
 , "* Compare' = Sum" = binary($.0, "=", $.1)
 , "/ ≠ Sum" = binary($.0, "≠", $.1)
 , "/ > Sum" = binary($.0, ">", $.1)
 , "/ < Sum" = binary($.0, "<", $.1)
 , "/ >1 Sum" = binary($.0, ">1", $.1)
 , "/ >2 Sum" = binary($.0, ">2", $.1)
 , "/ ≥ Sum" = binary($.0, "≥", $.1)
 , "/ /ge Sum" = binary($.0, "≥", $.1)
 , "/ ≤ Sum" = binary($.0, "≤", $.1)
 , "/ /le Sum" = binary($.0, "≤", $.1)
 , "/ /ne Sum" = binary($.0, "≠", $.1)
 , "Sum Product Sum'" = binaryops(common, $.1, $.2, rinfo)
 , "* Sum'-Product" = binary($.0, "-", $.1)
 , "/+Product" = binary($.0, "+", $.1)
 , "/ ∈ Product" = binary($.0, "∈", $.1)
 , "/ /in Product" = binary($.0, "∈", $.1)
 , "/ ∉ Product" = binary($.0, "∉", $.1)
 , "/ /nin Product" = binary($.0, "∉", $.1)
 , "Product Unary Product'" = binaryops(common, $.1, $.2, rinfo)
 , "* Product' * Unary" = binary($.0, "*", $.1)
 , "/ >> Unary" = binary($.0, ">>", $.1)
 , "/ << Unary" = binary($.0, "<<", $.1)
 , "/ slash Unary" = binary($.0, [slash], $.1)
 , "/ mod Unary" = binary($.0, "mod", $.1)
 , "/ ∩ Unary" = binary($.0, "∩", $.1)
 , "/ ∪ Unary" = binary($.0, "∪", $.1)
 , "/ /cap Unary" = binary($.0, "∩", $.1)
 , "/ /cup Unary" = binary($.0, "∪", $.1)
 , "/ \ Unary" = binary($.0, "\", $.1)
 , "Unary-Unary" = unaryop(common, dict.$.1, rinfo, "-", $.1)
 , "/ Id.Unary" = unaryop(common, dict.$.1, {place-1?} rinfo, text.$.1, $.2)
 , "/ {N} Unary"
 = (if outText.common then
  bindinfo(
   dict.$.2
   , [Words.text.$.1]
    + code.$.2
    + symbol(internalmod, "{", seqof.typeword, 1#types.$.2, 1#types.$.2)
   , types.$.2
   , ""
  )
 else $.2)
 , "/ Power" = $.1
 , "Power Atom Power'" = binaryops(common, $.1, $.2, rinfo)
 , "* Power'#Unary" = binary($.0, "#", $.1)
 , "/^Unary" = binary($.0, "^", $.1)
 , "Atom (E)"
 = (if outText.common then bindinfo(dict.$.1, code.$.1 + symbol(internalmod, "(", typeint, typeint), types.$.1, "")
 else $.1)
 , "/ [E EL']"
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
 , "/ Name (E EL')"
 = unaryop(
  common
  , dict.$.1
  , rinfo
  , text.$.1
  , bindinfo(dict.$.2, code.$.2 + code.$.3, types.$.2 + types.$.3, "")
 )
 , "/ Name" = bindlit2(common, $.1, rinfo)
 , "Name Id:Type"
 = bindinfo(dict.$.1, empty:seq.symbol, empty:seq.mytype, text.$.1 + text.$.2)
 , "/ Id" = $.1
 , "Id !, ! [! (!] !) !:!.! dq any" = $.1
 , "comma?," = $.0
 , "/" = $.0
 , "* IF else if E then E" = ifExp(common, $.0, $.1, $.2, rinfo)
 , "Type Id.Type"
 = bindinfo(dict.$.2, empty:seq.symbol, empty:seq.mytype, text.$.1 + "." + text.$.2)
 , "/ Id" = $.1
 , "Declare let any = E comma?" = letExp(common, $.1, $.2, rinfo)
 , "/ assert E report E comma?" = assertExp(common, $.1, $.2, rinfo)
 , "/ {N} comma?"
 = (if outText.common then
  bindinfo(
   dict.$.0
   , code.$.0 + Words.text.$.1 + symbol(internalmod, "{", seqof.typeword, typeint)
   , empty:seq.mytype
   , ""
  )
 else $.0)
 , "/ for ForDeclare do E comma?"
 = forbody(common, $.1, bindinfo(dict.$.0, [Littrue], [typeboolean], ""), $.2, rinfo)
 , "/ for ForDeclare while E do E comma?" = forbody(common, $.1, $.2, $.3, rinfo)
 , "ForDeclare AccumList, any ∈ E" = forSeqExp(common, $.1, text.$.2, $.3, rinfo)
 , "/ AccumList, any /in E" = forSeqExp(common, $.1, text.$.2, $.3, rinfo)
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
 , "FP any:Type" = addpara(common, text.$.1, $.2, rinfo)
 , "/ Type" = addpara(common, $.0, ":", $.1, rinfo)
 , "* N {N}" = /All
 , "/ !} any" = /All
]

<<<< Below is auto generated code >>>>

/br Non-terminals:AccumList AccumList' And And' Atom Compare Compare' Declare Declare' E EL' FP FPL FPL' ForDeclare IF Id N Name Or Or' Parser Power Power' Product Product' String String' Sum Sum' Type Unary comma? str2
/br Terminals:#() *+,-./and /cap /cup /ge /in /le /ne /nin /or:< << = > >1 >2 >> Function [\]^any assert carrot do dq else for function if let mod report slash then while {} ∈ ∉ ∧ ∨ ∩ ∪ ≠ ≤ ≥ ⊻
/br Parser ← function Name (FPL) Type Declare' E / function Name Type Declare' E / Function Name (FPL) Type Declare' E / Function Name Type Declare' E
/br String ← dq String' dq
/br * String' ← carrot (E) / carrot / str2
/br+str2 ← ! dq ! carrot any
/br E ← Or
/br * EL' ←, E
/br Or ← And Or'
/br * Or' ← ∨ And / /or And / ⊻ And
/br And ← Compare And'
/br * And' ← ∧ Compare / /and Compare
/br Compare ← Sum Compare'
/br * Compare' ← = Sum / ≠ Sum / > Sum / < Sum / >1 Sum / >2 Sum / ≥ Sum / /ge Sum / ≤ Sum / /le Sum / /ne Sum
/br Sum ← Product Sum'
/br * Sum' ←-Product /+Product / ∈ Product / /in Product / ∉ Product / /nin Product
/br Product ← Unary Product'
/br * Product' ← * Unary / >> Unary / << Unary / slash Unary / mod Unary / ∩ Unary / ∪ Unary / /cap Unary / /cup Unary / \ Unary
/br Unary ←-Unary / Id.Unary / {N} Unary / Power
/br Power ← Atom Power'
/br * Power' ←#Unary /^Unary
/br Atom ← (E) / [E EL'] / String / Declare Declare' E / if E then E IF else E / Name (E EL') / Name
/br Name ← Id:Type / Id
/br Id ← !, ! [! (!] !) !:!.! dq any
/br comma? ←, /
/br * IF ← else if E then E
/br Type ← Id.Type / Id
/br Declare ← let any = E comma? / assert E report E comma? / {N} comma? / for ForDeclare do E comma? / for ForDeclare while E do E comma?
/br ForDeclare ← AccumList, any ∈ E / AccumList, any /in E / AccumList
/br AccumList ← ! while any = E AccumList'
/br * AccumList' ←, any = E
/br * Declare' ← Declare
/br FPL ← FP FPL'
/br * FPL' ←, FP
/br FP ← any:Type / Type
/br * N ← {N} / !} any

function action(
partno:int
, R:seq.bindinfo
, common:commonType
, rinfo:recoverInfo
) bindinfo
if partno = 2 then checktype(common, 3^R, 2^R, 1^R, rinfo)
else if partno = 3 then checktype(common, 3^R, 2^R, 1^R, rinfo)
else if partno = 4 then checktype(common, 3^R, 2^R, 1^R, rinfo)
else if partno = 5 then checktype(common, 3^R, 2^R, 1^R, rinfo)
else if partno = 6 then strExp(common, 1^R, "", true, empty:seq.symbol, typeint, rinfo)
else if partno = 7 then strExp(common, 2^R, "", true, code.1^R, 1#types.1^R, rinfo)
else if partno = 8 then strExp(common, 1^R, "^", false, empty:seq.symbol, typeint, rinfo)
else if partno = 9 then strExp(common, 2^R, text.1^R, false, empty:seq.symbol, typeint, rinfo)
else if partno = 11 then 1^R
else if partno = 12 then bindinfo(dict.2^R, code.2^R + code.1^R, types.2^R + types.1^R, "")
else if partno = 13 then binaryops(common, 2^R, 1^R, rinfo)
else if partno = 14 then binary(2^R, "∨", 1^R)
else if partno = 15 then binary(2^R, "∨", 1^R)
else if partno = 16 then binary(2^R, "⊻", 1^R)
else if partno = 17 then binaryops(common, 2^R, 1^R, rinfo)
else if partno = 18 then binary(2^R, "∧", 1^R)
else if partno = 19 then binary(2^R, "∧", 1^R)
else if partno = 20 then binaryops(common, 2^R, 1^R, rinfo)
else if partno = 21 then binary(2^R, "=", 1^R)
else if partno = 22 then binary(2^R, "≠", 1^R)
else if partno = 23 then binary(2^R, ">", 1^R)
else if partno = 24 then binary(2^R, "<", 1^R)
else if partno = 25 then binary(2^R, ">1", 1^R)
else if partno = 26 then binary(2^R, ">2", 1^R)
else if partno = 27 then binary(2^R, "≥", 1^R)
else if partno = 28 then binary(2^R, "≥", 1^R)
else if partno = 29 then binary(2^R, "≤", 1^R)
else if partno = 30 then binary(2^R, "≤", 1^R)
else if partno = 31 then binary(2^R, "≠", 1^R)
else if partno = 32 then binaryops(common, 2^R, 1^R, rinfo)
else if partno = 33 then binary(2^R, "-", 1^R)
else if partno = 34 then binary(2^R, "+", 1^R)
else if partno = 35 then binary(2^R, "∈", 1^R)
else if partno = 36 then binary(2^R, "∈", 1^R)
else if partno = 37 then binary(2^R, "∉", 1^R)
else if partno = 38 then binary(2^R, "∉", 1^R)
else if partno = 39 then binaryops(common, 2^R, 1^R, rinfo)
else if partno = 40 then binary(2^R, "*", 1^R)
else if partno = 41 then binary(2^R, ">>", 1^R)
else if partno = 42 then binary(2^R, "<<", 1^R)
else if partno = 43 then binary(2^R, [slash], 1^R)
else if partno = 44 then binary(2^R, "mod", 1^R)
else if partno = 45 then binary(2^R, "∩", 1^R)
else if partno = 46 then binary(2^R, "∪", 1^R)
else if partno = 47 then binary(2^R, "∩", 1^R)
else if partno = 48 then binary(2^R, "∪", 1^R)
else if partno = 49 then binary(2^R, "\", 1^R)
else if partno = 50 then unaryop(common, dict.1^R, rinfo, "-", 1^R)
else if partno = 51 then unaryop(common, dict.2^R, {place-1?} rinfo, text.2^R, 1^R)
else if partno = 52 then
 if outText.common then
  bindinfo(
   dict.1^R
   , [Words.text.2^R]
    + code.1^R
    + symbol(internalmod, "{", seqof.typeword, 1#types.1^R, 1#types.1^R)
   , types.1^R
   , ""
  )
 else 1^R
else if partno = 53 then 1^R
else if partno = 54 then binaryops(common, 2^R, 1^R, rinfo)
else if partno = 55 then binary(2^R, "#", 1^R)
else if partno = 56 then binary(2^R, "^", 1^R)
else if partno = 57 then
 if outText.common then bindinfo(dict.1^R, code.1^R + symbol(internalmod, "(", typeint, typeint), types.1^R, "")
 else 1^R
else if partno = 58 then
 seqExp(
  common
  , bindinfo(dict.2^R, code.2^R + code.1^R, types.2^R + types.1^R, "")
  , rinfo
 )
else if partno = 59 then 1^R
else if partno = 60 then
 bindinfo(
  dict.4^R
  , mergeText(common, mergeText(common, code.3^R, code.2^R), code.1^R)
  , types.1^R
  , ""
 )
else if partno = 61 then ifExp(common, 4^R, 3^R, 2^R, 1^R, rinfo)
else if partno = 62 then
 unaryop(
  common
  , dict.3^R
  , rinfo
  , text.3^R
  , bindinfo(dict.2^R, code.2^R + code.1^R, types.2^R + types.1^R, "")
 )
else if partno = 63 then bindlit2(common, 1^R, rinfo)
else if partno = 64 then bindinfo(dict.2^R, empty:seq.symbol, empty:seq.mytype, text.2^R + text.1^R)
else if partno = 65 then 1^R
else if partno = 66 then 1^R
else if partno = 67 then 1^R
else if partno = 68 then 1^R
else if partno = 69 then ifExp(common, 3^R, 2^R, 1^R, rinfo)
else if partno = 70 then bindinfo(dict.1^R, empty:seq.symbol, empty:seq.mytype, text.2^R + "." + text.1^R)
else if partno = 71 then 1^R
else if partno = 72 then letExp(common, 3^R, 2^R, rinfo)
else if partno = 73 then assertExp(common, 3^R, 2^R, rinfo)
else if partno = 74 then
 if outText.common then
  bindinfo(
   dict.3^R
   , code.3^R + Words.text.2^R + symbol(internalmod, "{", seqof.typeword, typeint)
   , empty:seq.mytype
   , ""
  )
 else 3^R
else if partno = 75 then forbody(common, 3^R, bindinfo(dict.4^R, [Littrue], [typeboolean], ""), 2^R, rinfo)
else if partno = 76 then forbody(common, 4^R, 3^R, 2^R, rinfo)
else if partno = 77 then forSeqExp(common, 3^R, text.2^R, 1^R, rinfo)
else if partno = 78 then forSeqExp(common, 3^R, text.2^R, 1^R, rinfo)
else if partno = 79 then forSeqExp(common, 1^R, ".", 1^R, rinfo)
else if partno = 80 then bindinfo(dict.4^R, code.2^R + code.1^R, types.2^R + types.1^R, text.3^R + text.1^R)
else if partno = 81 then bindinfo(dict.3^R, code.3^R + code.1^R, types.3^R + types.1^R, text.3^R + text.2^R)
else if partno = 82 then bindinfo(dict.1^R, mergeText(common, code.2^R, code.1^R), empty:seq.mytype, "")
else if partno = 83 then declarePara(dict.2^R, text.2^R + text.1^R, types.2^R + types.1^R)
else if partno = 84 then bindinfo(dict.2^R, empty:seq.symbol, types.2^R + types.1^R, text.2^R + text.1^R)
else if partno = 85 then addpara(common, text.2^R, 1^R, rinfo)
else if partno = 86 then addpara(common, 2^R, ":", 1^R, rinfo)
else 1#R

function mytable seq.tableEntry
[
 {1} tableEntry(NT.T'.2, 1#"?", Match, Failure, "")
 , {2} tableEntry(T', 1#"function", NT.3, T'.15, "function Name (FPL) Type E")
 , {3} tableEntry(NT.157, 1#"Name", T'.4, T'.15, "Name (FPL) Type E")
 , {4} tableEntry(T', 1#"(", NT.5, NT.12, "(FPL) Type E")
 , {5} tableEntry(NT.227, 1#"FPL", T.6, T'.10, "FPL) Type E")
 , {6} tableEntry(T, 1#")", NT.7, T'.10, ") Type E")
 , {7} tableEntry(NT.176, 1#"Type", NT.8, T'.10, "Type E")
 , {8} tableEntry(NT.226, 1#"Declare'", NT.9, T'.10, "E")
 , {9} tableEntry(NT.40, 1#"E", Reduce.2, T'.10, "E")
 , {10} tableEntry(T', 1#"function", NT.11, T'.15, "function Name Type E")
 , {11} tableEntry(NT.157, 1#"Name", NT.12, T'.15, "Name Type E")
 , {12} tableEntry(NT.176, 1#"Type", NT.13, T'.15, "Type E")
 , {13} tableEntry(NT.226, 1#"Declare'", NT.14, T'.15, "E")
 , {14} tableEntry(NT.40, 1#"E", Reduce.3, T'.15, "E")
 , {15} tableEntry(T', 1#"Function", NT.16, Fail, "Function Name (FPL) Type E")
 , {16} tableEntry(NT.157, 1#"Name", T'.17, Fail, "Name (FPL) Type E")
 , {17} tableEntry(T', 1#"(", NT.18, NT.25, "(FPL) Type E")
 , {18} tableEntry(NT.227, 1#"FPL", T.19, T.23, "FPL) Type E")
 , {19} tableEntry(T, 1#")", NT.20, T.23, ") Type E")
 , {20} tableEntry(NT.176, 1#"Type", NT.21, T.23, "Type E")
 , {21} tableEntry(NT.226, 1#"Declare'", NT.22, T.23, "E")
 , {22} tableEntry(NT.40, 1#"E", Reduce.4, T.23, "E")
 , {23} tableEntry(T, 1#"Function", NT.24, Fail, "Function Name Type E")
 , {24} tableEntry(NT.157, 1#"Name", NT.25, Fail, "Name Type E")
 , {25} tableEntry(NT.176, 1#"Type", NT.26, Fail, "Type E")
 , {26} tableEntry(NT.226, 1#"Declare'", NT.27, Fail, "E")
 , {27} tableEntry(NT.40, 1#"E", Reduce.5, Fail, "E")
 , {28} tableEntry(T, 1#dq, NT.29, Fail, "^(1#dq)^(1#dq)")
 , {29} tableEntry(NT.T'.31, 1#"String'", T.30, Fail, "^(1#dq)")
 , {30} tableEntry(T, 1#dq, Reduce.6, Fail, "^(1#dq)")
 , {31} tableEntry(T', 1#"^", T.32, NT.36, "^(1#"^") (E)")
 , {32} tableEntry(T, 1#"(", NT.33, T'.35, "(E)")
 , {33} tableEntry(NT.40, 1#"E", T.34, T'.35, "E)")
 , {34} tableEntry(T, 1#")", Reduce*(7, T'.31), T'.35, ")")
 , {35} tableEntry(T', 1#"^", Reduce*(8, T'.31), NT.36, "^(1#"^")")
 , {36} tableEntry(NT.!T.37, 1#"str2", Reduce*(9, T'.31), Success*, "str2")
 , {37} tableEntry(!T, 1#dq, Fail, !T.38, "^(1#dq) any")
 , {38} tableEntry(!T, 1#"^", Fail, MatchAny.39, "^(1#"^") any")
 , {39} tableEntry(MatchAny, 1#"?", Discard*.!T.240, Fail, "any")
 , {40} tableEntry(NT.43, 1#"Or", Reduce.11, Fail, "Or")
 , {41} tableEntry(T, 1#",", NT.42, Success*, ", E")
 , {42} tableEntry(NT.40, 1#"E", Reduce*(12, T.41), Success*, "E")
 , {43} tableEntry(NT.51, 1#"And", NT.44, Fail, "And")
 , {44} tableEntry(NT.T'.45, 1#"Or'", Reduce.13, Fail, "")
 , {45} tableEntry(T', 1#"∨", NT.46, T'.47, "∨ And")
 , {46} tableEntry(NT.51, 1#"And", Reduce*(14, T'.45), T'.47, "And")
 , {47} tableEntry(T', 1#"/or", NT.48, T.49, "/or And")
 , {48} tableEntry(NT.51, 1#"And", Reduce*(15, T'.45), T.49, "And")
 , {49} tableEntry(T, 1#"⊻", NT.50, Success*, "⊻ And")
 , {50} tableEntry(NT.51, 1#"And", Reduce*(16, T'.45), Success*, "And")
 , {51} tableEntry(NT.57, 1#"Compare", NT.52, Fail, "Compare")
 , {52} tableEntry(NT.T'.53, 1#"And'", Reduce.17, Fail, "")
 , {53} tableEntry(T', 1#"∧", NT.54, T.55, "∧ Compare")
 , {54} tableEntry(NT.57, 1#"Compare", Reduce*(18, T'.53), T.55, "Compare")
 , {55} tableEntry(T, 1#"/and", NT.56, Success*, "/and Compare")
 , {56} tableEntry(NT.57, 1#"Compare", Reduce*(19, T'.53), Success*, "Compare")
 , {57} tableEntry(NT.81, 1#"Sum", NT.58, Fail, "Sum")
 , {58} tableEntry(NT.T'.59, 1#"Compare'", Reduce.20, Fail, "")
 , {59} tableEntry(T', 1#"=", NT.60, T'.61, "= Sum")
 , {60} tableEntry(NT.81, 1#"Sum", Reduce*(21, T'.59), T'.61, "Sum")
 , {61} tableEntry(T', 1#"≠", NT.62, T'.63, "≠ Sum")
 , {62} tableEntry(NT.81, 1#"Sum", Reduce*(22, T'.59), T'.63, "Sum")
 , {63} tableEntry(T', 1#">", NT.64, T'.65, "> Sum")
 , {64} tableEntry(NT.81, 1#"Sum", Reduce*(23, T'.59), T'.65, "Sum")
 , {65} tableEntry(T', 1#"<", NT.66, T'.67, "< Sum")
 , {66} tableEntry(NT.81, 1#"Sum", Reduce*(24, T'.59), T'.67, "Sum")
 , {67} tableEntry(T', 1#">1", NT.68, T'.69, ">1 Sum")
 , {68} tableEntry(NT.81, 1#"Sum", Reduce*(25, T'.59), T'.69, "Sum")
 , {69} tableEntry(T', 1#">2", NT.70, T'.71, ">2 Sum")
 , {70} tableEntry(NT.81, 1#"Sum", Reduce*(26, T'.59), T'.71, "Sum")
 , {71} tableEntry(T', 1#"≥", NT.72, T'.73, "≥ Sum")
 , {72} tableEntry(NT.81, 1#"Sum", Reduce*(27, T'.59), T'.73, "Sum")
 , {73} tableEntry(T', 1#"/ge", NT.74, T'.75, "/ge Sum")
 , {74} tableEntry(NT.81, 1#"Sum", Reduce*(28, T'.59), T'.75, "Sum")
 , {75} tableEntry(T', 1#"≤", NT.76, T'.77, "≤ Sum")
 , {76} tableEntry(NT.81, 1#"Sum", Reduce*(29, T'.59), T'.77, "Sum")
 , {77} tableEntry(T', 1#"/le", NT.78, T.79, "/le Sum")
 , {78} tableEntry(NT.81, 1#"Sum", Reduce*(30, T'.59), T.79, "Sum")
 , {79} tableEntry(T, 1#"/ne", NT.80, Success*, "/ne Sum")
 , {80} tableEntry(NT.81, 1#"Sum", Reduce*(31, T'.59), Success*, "Sum")
 , {81} tableEntry(NT.95, 1#"Product", NT.82, Fail, "Product")
 , {82} tableEntry(NT.T'.83, 1#"Sum'", Reduce.32, Fail, "")
 , {83} tableEntry(T', 1#"-", NT.84, T'.85, "-Product")
 , {84} tableEntry(NT.95, 1#"Product", Reduce*(33, T'.83), T'.85, "Product")
 , {85} tableEntry(T', 1#"+", NT.86, T'.87, "+Product")
 , {86} tableEntry(NT.95, 1#"Product", Reduce*(34, T'.83), T'.87, "Product")
 , {87} tableEntry(T', 1#"∈", NT.88, T'.89, "∈ Product")
 , {88} tableEntry(NT.95, 1#"Product", Reduce*(35, T'.83), T'.89, "Product")
 , {89} tableEntry(T', 1#"/in", NT.90, T'.91, "/in Product")
 , {90} tableEntry(NT.95, 1#"Product", Reduce*(36, T'.83), T'.91, "Product")
 , {91} tableEntry(T', 1#"∉", NT.92, T.93, "∉ Product")
 , {92} tableEntry(NT.95, 1#"Product", Reduce*(37, T'.83), T.93, "Product")
 , {93} tableEntry(T, 1#"/nin", NT.94, Success*, "/nin Product")
 , {94} tableEntry(NT.95, 1#"Product", Reduce*(38, T'.83), Success*, "Product")
 , {95} tableEntry(NT.T'.117, 1#"Unary", NT.96, Fail, "Unary")
 , {96} tableEntry(NT.T'.97, 1#"Product'", Reduce.39, Fail, "")
 , {97} tableEntry(T', 1#"*", NT.98, T'.99, "* Unary")
 , {98} tableEntry(NT.T'.117, 1#"Unary", Reduce*(40, T'.97), T'.99, "Unary")
 , {99} tableEntry(T', 1#">>", NT.100, T'.101, ">> Unary")
 , {100} tableEntry(NT.T'.117, 1#"Unary", Reduce*(41, T'.97), T'.101, "Unary")
 , {101} tableEntry(T', 1#"<<", NT.102, T'.103, "<< Unary")
 , {102} tableEntry(NT.T'.117, 1#"Unary", Reduce*(42, T'.97), T'.103, "Unary")
 , {103} tableEntry(T', slash, NT.104, T'.105, "^(slash) Unary")
 , {104} tableEntry(NT.T'.117, 1#"Unary", Reduce*(43, T'.97), T'.105, "Unary")
 , {105} tableEntry(T', 1#"mod", NT.106, T'.107, "mod Unary")
 , {106} tableEntry(NT.T'.117, 1#"Unary", Reduce*(44, T'.97), T'.107, "Unary")
 , {107} tableEntry(T', 1#"∩", NT.108, T'.109, "∩ Unary")
 , {108} tableEntry(NT.T'.117, 1#"Unary", Reduce*(45, T'.97), T'.109, "Unary")
 , {109} tableEntry(T', 1#"∪", NT.110, T'.111, "∪ Unary")
 , {110} tableEntry(NT.T'.117, 1#"Unary", Reduce*(46, T'.97), T'.111, "Unary")
 , {111} tableEntry(T', 1#"/cap", NT.112, T'.113, "/cap Unary")
 , {112} tableEntry(NT.T'.117, 1#"Unary", Reduce*(47, T'.97), T'.113, "Unary")
 , {113} tableEntry(T', 1#"/cup", NT.114, T.115, "/cup Unary")
 , {114} tableEntry(NT.T'.117, 1#"Unary", Reduce*(48, T'.97), T.115, "Unary")
 , {115} tableEntry(T, 1#"\", NT.116, Success*, "\ Unary")
 , {116} tableEntry(NT.T'.117, 1#"Unary", Reduce*(49, T'.97), Success*, "Unary")
 , {117} tableEntry(T', 1#"-", NT.118, NT.119, "-Unary")
 , {118} tableEntry(NT.T'.117, 1#"Unary", Reduce.50, NT.119, "Unary")
 , {119} tableEntry(NT.!T.161, 1#"Id", T.120, T'.122, "Id.Unary")
 , {120} tableEntry(T, 1#".", NT.121, T'.122, ".Unary")
 , {121} tableEntry(NT.T'.117, 1#"Unary", Reduce.51, T'.122, "Unary")
 , {122} tableEntry(T', 1#"{", NT.123, NT.126, "{} Unary")
 , {123} tableEntry(NT.T.235, 1#"N", T.124, NT.126, "} Unary")
 , {124} tableEntry(T, 1#"}", NT.125, NT.126, "} Unary")
 , {125} tableEntry(NT.T'.117, 1#"Unary", Reduce.52, NT.126, "Unary")
 , {126} tableEntry(NT.127, 1#"Power", Reduce.53, Fail, "Power")
 , {127} tableEntry(NT.T'.133, 1#"Atom", NT.128, Fail, "Atom")
 , {128} tableEntry(NT.T'.129, 1#"Power'", Reduce.54, Fail, "")
 , {129} tableEntry(T', 1#"#", NT.130, T.131, "#Unary")
 , {130} tableEntry(NT.T'.117, 1#"Unary", Reduce*(55, T'.129), T.131, "Unary")
 , {131} tableEntry(T, 1#"^", NT.132, Success*, "^(1#"^") Unary")
 , {132} tableEntry(NT.T'.117, 1#"Unary", Reduce*(56, T'.129), Success*, "Unary")
 , {133} tableEntry(T', 1#"(", NT.134, T'.136, "(E)")
 , {134} tableEntry(NT.40, 1#"E", T.135, T'.136, "E)")
 , {135} tableEntry(T, 1#")", Reduce.57, T'.136, ")")
 , {136} tableEntry(T', 1#"[", NT.137, NT.140, "[E]")
 , {137} tableEntry(NT.40, 1#"E", NT.138, NT.140, "E]")
 , {138} tableEntry(NT.T.41, 1#"EL'", T.139, NT.140, "]")
 , {139} tableEntry(T, 1#"]", Reduce.58, NT.140, "]")
 , {140} tableEntry(NT.T.28, 1#"String", Reduce.59, NT.141, "String")
 , {141} tableEntry(NT.T'.180, 1#"Declare", NT.142, T'.144, "Declare E")
 , {142} tableEntry(NT.226, 1#"Declare'", NT.143, T'.144, "E")
 , {143} tableEntry(NT.40, 1#"E", Reduce.60, T'.144, "E")
 , {144} tableEntry(T', 1#"if", NT.145, NT.151, "if E then E else E")
 , {145} tableEntry(NT.40, 1#"E", T.146, NT.151, "E then E else E")
 , {146} tableEntry(T, 1#"then", NT.147, NT.151, "then E else E")
 , {147} tableEntry(NT.40, 1#"E", NT.148, NT.151, "E else E")
 , {148} tableEntry(NT.T.171, 1#"IF", T.149, NT.151, "else E")
 , {149} tableEntry(T, 1#"else", NT.150, NT.151, "else E")
 , {150} tableEntry(NT.40, 1#"E", Reduce.61, NT.151, "E")
 , {151} tableEntry(NT.157, 1#"Name", T.152, Fail, "Name (E)")
 , {152} tableEntry(T, 1#"(", NT.153, NT.156, "(E)")
 , {153} tableEntry(NT.40, 1#"E", NT.154, NT.156, "E)")
 , {154} tableEntry(NT.T.41, 1#"EL'", T.155, NT.156, ")")
 , {155} tableEntry(T, 1#")", Reduce.62, NT.156, ")")
 , {156} tableEntry(NT.157, 1#"Name", Reduce.63, Fail, "Name")
 , {157} tableEntry(NT.!T.161, 1#"Id", T.158, Fail, "Id:Type")
 , {158} tableEntry(T, 1#":", NT.159, NT.160, ":Type")
 , {159} tableEntry(NT.176, 1#"Type", Reduce.64, NT.160, "Type")
 , {160} tableEntry(NT.!T.161, 1#"Id", Reduce.65, Fail, "Id")
 , {161} tableEntry(!T, 1#",", Fail, !T.162, ", any")
 , {162} tableEntry(!T, 1#"[", Fail, !T.163, "[any")
 , {163} tableEntry(!T, 1#"(", Fail, !T.164, "(any")
 , {164} tableEntry(!T, 1#"]", Fail, !T.165, "] any")
 , {165} tableEntry(!T, 1#")", Fail, !T.166, ") any")
 , {166} tableEntry(!T, 1#":", Fail, !T.167, ":any")
 , {167} tableEntry(!T, 1#".", Fail, !T.168, ".any")
 , {168} tableEntry(!T, 1#dq, Fail, MatchAny.169, "^(1#dq) any")
 , {169} tableEntry(MatchAny, 1#"?", Reduce.66, Fail, "any")
 , {170} tableEntry(T, 1#",", Reduce.67, Reduce.68, ",")
 , {171} tableEntry(T, 1#"else", T.172, Success*, "else if E then E")
 , {172} tableEntry(T, 1#"if", NT.173, Success*, "if E then E")
 , {173} tableEntry(NT.40, 1#"E", T.174, Success*, "E then E")
 , {174} tableEntry(T, 1#"then", NT.175, Success*, "then E")
 , {175} tableEntry(NT.40, 1#"E", Reduce*(69, T.171), Success*, "E")
 , {176} tableEntry(NT.!T.161, 1#"Id", T.177, Fail, "Id.Type")
 , {177} tableEntry(T, 1#".", NT.178, NT.179, ".Type")
 , {178} tableEntry(NT.176, 1#"Type", Reduce.70, NT.179, "Type")
 , {179} tableEntry(NT.!T.161, 1#"Id", Reduce.71, Fail, "Id")
 , {180} tableEntry(T', 1#"let", MatchAny.181, T'.185, "let any = E")
 , {181} tableEntry(MatchAny, 1#"?", T.182, T'.185, "any = E")
 , {182} tableEntry(T, 1#"=", NT.183, T'.185, "= E")
 , {183} tableEntry(NT.40, 1#"E", NT.184, T'.185, "E")
 , {184} tableEntry(NT.T.170, 1#"comma?", Reduce.72, T'.185, "")
 , {185} tableEntry(T', 1#"assert", NT.186, T'.190, "assert E report E")
 , {186} tableEntry(NT.40, 1#"E", T.187, T'.190, "E report E")
 , {187} tableEntry(T, 1#"report", NT.188, T'.190, "report E")
 , {188} tableEntry(NT.40, 1#"E", NT.189, T'.190, "E")
 , {189} tableEntry(NT.T.170, 1#"comma?", Reduce.73, T'.190, "")
 , {190} tableEntry(T', 1#"{", NT.191, T'.194, "{}")
 , {191} tableEntry(NT.T.235, 1#"N", T.192, T'.194, "}")
 , {192} tableEntry(T, 1#"}", NT.193, T'.194, "}")
 , {193} tableEntry(NT.T.170, 1#"comma?", Reduce.74, T'.194, "")
 , {194} tableEntry(T', 1#"for", NT.195, Fail, "for ForDeclare do E")
 , {195} tableEntry(NT.206, 1#"ForDeclare", T'.196, Fail, "ForDeclare do E")
 , {196} tableEntry(T', 1#"do", NT.197, T.201, "do E")
 , {197} tableEntry(NT.40, 1#"E", NT.198, T.199, "E")
 , {198} tableEntry(NT.T.170, 1#"comma?", Reduce.75, T.199, "")
 , {199} tableEntry(T, 1#"for", NT.200, Fail, "for ForDeclare while E do E")
 , {200} tableEntry(NT.206, 1#"ForDeclare", T.201, Fail, "ForDeclare while E do E")
 , {201} tableEntry(T, 1#"while", NT.202, Fail, "while E do E")
 , {202} tableEntry(NT.40, 1#"E", T.203, Fail, "E do E")
 , {203} tableEntry(T, 1#"do", NT.204, Fail, "do E")
 , {204} tableEntry(NT.40, 1#"E", NT.205, Fail, "E")
 , {205} tableEntry(NT.T.170, 1#"comma?", Reduce.76, Fail, "")
 , {206} tableEntry(NT.!T.217, 1#"AccumList", T'.207, Fail, "AccumList, any ∈ E")
 , {207} tableEntry(T', 1#",", MatchAny.208, T.212, ", any ∈ E")
 , {208} tableEntry(MatchAny, 1#"?", T'.209, NT.211, "any ∈ E")
 , {209} tableEntry(T', 1#"∈", NT.210, T.214, "∈ E")
 , {210} tableEntry(NT.40, 1#"E", Reduce.77, NT.211, "E")
 , {211} tableEntry(NT.!T.217, 1#"AccumList", T.212, Fail, "AccumList, any /in E")
 , {212} tableEntry(T, 1#",", MatchAny.213, NT.216, ", any /in E")
 , {213} tableEntry(MatchAny, 1#"?", T.214, NT.216, "any /in E")
 , {214} tableEntry(T, 1#"/in", NT.215, NT.216, "/in E")
 , {215} tableEntry(NT.40, 1#"E", Reduce.78, NT.216, "E")
 , {216} tableEntry(NT.!T.217, 1#"AccumList", Reduce.79, Fail, "AccumList")
 , {217} tableEntry(!T, 1#"while", Fail, MatchAny.218, "while any = E")
 , {218} tableEntry(MatchAny, 1#"?", T.219, Fail, "any = E")
 , {219} tableEntry(T, 1#"=", NT.220, Fail, "= E")
 , {220} tableEntry(NT.40, 1#"E", NT.221, Fail, "E")
 , {221} tableEntry(NT.T.222, 1#"AccumList'", Reduce.80, Fail, "")
 , {222} tableEntry(T, 1#",", MatchAny.223, Success*, ", any = E")
 , {223} tableEntry(MatchAny, 1#"?", T.224, Success*, "any = E")
 , {224} tableEntry(T, 1#"=", NT.225, Success*, "= E")
 , {225} tableEntry(NT.40, 1#"E", Reduce*(81, T.222), Success*, "E")
 , {226} tableEntry(NT.T'.180, 1#"Declare", Reduce*(82, NT.226), Success*, "Declare")
 , {227} tableEntry(NT.MatchAny.231, 1#"FP", NT.228, Fail, "FP")
 , {228} tableEntry(NT.T.229, 1#"FPL'", Reduce.83, Fail, "")
 , {229} tableEntry(T, 1#",", NT.230, Success*, ", FP")
 , {230} tableEntry(NT.MatchAny.231, 1#"FP", Reduce*(84, T.229), Success*, "FP")
 , {231} tableEntry(MatchAny, 1#"?", T.232, NT.234, "any:Type")
 , {232} tableEntry(T, 1#":", NT.233, NT.234, ":Type")
 , {233} tableEntry(NT.176, 1#"Type", Reduce.85, NT.234, "Type")
 , {234} tableEntry(NT.176, 1#"Type", Reduce.86, Fail, "Type")
 , {235} tableEntry(T, 1#"{", NT.236, !T.238, "{}")
 , {236} tableEntry(NT.T.235, 1#"N", T.237, !T.238, "}")
 , {237} tableEntry(T, 1#"}", Discard*.T.235, !T.238, "}")
 , {238} tableEntry(!T, 1#"}", All, MatchAny.239, "} any")
 , {239} tableEntry(MatchAny, 1#"?", Discard*.T.235, All, "any")
 , {240} tableEntry(!T, 1#dq, All, !T.241, "^(1#dq) any")
 , {241} tableEntry(!T, 1#"^", All, MatchAny.242, "^(1#"^") any")
 , {242} tableEntry(MatchAny, 1#"?", Discard*.!T.240, All, "any")
]

function =(seq.word, bindinfo) boolean true

function $(int) bindinfo 1#empty:seq.bindinfo

use standard

use seq.tableEntry

use otherseq.frame

use stack.frame

use otherseq.bindinfo

use PEGrules

function recoveryEnding(rinfo:recoverInfo) seq.word
for acc = "", frame ∈ reverse.toseq.stk.rinfo
do
 if action.Sstate.frame ∈ [T, T', NT] then acc + recover.(index.Sstate.frame)#mytable
 else acc,
acc

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.bindinfo
, faili:int
, failresult:seq.bindinfo

type recoverInfo is stk:stack.frame, input:seq.word, place:int

Function status(a:recoverInfo) word
if Sstate.top.stk.a ≠ Match then 1#"Failed"
else if place.a = {length of input} faili.top.stk.a then 1#"Match"
else 1#"MatchPrefix"

Function result(a:recoverInfo) bindinfo 1^result.top.stk.a

function parse(myinput0:seq.word, initAttr:bindinfo, common:commonType) recoverInfo
let myinput = packed(myinput0 + endMark)
let packedTable = packed.mytable
for
 rinfo = recoverInfo(empty:stack.frame, myinput, 0)
 , stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = 1#myinput
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
  let newrinfo = if i > place.rinfo then recoverInfo(stk, myinput, i) else rinfo,
  next(newrinfo, stk, nextState.state, i, inputi, result.top, i, result.top)
 else if actionState = All then
  let top = top.stk
  let att = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
  next(rinfo, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
 else if actionState = Lambda then
  let newrinfo = if i > place.rinfo then recoverInfo(stk, myinput, i) else rinfo
  let att = [action(reduceNo.state, result, common, newrinfo)],
  next(newrinfo, stk, nextState2.state, i, inputi, result + att, faili, failresult)
 else if actionState = Reduce then
  let top = top.stk
  let newrinfo = if i > place.rinfo then recoverInfo(stk, myinput, i) else rinfo,
  let att = [action(reduceNo.state, result, common, newrinfo)],
  next(newrinfo, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
 else if actionState = Reduce* then
  let newrinfo = if i > place.rinfo then recoverInfo(stk, myinput, i) else rinfo
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
  if inputi = endMark then {fail} next(rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   let reslt = result + toAttribute(1^result, [inputi])
   let ini = idxNB(myinput, i + 1),
   next(rinfo, stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
 else if actionState = T' then
  let te = idxNB(packedTable, index.state),
  if inputi = match.te then next(rinfo, stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else next(rinfo, stk, Fstate.te, i, inputi, result, faili, failresult)
 else
  {match non Terminal}
  let te = idxNB(packedTable, index.state)
  assert action.action.te ∈ [NT, NT*] report "PROBLEM PEG^(state)"
  let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult)),
  let tmp = [toAttribute(1^result, empty:seq.word)],
  next(rinfo, newstk, nextState.action.te, i, inputi, tmp, i, tmp),
recoverInfo(
 push(stk.rinfo, frame(state, state, place.rinfo, result, n.myinput, result))
 , input.rinfo
 , place.rinfo
) 