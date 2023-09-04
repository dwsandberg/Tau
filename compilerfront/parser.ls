Module parser

use PEGrules

use UTF8

use seq.char

use mytype

use otherseq.mytype

use seq.mytype

use set.mytype

use newPretty

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
{OPTION PROFILE}
let b = bindinfo(dict, empty:seq.symbol, empty:seq.mytype, "")
let r = parse(packed.input, mytable, b, commonType(types, outText, input))
assert status.r ∈ "Match"
report errormessage("syntax error", input, i.top.stk.r, pop.stk.r),
code.result.r

function toAttribute(b:bindinfo, w:seq.word) bindinfo
bindinfo(dict.b, empty:seq.symbol, empty:seq.mytype, w)

Function errormessage(
 message:seq.word
 , input:seq.word
 , place:int
 , parsestk:stack.frame
) seq.word
let ending = recovery.parsestk
let pp = prettyNoChange(subseq(input, 1, place - 1) + ending)
let debug =
 if false then
  for txt = "/br", f ∈ toseq.parsestk do txt + %.Sstate.f,
   txt
   + "/br"
   + showZ(subseq(input, 1, place - 1) + ending)
   + "/br"
   + showZ.subseq(pp, n.pp - 10, n.pp)
   + "/br"
   + ending
 else ""
for
 idx = n.pp
 , remove = ending
 , addback = ""
 , go = not.isempty.ending
 , idx0 ∈ arithseq(n.pp,-1, n.pp)
while go
do
 let e = idx_pp,
  if e ∈ "*>^(escapeformat)" then
  next(idx + 1, remove, [e] + addback, go)
  else if e = 1^remove then
  next(idx + 1, remove >> 1, addback, n.remove > 1)
  else if e ∈ "/keyword /br" then
  next(idx + 1, remove, addback, go)
  else next(idx + 1, remove, addback, false)
let t = "<* literal^(message) *>" + debug + "/br" + subseq(pp, 1, idx)
let unprocessed = subseq(input, place, place + 10),
(if not.isempty.t ∧ 1^t ∈ "/keyword" then t >> 1 + addback else t + addback)
 + "/br <* literal^(message) *> /br"
 + 
 if isempty.unprocessed then
 "at end but expecting:^(ending)"
 else "part of unprocessed input: ^(unprocessed)"

function showZ(out:seq.word) seq.word
for acc = "", w ∈ out do acc + encodeword(decodeword.w + char1."Z"),
acc

Function binary(R0:bindinfo, op:seq.word, R1:bindinfo) bindinfo
bindinfo(dict.R0, code.R0 + code.R1, types.R0 + types.R1, text.R0 + text.R1 + op + %.n.code.R1)

Function binaryops(
 static:commonType
 , R0:bindinfo
 , R1:bindinfo
 , place:int
 , parsestk:stack.frame
) bindinfo
if isempty.text.R1 then
R0
else
 let dict = dict.R0
 for arg1code = code.R0, arg1type = types.R0, start = 1, ops = text.R1, arg2type ∈ types.R1
 do
  let types = arg1type + arg2type
  let op = [1_ops]
  let len = toint.2_ops
  let arg2code = subseq(code.R1, start, start + len - 1),
   if 1_op ∈ "∧ ∨" ∧ types = [typeboolean, typeboolean] ∧ not.outText.static then
    let code =
     if op = "∧" then
     ifthenelse(arg1code, arg2code, [Litfalse], typeboolean)
     else ifthenelse(arg1code, [Littrue], arg2code, typeboolean),
    next(code, [typeboolean], start + len, ops << 2)
   else
    let f =
     if op = "≠" then
     [lookupbysig(static, dict, "=", types, place, parsestk), NotOp]
     else if op = "∉" then
     [lookupbysig(static, dict, "∈", types, place, parsestk), NotOp]
     else if op = "≥" then
     [lookupbysig(static, dict, "<", types, place, parsestk), NotOp]
     else if op = "≤" then
     [lookupbysig(static, dict, ">", types, place, parsestk), NotOp]
     else [lookupbysig(static, dict, [1_op], types, place, parsestk)],
    next(arg1code + arg2code + f, [resulttype.1_f], start + len, ops << 2),
 bindinfo(dict, arg1code, arg1type, "")

function strExp(
 static:commonType
 , R0:bindinfo
 , str2:bindinfo
 , more:seq.word
 , forcecode:boolean
 , place:int
 , parsestk:stack.frame
) bindinfo
let t = seqof.typeword,
if isempty.code.R0 then
 if forcecode then
 bindinfo(dict.R0, [Words(text.R0 + text.str2)], [t], "")
 else bindinfo(dict.R0, code.R0, types.R0, text.R0 + text.str2 + more)
else if isempty(text.str2 + more) then
R0
else
 let f = lookupbysig(static, dict.R0, "+", [t, t], place, parsestk),
 bindinfo(dict.R0, code.R0 + Words(text.str2 + more) + f, [t], "")

function strExp(
 static:commonType
 , R0:bindinfo
 , str2:bindinfo
 , exp:bindinfo
 , place:int
 , parsestk:stack.frame
) bindinfo
let t = seqof.typeword
let f = lookupbysig(static, dict.exp, "+", [t, t], place, parsestk)
let code1 =
 if isempty.code.R0 then
 [Words(text.R0 + text.str2)]
 else if isempty.text.str2 then
 code.R0
 else code.R0 + Words.text.str2 + f
let codeexp =
 if 1_types.exp = t then
 code.exp
 else
  let cvt = lookupbysig(static, dict.exp, "%", types.exp, place, parsestk)
  assert resulttype.cvt = seqof.typeword
  report errormessage("Expected function^(cvt) to have return type of seq.word", input.static, place, parsestk),
  code.exp + cvt,
bindinfo(dict.R0, code1 + codeexp + f, [t], "")

Function ifExp(
 static:commonType
 , R0:bindinfo
 , cond:bindinfo
 , thenpart:bindinfo
 , place:int
 , parsestk:stack.frame
) bindinfo
assert 1_types.cond = typeboolean
report errormessage("cond of if must be boolean but is^(1_types.cond)", input.static, place, parsestk)
assert isempty.types.R0 ∨ types.R0 = types.thenpart
report errormessage("then and else types are different", input.static, place, parsestk),
bindinfo(dict.R0, code.R0 + code.cond + Br2(1, 2) + code.thenpart + Exit, types.thenpart, "")

function ifExp(
 static:commonType
 , cond:bindinfo
 , thenpart:bindinfo
 , elseifpart:bindinfo
 , elsepart:bindinfo
 , place:int
 , parsestk:stack.frame
) bindinfo
let t = ifExp(static, toAttribute(cond, ""), cond, thenpart, place, parsestk)
assert
 types.thenpart = types.elsepart
 ∧ (isempty.types.elseifpart ∨ types.elseifpart = types.thenpart)
report errormessage("then and else types are different", input.static, place, parsestk),
bindinfo(
 dict.cond
 , [Start.1_types.thenpart]
  + code.t
  + code.elseifpart
  + if outText.static then code.elsepart + EndBlock else code.elsepart + Exit + EndBlock
 , types.elsepart
 , ""
)

function declarePara(d:symboldict, names:seq.word, types:seq.mytype) bindinfo
for dict = d, no = 1, t ∈ types do next(dict + Local(no_names, t, no), no + 1),
bindinfo(dict, empty:seq.symbol, empty:seq.mytype, "")

function lookupbysig(
 static:commonType
 , dict:symboldict
 , name:seq.word
 , paratypes:seq.mytype
 , place:int
 , parsestk:stack.frame
) symbol
let sym3 =
 if n.name = 1 then
 symbol(internalmod, name, paratypes, typeint)
 else symbol4(internalmod, 1_name, resolvetype(static, name << 1, place, parsestk), paratypes, typeint)
let f0 = lookupbysig(dict, sym3)
let f =
 if n.f0 < 2 then
 f0
 else for acc = empty:set.symbol, sy ∈ toseq.f0 do if isunbound.sy then acc else acc + sy, acc
assert not.isempty.f
report errormessage(
 "cannot find 1^(if n.name = 1 then name else [1_name, 1_":"] + name << 1) (
  ^(for acc = "", @e ∈ paratypes do acc + %.@e + ",", acc >> 1))"
 , input.static
 , place
 , parsestk
)
assert n.f = 1
report errormessage(
 "found more than one
  ^(for acc = "", @e ∈ toseq.f do acc + library.module.@e + "." + %.@e, acc)"
 , input.static
 , place
 , parsestk
)
let discard =
 for acc = 0, sym2 ∈ requires(dict, 1_f)
 do
  let xxx = lookupbysig(dict, sym2)
  assert not.isempty.xxx ∨ isAbstract.module.1_f
  report errormessage("using symbol^(1_f) requires unbound^(sym2)", input.static, place, parsestk),
  0,
 0,
1_f

Function addpara(
 static:commonType
 , name:seq.word
 , ptype:bindinfo
 , place:int
 , parsestk:stack.frame
) bindinfo
let b = ptype
let paratype = resolvetype(static, text.ptype, place, parsestk)
assert isempty.lookupbysig(dict.b, name) ∨ name = ":"
report errormessage("duplciate symbol:^(name)", input.static, place, parsestk),
bindinfo(dict.b, empty:seq.symbol, [paratype], name)

Function addpara(
 static:commonType
 , b:bindinfo
 , name:seq.word
 , ptype:bindinfo
 , place:int
 , parsestk:stack.frame
) bindinfo
let paratype = resolvetype(static, text.ptype, place, parsestk)
assert isempty.lookupbysig(dict.b, name) ∨ name = ":"
report errormessage("duplciate symbol:^(name)", input.static, place, parsestk),
bindinfo(
 dict.b + Local(1_name, paratype, n.text.b + 1)
 , empty:seq.symbol
 , empty:seq.mytype
 , text.b + name
)

Function seq(static:commonType, R:bindinfo, place:int, parsestk:stack.frame) bindinfo
let types = types.R
assert for acc = true, @e ∈ types do acc ∧ 1_types = @e, acc
report errormessage("types do not match in build", input.static, place, parsestk),
bindinfo(dict.R, code.R + Sequence(1_types, n.types), [seqof.1_types], "")

Function letExp(
 static:commonType
 , R:bindinfo
 , exp:bindinfo
 , place:int
 , parsestk:stack.frame
) bindinfo
let name = text.R
assert isempty.lookupbysig(dict.R, name)
report errormessage("duplicate symbol:^(name)", input.static, place, parsestk)
let newdict = dict.R + Local(1_name, 1_types.exp, cardinality.dict.R),
bindinfo(newdict, code.R + code.exp + Define(1_name, cardinality.dict.R), types.exp, name)

Function bindlit2(
 static:commonType
 , R:bindinfo
 , place:int
 , parsestk:stack.frame
) bindinfo
assert not.isempty.text.R report "bindlit2"
let chars = decodeword.1_text.R,
if not.checkfirstdigit.chars then
 let f = lookupbysig(static, dict.R, text.R, empty:seq.mytype, place, parsestk),
 bindinfo(dict.R, [f], [resulttype.f], "")
else
 let rt = if n.chars > 1 ∧ 2_chars ∈ decodeword.1_"Xx" then typebits else typeint,
 bindinfo(
  dict.R
  , [if outText.static then symbol(internalmod, text.R, rt) else Lit.cvttoint.chars]
  , [rt]
  , ""
 )

function checkfirstdigit(chars:seq.char) boolean
let i = if n.chars > 1 ∧ 1_chars = char1."-" then 2 else 1,
between(toint.i_chars, 48, 57)

Function unaryop(
 static:commonType
 , dict:symboldict
 , place:int
 , parsestk:stack.frame
 , op:seq.word
 , exp:bindinfo
) bindinfo
if 1_op = 1_"process" ∧ n.types.exp = 1 then
 let rt = 1_resolvetype(types.static, %.1_types.exp)
 let processtype = processof.rt
 let dcws = deepcopyseqword
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
else
 let chars = decodeword.1_op,
  if checkfirstdigit.chars ∧ n.code.exp = 1 then
   let dec =
    if outText.static then
    name.1_code.exp
    else
     assert isIntLit.1_code.exp
     report errormessage("illformed real literal", input.static, place, parsestk),
     place_input.static,
   bindinfo(dict, [Words(op + "." + dec), makerealSymbol], [typereal], "")
  else
   let f = lookupbysig(static, dict, op, types.exp, place, parsestk),
   bindinfo(dict, code.exp + f, [resulttype.f], "")

function resolvetype(
 static:commonType
 , text:seq.word
 , place:int
 , parsestk:stack.frame
) mytype
let a = resolvetype(types.static, text)
assert not.isempty.a
report errormessage("cannot resolve type^(text)", input.static, place, parsestk),
1_a

Function checktype(
 static:commonType
 , functype:bindinfo
 , Declare:bindinfo
 , exp:bindinfo
 , place:int
 , parsestk:stack.frame
) bindinfo
let returntype = resolvetype(static, text.functype, place, parsestk)
assert returntype = 1_types.exp
report errormessage(
 "function type of^(returntype) does not match expression type^(1_types.exp)"
 , input.static
 , place
 , parsestk
),
bindinfo(dict.exp, mergeText(static, code.Declare, code.exp), empty:seq.mytype, "")

Function forSeqExp(
 static:commonType
 , accum0:bindinfo
 , elename:seq.word
 , theseq:bindinfo
 , place:int
 , parsestk:stack.frame
) bindinfo
let noseq = elename = "."
let oldnesting = lookupbysig(dict.accum0, "for")
let basetype = typebase.cardinality.dict.accum0
{we declare accumulators after all initial values are calculated since initial values may change
 size of symboldict. }
for accdict = dict.accum0, i = 1, name ∈ text.accum0
do
 assert isempty.lookupbysig(dict.accum0, [name])
 report errormessage("duplicate symbol:^(name)", input.static, place, parsestk)
 let z = Local(name, i_types.accum0, cardinality.accdict),
 next(accdict + z, i + 1)
let seqtype =
 if noseq then
 seqof.typeint
 else
  let seqtype0 = 1_types.theseq
  assert isempty.lookupbysig(accdict, elename)
  report errormessage("duplicate symbol:^(elename)", input.static, place, parsestk)
  assert isseq.seqtype0
  report errormessage(
   "final expression in for list must be a sequence but it is of type:^(seqtype0)"
   , input.static
   , place
   , parsestk
  ),
  seqtype0
{keep track so right next is used in nested fors}
let lastaccum = cardinality.accdict - 1
let elementSym = Local(1_elename, parameter.seqtype, lastaccum + 2)
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
 , place:int
 , parsestk:stack.frame
) bindinfo
assert 1_types.cond = typeboolean
report errormessage("condition in assert must be boolean in:", input.static, place, parsestk)
assert 1_types.exp = seqof.typeword
report errormessage("report in assert must be seq of word in:", input.static, place, parsestk),
if outText.static then
bindinfo(
 dict.cond
 , code.cond + code.exp + symbol(internalmod, "$assert", typeboolean, seqof.typeword, typeint)
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
   + Define(1_"assert", cardinality.dict.cond)
  , empty:seq.mytype
  , ""
 )

Function forbody(
 static:commonType
 , vars:bindinfo
 , exitexp:bindinfo
 , forbodyin:bindinfo
 , place:int
 , parsestk:stack.frame
) bindinfo
let textvars = text.vars
let codevars = code.vars
let typesvars = types.vars
let accumTypes = typesvars >> 1
let theseqtype = 1^types.vars
let nowhile = code.exitexp = [Littrue]
let noseq = 1^text.vars ∈ "."
let forbodytype = resulttype.1_lookupbysig(dict.vars, "for")
let forbody =
 if n.accumTypes = 1 ∧ forbodytype = 1_types.forbodyin then
  {handle next with single accumulator}
  bindinfo(dict.forbodyin, code.forbodyin >> 1, [1_accumTypes], text.forbodyin)
 else forbodyin
let actualbodytype = 1_types.forbody
let checktypes =
 if 1_types.exitexp = typeboolean then
  {while type is OK. now check body type}
  if n.accumTypes > 1 then
  if forbodytype = actualbodytype then "" else "incorrect body type:^(actualbodytype)"
  else if 1_accumTypes = actualbodytype then
   {body type is OK, now check to see if while clause is required}
   if noseq ∧ code.exitexp = [Littrue] then
   "While clause must be present and not equal to true when no sequence is specified."
   else ""
  else "Type of body expression^(actualbodytype) must match accumulator type^(1_accumTypes)"
 else "while expresssion type must be boolean"
assert isempty.checktypes report errormessage(checktypes, input.static, place, parsestk)
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
    + 1_types.forbody
    + seqof.typeword
   , typeint
  )
 else
  let firstvar = toint.1_%.parameter.forbodytype
  let lastidx = Local(firstvar + n.accumTypes)
  let theseq = Local(value.lastidx + 2)
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
    let setElement = [
     lastidx
     , if reverse then Lit.-1 else Lit.1
     , PlusOp
     , Define.value.masterindex
     , {let sequenceele = seq_(idx)} theseq
     , masterindex
     , symbol(builtinmod.theseqtype, "idxNB", seqof.theseqtype, typeint, theseqtype)
     , Define(value.lastidx + 1)
    ]
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
     + 
      if nowhile then
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
if outText.static ∧ not.isempty.a ∧ not.isempty.b then
a + b + symbol(internalmod, "$mergecode", typeint, typeint, typeint)
else a + b

function slash word 1_"/"

function /All word 1_"All"

function endMark word encodeword.[char.254]

function PEGgen(
 seqElementType:word
 , attributeType:bindinfo
 , runresultType:runresult
 , R:reduction
 , place:int
 , parsestk:stack.frame
 , error:boolean
 , common:commonType
 , recover:boolean
) seq.boolean
[
 "match2code carrot" = 1_"^"
 , "/ slash" = slash
 , "/ dq" = 1_dq
 , "/ any" = 1_"/1"
 , "S function Name (FPL) Type Declare' E"
  = checktype(common, 3_R, 4_R, 5_R, place, parsestk)
 , "/ function Name Type Declare' E" = checktype(common, 2_R, 3_R, 4_R, place, parsestk)
 , "/ Function Name (FPL) Type Declare' E"
  = checktype(common, 3_R, 4_R, 5_R, place, parsestk)
 , "/ Function Name Type Declare' E" = checktype(common, 2_R, 3_R, 4_R, place, parsestk)
 , "String dq String' str2 dq" = strExp(common, 1_R, 2_R, "", true, place, parsestk)
 , "* String' str2 carrot (E)" = strExp(common, 0_R, 1_R, 2_R, place, parsestk)
 , "/ str2 carrot" = strExp(common, 0_R, 1_R, "^", false, place, parsestk)
 , "/ str2" = strExp(common, 0_R, 1_R, "", false, place, parsestk)
 , "* str2 ! dq ! carrot any" = /All
 , "E Or" = 1_R
 , "* EL', E" = bindinfo(dict.0_R, code.0_R + code.1_R, types.0_R + types.1_R, "")
 , "Or And Or'" = binaryops(common, 1_R, 2_R, place, parsestk)
 , "* Or' ∨ And" = binary(0_R, "∨", 1_R)
 , "/ /or And" = binary(0_R, "∨", 1_R)
 , "/ ⊻ And" = binary(0_R, "⊻", 1_R)
 , "And Compare And'" = binaryops(common, 1_R, 2_R, place, parsestk)
 , "* And' ∧ Compare" = binary(0_R, "∧", 1_R)
 , "/ /and Compare" = binary(0_R, "∧", 1_R)
 , "Compare Sum Compare'" = binaryops(common, 1_R, 2_R, place, parsestk)
 , "* Compare' = Sum" = binary(0_R, "=", 1_R)
 , "/ ≠ Sum" = binary(0_R, "≠", 1_R)
 , "/ > Sum" = binary(0_R, ">", 1_R)
 , "/ < Sum" = binary(0_R, "<", 1_R)
 , "/ >1 Sum" = binary(0_R, ">1", 1_R)
 , "/ >2 Sum" = binary(0_R, ">2", 1_R)
 , "/ ≥ Sum" = binary(0_R, "≥", 1_R)
 , "/ /ge Sum" = binary(0_R, "≥", 1_R)
 , "/ ≤ Sum" = binary(0_R, "≤", 1_R)
 , "/ /le Sum" = binary(0_R, "≤", 1_R)
 , "/ /ne Sum" = binary(0_R, "≠", 1_R)
 , "Sum Product Sum'" = binaryops(common, 1_R, 2_R, place, parsestk)
 , "* Sum'-Product" = binary(0_R, "-", 1_R)
 , "/+Product" = binary(0_R, "+", 1_R)
 , "/ ∈ Product" = binary(0_R, "∈", 1_R)
 , "/ /in Product" = binary(0_R, "∈", 1_R)
 , "/ ∉ Product" = binary(0_R, "∉", 1_R)
 , "/ /nin Product" = binary(0_R, "∉", 1_R)
 , "Product Unary Product'" = binaryops(common, 1_R, 2_R, place, parsestk)
 , "* Product' * Unary" = binary(0_R, "*", 1_R)
 , "/ >> Unary" = binary(0_R, ">>", 1_R)
 , "/ << Unary" = binary(0_R, "<<", 1_R)
 , "/ slash Unary" = binary(0_R, [slash], 1_R)
 , "/ mod Unary" = binary(0_R, "mod", 1_R)
 , "/ ∩ Unary" = binary(0_R, "∩", 1_R)
 , "/ ∪ Unary" = binary(0_R, "∪", 1_R)
 , "/ /cap Unary" = binary(0_R, "∩", 1_R)
 , "/ /cup Unary" = binary(0_R, "∪", 1_R)
 , "/ \ Unary" = binary(0_R, "\", 1_R)
 , "Unary-Unary" = unaryop(common, dict.1_R, place, parsestk, "-", 1_R)
 , "/ Id.Unary" = unaryop(common, dict.1_R, place - 1, parsestk, text.1_R, 2_R)
 , "/ {N} Unary"
  = 
   if outText.common then
   bindinfo(
    dict.2_R
    , [Words.text.1_R]
     + code.2_R
     + symbol(internalmod, "{", seqof.typeword, 1_types.2_R, 1_types.2_R)
    , types.2_R
    , ""
   )
   else 2_R
 , "/ Power" = 1_R
 , "Power Atom Power'" = binaryops(common, 1_R, 2_R, place, parsestk)
 , "* Power'_Unary" = binary(0_R, "_", 1_R)
 , "/^Unary" = binary(0_R, "^", 1_R)
 , "Atom (E)" = 1_R
 , "/ [E EL']"
  = seq(
   common
   , bindinfo(dict.1_R, code.1_R + code.2_R, types.1_R + types.2_R, "")
   , place
   , parsestk
  )
 , "/ String" = 1_R
 , "/ Declare Declare' E"
  = bindinfo(
   dict.0_R
   , mergeText(common, mergeText(common, code.1_R, code.2_R), code.3_R)
   , types.3_R
   , ""
  )
 , "/ if E then E IF else E" = ifExp(common, 1_R, 2_R, 3_R, 4_R, place, parsestk)
 , "/ Name (E EL')"
  = unaryop(
   common
   , dict.1_R
   , place
   , parsestk
   , text.1_R
   , bindinfo(dict.2_R, code.2_R + code.3_R, types.2_R + types.3_R, "")
  )
 , "/ Name" = bindlit2(common, 1_R, place, parsestk)
 , "Name Id:Type"
  = bindinfo(dict.1_R, empty:seq.symbol, empty:seq.mytype, text.1_R + text.2_R)
 , "/ Id" = 1_R
 , "Id !, ! [! (!] !) !:!.! dq any" = 1_R
 , "comma?," = 0_R
 , "/" = 0_R
 , "* IF else if E then E" = ifExp(common, 0_R, 1_R, 2_R, place, parsestk)
 , "Type Id.Type"
  = bindinfo(dict.2_R, empty:seq.symbol, empty:seq.mytype, text.1_R + "." + text.2_R)
 , "/ Id" = 1_R
 , "Declare let any = E comma?" = letExp(common, 1_R, 2_R, place, parsestk)
 , "/ assert E report E comma?" = assertExp(common, 1_R, 2_R, place, parsestk)
 , "/ {N} comma?"
  = 
   if outText.common then
   bindinfo(
    dict.0_R
    , code.0_R + Words.text.1_R + symbol(internalmod, "{", seqof.typeword, typeint)
    , empty:seq.mytype
    , ""
   )
   else 0_R
 , "/ for ForDeclare do E comma?"
  = forbody(common, 1_R, bindinfo(dict.0_R, [Littrue], [typeboolean], ""), 2_R, place, parsestk)
 , "/ for ForDeclare while E do E comma?" = forbody(common, 1_R, 2_R, 3_R, place, parsestk)
 , "ForDeclare AccumList, any ∈ E"
  = forSeqExp(common, 1_R, text.2_R, 3_R, place, parsestk)
 , "/ AccumList, any /in E" = forSeqExp(common, 1_R, text.2_R, 3_R, place, parsestk)
 , "/ AccumList" = forSeqExp(common, 1_R, ".", 1_R, place, parsestk)
 , "AccumList Accum AccumList'"
  = bindinfo(dict.0_R, code.1_R + code.2_R, types.1_R + types.2_R, text.1_R + text.2_R)
 , "* AccumList', Accum"
  = bindinfo(dict.0_R, code.0_R + code.1_R, types.0_R + types.1_R, text.0_R + text.1_R)
 , "Accum ! while any = E" = bindinfo(dict.0_R, code.2_R, types.2_R, text.1_R)
 , "* Declare' Declare"
  = bindinfo(dict.1_R, mergeText(common, code.0_R, code.1_R), empty:seq.mytype, "")
 , "FPL FP FPL'"
  = declarePara(dict.1_R, text.1_R + text.2_R, types.1_R + types.2_R)
 , "* FPL', FP"
  = bindinfo(dict.0_R, empty:seq.symbol, types.0_R + types.1_R, text.0_R + text.1_R)
 , "FP any:Type" = addpara(common, text.1_R, 2_R, place, parsestk)
 , "/ Type" = addpara(common, 0_R, ":", 1_R, place, parsestk)
 , "* N {N}"
  = bindinfo(dict.0_R, empty:seq.symbol, empty:seq.mytype, text.0_R + "{^(text.1_R)}")
 , "/ str1"
  = bindinfo(dict.0_R, empty:seq.symbol, empty:seq.mytype, text.0_R + text.1_R)
 , "* str1 ! {!} any" = /All
]

<<<< Below is auto generated code >>>>

/br Non-terminals:Accum AccumList AccumList' And And' Atom Compare Compare' Declare Declare' E EL'
FP FPL FPL' ForDeclare IF Id N Name Or Or' Power Power' Product Product' S String String' Sum Sum' Type
Unary comma? str1 str2
/br Terminals:() *+,-./and /cap /cup /ge /in /le /ne /nin /or:< << = > >1 >2 >> Function [\]^
_any assert carrot do dq else for function if let mod report slash then while {} ∈ ∉ ∧ ∨ ∩ ∪ ≠ ≤ ≥
⊻
/br S ← function Name (FPL) Type Declare' E / function Name Type Declare' E
/br / Function Name (FPL) Type Declare' E
/br / Function Name Type Declare' E
/br String ← dq String' str2 dq
/br * String' ← str2 carrot (E) / str2 carrot / str2
/br * str2 ← ! dq ! carrot any
/br E ← Or
/br * EL' ←, E
/br Or ← And Or'
/br * Or' ← ∨ And / /or And / ⊻ And
/br And ← Compare And'
/br * And' ← ∧ Compare / /and Compare
/br Compare ← Sum Compare'
/br * Compare' ← = Sum / ≠ Sum / > Sum / < Sum
/br / >1 Sum
/br / >2 Sum
/br / ≥ Sum
/br / /ge Sum
/br / ≤ Sum
/br / /le Sum
/br / /ne Sum
/br Sum ← Product Sum'
/br * Sum' ←-Product /+Product / ∈ Product / /in Product
/br / ∉ Product
/br / /nin Product
/br Product ← Unary Product'
/br * Product' ← * Unary / >> Unary / << Unary / slash Unary
/br / mod Unary
/br / ∩ Unary
/br / ∪ Unary
/br / /cap Unary
/br / /cup Unary
/br / \ Unary
/br Unary ←-Unary / Id.Unary / {N} Unary
/br / Power
/br Power ← Atom Power'
/br * Power' ←_Unary /^Unary
/br Atom ← (E) / [E EL'] / String
/br / Declare Declare' E
/br / if E then E IF else E
/br / Name (E EL')
/br / Name
/br Name ← Id:Type / Id
/br Id ← !, ! [! (!] !) !:!.! dq any
/br comma? ←, /
/br * IF ← else if E then E
/br Type ← Id.Type / Id
/br Declare ← let any = E comma? / assert E report E comma?
/br / {N} comma?
/br / for ForDeclare do E comma?
/br / for ForDeclare while E do E comma?
/br ForDeclare ← AccumList, any ∈ E / AccumList, any /in E
/br / AccumList
/br AccumList ← Accum AccumList'
/br * AccumList' ←, Accum
/br Accum ← ! while any = E
/br * Declare' ← Declare
/br FPL ← FP FPL'
/br * FPL' ←, FP
/br FP ← any:Type / Type
/br * N ← {N} / str1
/br * str1 ← ! {!} any

function action(
 partno:int
 , R:reduction
 , place:int
 , input:seq.word
 , common:commonType
 , parsestk:stack.frame
) bindinfo
if partno = 2 then
checktype(common, 3_R, 4_R, 5_R, place, parsestk)
else if partno = 3 then
checktype(common, 2_R, 3_R, 4_R, place, parsestk)
else if partno = 4 then
checktype(common, 3_R, 4_R, 5_R, place, parsestk)
else if partno = 5 then
checktype(common, 2_R, 3_R, 4_R, place, parsestk)
else if partno = 6 then
strExp(common, 1_R, 2_R, "", true, place, parsestk)
else if partno = 7 then
strExp(common, 0_R, 1_R, 2_R, place, parsestk)
else if partno = 8 then
strExp(common, 0_R, 1_R, "^", false, place, parsestk)
else if partno = 9 then
strExp(common, 0_R, 1_R, "", false, place, parsestk)
else if partno = 11 then
1_R
else if partno = 12 then
bindinfo(dict.0_R, code.0_R + code.1_R, types.0_R + types.1_R, "")
else if partno = 13 then
binaryops(common, 1_R, 2_R, place, parsestk)
else if partno = 14 then
binary(0_R, "∨", 1_R)
else if partno = 15 then
binary(0_R, "∨", 1_R)
else if partno = 16 then
binary(0_R, "⊻", 1_R)
else if partno = 17 then
binaryops(common, 1_R, 2_R, place, parsestk)
else if partno = 18 then
binary(0_R, "∧", 1_R)
else if partno = 19 then
binary(0_R, "∧", 1_R)
else if partno = 20 then
binaryops(common, 1_R, 2_R, place, parsestk)
else if partno = 21 then
binary(0_R, "=", 1_R)
else if partno = 22 then
binary(0_R, "≠", 1_R)
else if partno = 23 then
binary(0_R, ">", 1_R)
else if partno = 24 then
binary(0_R, "<", 1_R)
else if partno = 25 then
binary(0_R, ">1", 1_R)
else if partno = 26 then
binary(0_R, ">2", 1_R)
else if partno = 27 then
binary(0_R, "≥", 1_R)
else if partno = 28 then
binary(0_R, "≥", 1_R)
else if partno = 29 then
binary(0_R, "≤", 1_R)
else if partno = 30 then
binary(0_R, "≤", 1_R)
else if partno = 31 then
binary(0_R, "≠", 1_R)
else if partno = 32 then
binaryops(common, 1_R, 2_R, place, parsestk)
else if partno = 33 then
binary(0_R, "-", 1_R)
else if partno = 34 then
binary(0_R, "+", 1_R)
else if partno = 35 then
binary(0_R, "∈", 1_R)
else if partno = 36 then
binary(0_R, "∈", 1_R)
else if partno = 37 then
binary(0_R, "∉", 1_R)
else if partno = 38 then
binary(0_R, "∉", 1_R)
else if partno = 39 then
binaryops(common, 1_R, 2_R, place, parsestk)
else if partno = 40 then
binary(0_R, "*", 1_R)
else if partno = 41 then
binary(0_R, ">>", 1_R)
else if partno = 42 then
binary(0_R, "<<", 1_R)
else if partno = 43 then
binary(0_R, [slash], 1_R)
else if partno = 44 then
binary(0_R, "mod", 1_R)
else if partno = 45 then
binary(0_R, "∩", 1_R)
else if partno = 46 then
binary(0_R, "∪", 1_R)
else if partno = 47 then
binary(0_R, "∩", 1_R)
else if partno = 48 then
binary(0_R, "∪", 1_R)
else if partno = 49 then
binary(0_R, "\", 1_R)
else if partno = 50 then
unaryop(common, dict.1_R, place, parsestk, "-", 1_R)
else if partno = 51 then
unaryop(common, dict.1_R, place - 1, parsestk, text.1_R, 2_R)
else if partno = 52 then
 if outText.common then
 bindinfo(
  dict.2_R
  , [Words.text.1_R]
   + code.2_R
   + symbol(internalmod, "{", seqof.typeword, 1_types.2_R, 1_types.2_R)
  , types.2_R
  , ""
 )
 else 2_R
else if partno = 53 then
1_R
else if partno = 54 then
binaryops(common, 1_R, 2_R, place, parsestk)
else if partno = 55 then
binary(0_R, "_", 1_R)
else if partno = 56 then
binary(0_R, "^", 1_R)
else if partno = 57 then
1_R
else if partno = 58 then
seq(
 common
 , bindinfo(dict.1_R, code.1_R + code.2_R, types.1_R + types.2_R, "")
 , place
 , parsestk
)
else if partno = 59 then
1_R
else if partno = 60 then
bindinfo(
 dict.0_R
 , mergeText(common, mergeText(common, code.1_R, code.2_R), code.3_R)
 , types.3_R
 , ""
)
else if partno = 61 then
ifExp(common, 1_R, 2_R, 3_R, 4_R, place, parsestk)
else if partno = 62 then
unaryop(
 common
 , dict.1_R
 , place
 , parsestk
 , text.1_R
 , bindinfo(dict.2_R, code.2_R + code.3_R, types.2_R + types.3_R, "")
)
else if partno = 63 then
bindlit2(common, 1_R, place, parsestk)
else if partno = 64 then
bindinfo(dict.1_R, empty:seq.symbol, empty:seq.mytype, text.1_R + text.2_R)
else if partno = 65 then
1_R
else if partno = 66 then
1_R
else if partno = 67 then
0_R
else if partno = 68 then
0_R
else if partno = 69 then
ifExp(common, 0_R, 1_R, 2_R, place, parsestk)
else if partno = 70 then
bindinfo(dict.2_R, empty:seq.symbol, empty:seq.mytype, text.1_R + "." + text.2_R)
else if partno = 71 then
1_R
else if partno = 72 then
letExp(common, 1_R, 2_R, place, parsestk)
else if partno = 73 then
assertExp(common, 1_R, 2_R, place, parsestk)
else if partno = 74 then
 if outText.common then
 bindinfo(
  dict.0_R
  , code.0_R + Words.text.1_R + symbol(internalmod, "{", seqof.typeword, typeint)
  , empty:seq.mytype
  , ""
 )
 else 0_R
else if partno = 75 then
forbody(common, 1_R, bindinfo(dict.0_R, [Littrue], [typeboolean], ""), 2_R, place, parsestk)
else if partno = 76 then
forbody(common, 1_R, 2_R, 3_R, place, parsestk)
else if partno = 77 then
forSeqExp(common, 1_R, text.2_R, 3_R, place, parsestk)
else if partno = 78 then
forSeqExp(common, 1_R, text.2_R, 3_R, place, parsestk)
else if partno = 79 then
forSeqExp(common, 1_R, ".", 1_R, place, parsestk)
else if partno = 80 then
bindinfo(dict.0_R, code.1_R + code.2_R, types.1_R + types.2_R, text.1_R + text.2_R)
else if partno = 81 then
bindinfo(dict.0_R, code.0_R + code.1_R, types.0_R + types.1_R, text.0_R + text.1_R)
else if partno = 82 then
bindinfo(dict.0_R, code.2_R, types.2_R, text.1_R)
else if partno = 83 then
bindinfo(dict.1_R, mergeText(common, code.0_R, code.1_R), empty:seq.mytype, "")
else if partno = 84 then
declarePara(dict.1_R, text.1_R + text.2_R, types.1_R + types.2_R)
else if partno = 85 then
bindinfo(dict.0_R, empty:seq.symbol, types.0_R + types.1_R, text.0_R + text.1_R)
else if partno = 86 then
addpara(common, text.1_R, 2_R, place, parsestk)
else if partno = 87 then
addpara(common, 0_R, ":", 1_R, place, parsestk)
else if partno = 88 then
bindinfo(dict.0_R, empty:seq.symbol, empty:seq.mytype, text.0_R + "{^(text.1_R)}")
else if partno = 89 then
bindinfo(dict.0_R, empty:seq.symbol, empty:seq.mytype, text.0_R + text.1_R)
else 0_R

function mytable seq.tableEntry
[
 {1} tableEntry(MatchNT.Match.2, 1_"?", Reduce.1, Reduce, "")
 , {2} tableEntry(Match, 1_"function", S.3, Match.10, "function any (any) any any")
 , {3} tableEntry(MatchNT.S.160, 1_"?", MatchNext.4, S.24, "any (any) any any")
 , {4} tableEntry(MatchNext, 1_"(", S.5, S.12, "(any) any any")
 , {5} tableEntry(MatchNT.S.229, 1_"?", Match.6, Match.10, "any) any any")
 , {6} tableEntry(Match, 1_")", S.7, Match.10, ") any any")
 , {7} tableEntry(MatchNT.S.179, 1_"?", S.8, Match.10, "any any")
 , {8} tableEntry(MatchNT.S.228, 1_"?", S.9, Match.10, "any")
 , {9} tableEntry(MatchNT.S.43, 1_"?", Reduce.2, Match.10, "any")
 , {10} tableEntry(Match, 1_"function", S.11, Match.15, "function any any any")
 , {11} tableEntry(MatchNT.S.160, 1_"?", S.12, Match.15, "any any any")
 , {12} tableEntry(MatchNT.S.179, 1_"?", S.13, Match.15, "any any")
 , {13} tableEntry(MatchNT.S.228, 1_"?", S.14, Match.15, "any")
 , {14} tableEntry(MatchNT.S.43, 1_"?", Reduce.3, Match.15, "any")
 , {15} tableEntry(Match, 1_"Function", S.16, Match.23, "Function any (any) any any")
 , {16} tableEntry(MatchNT.S.160, 1_"?", Match.17, Match.23, "any (any) any any")
 , {17} tableEntry(Match, 1_"(", S.18, Match.23, "(any) any any")
 , {18} tableEntry(MatchNT.S.229, 1_"?", Match.19, Match.23, "any) any any")
 , {19} tableEntry(Match, 1_")", S.20, Match.23, ") any any")
 , {20} tableEntry(MatchNT.S.179, 1_"?", S.21, Match.23, "any any")
 , {21} tableEntry(MatchNT.S.228, 1_"?", S.22, Match.23, "any")
 , {22} tableEntry(MatchNT.S.43, 1_"?", Reduce.4, Match.23, "any")
 , {23} tableEntry(Match, 1_"Function", S.24, Fail, "Function any any any")
 , {24} tableEntry(MatchNT.S.160, 1_"?", S.25, Fail, "any any any")
 , {25} tableEntry(MatchNT.S.179, 1_"?", S.26, Fail, "any any")
 , {26} tableEntry(MatchNT.S.228, 1_"?", S.27, Fail, "any")
 , {27} tableEntry(MatchNT.S.43, 1_"?", Reduce.5, Fail, "any")
 , {28} tableEntry(Match, 1_dq, S.29, Fail, "^(1_dq)^(1_dq)")
 , {29} tableEntry(MatchNT.S.32, 1_"?", S.30, Fail, "^(1_dq)")
 , {30} tableEntry(MatchNT.!Match.40, 1_"?", Match.31, Fail, "^(1_dq)")
 , {31} tableEntry(Match, 1_dq, Reduce.6, Fail, "^(1_dq)")
 , {32} tableEntry(MatchNT.!Match.40, 1_"?", MatchNext.33, S.37, "^(1_"^") (any)")
 , {33} tableEntry(MatchNext, 1_"^", MatchNext.34, Match.38, "^(1_"^") (any)")
 , {34} tableEntry(MatchNext, 1_"(", S.35, Reduce(8, S.32), "(any)")
 , {35} tableEntry(MatchNT.S.43, 1_"?", Match.36, S.37, "any)")
 , {36} tableEntry(Match, 1_")", Reduce(7, S.32), S.37, ")")
 , {37} tableEntry(MatchNT.!Match.40, 1_"?", Match.38, S.39, "^(1_"^")")
 , {38} tableEntry(Match, 1_"^", Reduce(8, S.32), S.39, "^(1_"^")")
 , {39} tableEntry(MatchNT.!Match.40, 1_"?", Reduce(9, S.32), Success*, "")
 , {40} tableEntry(!Match, 1_dq, All, !Match.41, "^(1_dq) any")
 , {41} tableEntry(!Match, 1_"^", All, MatchAny.42, "^(1_"^") any")
 , {42} tableEntry(MatchAny, 1_"?", Discard*.!Match.40, All, "any")
 , {43} tableEntry(MatchNT.S.46, 1_"?", Reduce.11, Fail, "any")
 , {44} tableEntry(Match, 1_",", S.45, Success*, ", any")
 , {45} tableEntry(MatchNT.S.43, 1_"?", Reduce(12, Match.44), Success*, "any")
 , {46} tableEntry(MatchNT.S.54, 1_"?", S.47, Fail, "any")
 , {47} tableEntry(MatchNT.Match.48, 1_"?", Reduce.13, Fail, "")
 , {48} tableEntry(Match, 1_"∨", S.49, Match.50, "∨ any")
 , {49} tableEntry(MatchNT.S.54, 1_"?", Reduce(14, Match.48), Match.50, "any")
 , {50} tableEntry(Match, 1_"/or", S.51, Match.52, "/or any")
 , {51} tableEntry(MatchNT.S.54, 1_"?", Reduce(15, Match.48), Match.52, "any")
 , {52} tableEntry(Match, 1_"⊻", S.53, Success*, "⊻ any")
 , {53} tableEntry(MatchNT.S.54, 1_"?", Reduce(16, Match.48), Success*, "any")
 , {54} tableEntry(MatchNT.S.60, 1_"?", S.55, Fail, "any")
 , {55} tableEntry(MatchNT.Match.56, 1_"?", Reduce.17, Fail, "")
 , {56} tableEntry(Match, 1_"∧", S.57, Match.58, "∧ any")
 , {57} tableEntry(MatchNT.S.60, 1_"?", Reduce(18, Match.56), Match.58, "any")
 , {58} tableEntry(Match, 1_"/and", S.59, Success*, "/and any")
 , {59} tableEntry(MatchNT.S.60, 1_"?", Reduce(19, Match.56), Success*, "any")
 , {60} tableEntry(MatchNT.S.84, 1_"?", S.61, Fail, "any")
 , {61} tableEntry(MatchNT.Match.62, 1_"?", Reduce.20, Fail, "")
 , {62} tableEntry(Match, 1_"=", S.63, Match.64, "= any")
 , {63} tableEntry(MatchNT.S.84, 1_"?", Reduce(21, Match.62), Match.64, "any")
 , {64} tableEntry(Match, 1_"≠", S.65, Match.66, "≠ any")
 , {65} tableEntry(MatchNT.S.84, 1_"?", Reduce(22, Match.62), Match.66, "any")
 , {66} tableEntry(Match, 1_">", S.67, Match.68, "> any")
 , {67} tableEntry(MatchNT.S.84, 1_"?", Reduce(23, Match.62), Match.68, "any")
 , {68} tableEntry(Match, 1_"<", S.69, Match.70, "< any")
 , {69} tableEntry(MatchNT.S.84, 1_"?", Reduce(24, Match.62), Match.70, "any")
 , {70} tableEntry(Match, 1_">1", S.71, Match.72, ">1 any")
 , {71} tableEntry(MatchNT.S.84, 1_"?", Reduce(25, Match.62), Match.72, "any")
 , {72} tableEntry(Match, 1_">2", S.73, Match.74, ">2 any")
 , {73} tableEntry(MatchNT.S.84, 1_"?", Reduce(26, Match.62), Match.74, "any")
 , {74} tableEntry(Match, 1_"≥", S.75, Match.76, "≥ any")
 , {75} tableEntry(MatchNT.S.84, 1_"?", Reduce(27, Match.62), Match.76, "any")
 , {76} tableEntry(Match, 1_"/ge", S.77, Match.78, "/ge any")
 , {77} tableEntry(MatchNT.S.84, 1_"?", Reduce(28, Match.62), Match.78, "any")
 , {78} tableEntry(Match, 1_"≤", S.79, Match.80, "≤ any")
 , {79} tableEntry(MatchNT.S.84, 1_"?", Reduce(29, Match.62), Match.80, "any")
 , {80} tableEntry(Match, 1_"/le", S.81, Match.82, "/le any")
 , {81} tableEntry(MatchNT.S.84, 1_"?", Reduce(30, Match.62), Match.82, "any")
 , {82} tableEntry(Match, 1_"/ne", S.83, Success*, "/ne any")
 , {83} tableEntry(MatchNT.S.84, 1_"?", Reduce(31, Match.62), Success*, "any")
 , {84} tableEntry(MatchNT.S.98, 1_"?", S.85, Fail, "any")
 , {85} tableEntry(MatchNT.Match.86, 1_"?", Reduce.32, Fail, "")
 , {86} tableEntry(Match, 1_"-", S.87, Match.88, "-any")
 , {87} tableEntry(MatchNT.S.98, 1_"?", Reduce(33, Match.86), Match.88, "any")
 , {88} tableEntry(Match, 1_"+", S.89, Match.90, "+any")
 , {89} tableEntry(MatchNT.S.98, 1_"?", Reduce(34, Match.86), Match.90, "any")
 , {90} tableEntry(Match, 1_"∈", S.91, Match.92, "∈ any")
 , {91} tableEntry(MatchNT.S.98, 1_"?", Reduce(35, Match.86), Match.92, "any")
 , {92} tableEntry(Match, 1_"/in", S.93, Match.94, "/in any")
 , {93} tableEntry(MatchNT.S.98, 1_"?", Reduce(36, Match.86), Match.94, "any")
 , {94} tableEntry(Match, 1_"∉", S.95, Match.96, "∉ any")
 , {95} tableEntry(MatchNT.S.98, 1_"?", Reduce(37, Match.86), Match.96, "any")
 , {96} tableEntry(Match, 1_"/nin", S.97, Success*, "/nin any")
 , {97} tableEntry(MatchNT.S.98, 1_"?", Reduce(38, Match.86), Success*, "any")
 , {98} tableEntry(MatchNT.Match.120, 1_"?", S.99, Fail, "any")
 , {99} tableEntry(MatchNT.Match.100, 1_"?", Reduce.39, Fail, "")
 , {100} tableEntry(Match, 1_"*", S.101, Match.102, "* any")
 , {101} tableEntry(MatchNT.Match.120, 1_"?", Reduce(40, Match.100), Match.102, "any")
 , {102} tableEntry(Match, 1_">>", S.103, Match.104, ">> any")
 , {103} tableEntry(MatchNT.Match.120, 1_"?", Reduce(41, Match.100), Match.104, "any")
 , {104} tableEntry(Match, 1_"<<", S.105, Match.106, "<< any")
 , {105} tableEntry(MatchNT.Match.120, 1_"?", Reduce(42, Match.100), Match.106, "any")
 , {106} tableEntry(Match, slash, S.107, Match.108, "^(slash) any")
 , {107} tableEntry(MatchNT.Match.120, 1_"?", Reduce(43, Match.100), Match.108, "any")
 , {108} tableEntry(Match, 1_"mod", S.109, Match.110, "mod any")
 , {109} tableEntry(MatchNT.Match.120, 1_"?", Reduce(44, Match.100), Match.110, "any")
 , {110} tableEntry(Match, 1_"∩", S.111, Match.112, "∩ any")
 , {111} tableEntry(MatchNT.Match.120, 1_"?", Reduce(45, Match.100), Match.112, "any")
 , {112} tableEntry(Match, 1_"∪", S.113, Match.114, "∪ any")
 , {113} tableEntry(MatchNT.Match.120, 1_"?", Reduce(46, Match.100), Match.114, "any")
 , {114} tableEntry(Match, 1_"/cap", S.115, Match.116, "/cap any")
 , {115} tableEntry(MatchNT.Match.120, 1_"?", Reduce(47, Match.100), Match.116, "any")
 , {116} tableEntry(Match, 1_"/cup", S.117, Match.118, "/cup any")
 , {117} tableEntry(MatchNT.Match.120, 1_"?", Reduce(48, Match.100), Match.118, "any")
 , {118} tableEntry(Match, 1_"\", S.119, Success*, "\ any")
 , {119} tableEntry(MatchNT.Match.120, 1_"?", Reduce(49, Match.100), Success*, "any")
 , {120} tableEntry(Match, 1_"-", S.121, S.122, "-any")
 , {121} tableEntry(MatchNT.Match.120, 1_"?", Reduce.50, S.122, "any")
 , {122} tableEntry(MatchNT.!Match.164, 1_"?", Match.123, Match.125, "any.any")
 , {123} tableEntry(Match, 1_".", S.124, Match.125, ".any")
 , {124} tableEntry(MatchNT.Match.120, 1_"?", Reduce.51, Match.125, "any")
 , {125} tableEntry(Match, 1_"{", S.126, S.129, "{} any")
 , {126} tableEntry(MatchNT.Match.237, 1_"?", Match.127, S.129, "} any")
 , {127} tableEntry(Match, 1_"}", S.128, S.129, "} any")
 , {128} tableEntry(MatchNT.Match.120, 1_"?", Reduce.52, S.129, "any")
 , {129} tableEntry(MatchNT.S.130, 1_"?", Reduce.53, Fail, "any")
 , {130} tableEntry(MatchNT.Match.136, 1_"?", S.131, Fail, "any")
 , {131} tableEntry(MatchNT.Match.132, 1_"?", Reduce.54, Fail, "")
 , {132} tableEntry(Match, 1_"_", S.133, Match.134, "_any")
 , {133} tableEntry(MatchNT.Match.120, 1_"?", Reduce(55, Match.132), Match.134, "any")
 , {134} tableEntry(Match, 1_"^", S.135, Success*, "^(1_"^") any")
 , {135} tableEntry(MatchNT.Match.120, 1_"?", Reduce(56, Match.132), Success*, "any")
 , {136} tableEntry(Match, 1_"(", S.137, Match.139, "(any)")
 , {137} tableEntry(MatchNT.S.43, 1_"?", Match.138, Reduce.63, "any)")
 , {138} tableEntry(Match, 1_")", Reduce.57, Match.139, ")")
 , {139} tableEntry(Match, 1_"[", S.140, S.143, "[any]")
 , {140} tableEntry(MatchNT.S.43, 1_"?", S.141, S.143, "any]")
 , {141} tableEntry(MatchNT.Match.44, 1_"?", Match.142, S.143, "]")
 , {142} tableEntry(Match, 1_"]", Reduce.58, S.143, "]")
 , {143} tableEntry(MatchNT.Match.28, 1_"?", Reduce.59, S.144, "^(1_dq)^(1_dq)")
 , {144} tableEntry(MatchNT.Match.183, 1_"?", S.145, Match.147, "{} any")
 , {145} tableEntry(MatchNT.S.228, 1_"?", S.146, Match.147, "any")
 , {146} tableEntry(MatchNT.S.43, 1_"?", Reduce.60, Match.147, "any")
 , {147} tableEntry(Match, 1_"if", S.148, S.154, "if any then any else any")
 , {148} tableEntry(MatchNT.S.43, 1_"?", Match.149, S.154, "any then any else any")
 , {149} tableEntry(Match, 1_"then", S.150, S.154, "then any else any")
 , {150} tableEntry(MatchNT.S.43, 1_"?", S.151, S.154, "any else any")
 , {151} tableEntry(MatchNT.Match.174, 1_"?", Match.152, S.154, "else any")
 , {152} tableEntry(Match, 1_"else", S.153, S.154, "else any")
 , {153} tableEntry(MatchNT.S.43, 1_"?", Reduce.61, S.154, "any")
 , {154} tableEntry(MatchNT.S.160, 1_"?", Match.155, S.159, "any (any)")
 , {155} tableEntry(Match, 1_"(", S.156, S.159, "(any)")
 , {156} tableEntry(MatchNT.S.43, 1_"?", S.157, S.159, "any)")
 , {157} tableEntry(MatchNT.Match.44, 1_"?", Match.158, S.159, ")")
 , {158} tableEntry(Match, 1_")", Reduce.62, S.159, ")")
 , {159} tableEntry(MatchNT.S.160, 1_"?", Reduce.63, Fail, "any")
 , {160} tableEntry(MatchNT.!Match.164, 1_"?", MatchNext.161, S.163, "any:any")
 , {161} tableEntry(MatchNext, 1_":", S.162, Reduce.65, ":any")
 , {162} tableEntry(MatchNT.S.179, 1_"?", Reduce.64, S.163, "any")
 , {163} tableEntry(MatchNT.!Match.164, 1_"?", Reduce.65, Fail, "any")
 , {164} tableEntry(!Match, 1_",", Fail, !Match.165, ", any")
 , {165} tableEntry(!Match, 1_"[", Fail, !Match.166, "[any")
 , {166} tableEntry(!Match, 1_"(", Fail, !Match.167, "(any")
 , {167} tableEntry(!Match, 1_"]", Fail, !Match.168, "] any")
 , {168} tableEntry(!Match, 1_")", Fail, !Match.169, ") any")
 , {169} tableEntry(!Match, 1_":", Fail, !Match.170, ":any")
 , {170} tableEntry(!Match, 1_".", Fail, !Match.171, ".any")
 , {171} tableEntry(!Match, 1_dq, Fail, MatchAny.172, "^(1_dq) any")
 , {172} tableEntry(MatchAny, 1_"?", Reduce.66, Fail, "any")
 , {173} tableEntry(Match, 1_",", Reduce.67, Reduce.68, ",")
 , {174} tableEntry(Match, 1_"else", Match.175, Success*, "else if any then any")
 , {175} tableEntry(Match, 1_"if", S.176, Success*, "if any then any")
 , {176} tableEntry(MatchNT.S.43, 1_"?", Match.177, Success*, "any then any")
 , {177} tableEntry(Match, 1_"then", S.178, Success*, "then any")
 , {178} tableEntry(MatchNT.S.43, 1_"?", Reduce(69, Match.174), Success*, "any")
 , {179} tableEntry(MatchNT.!Match.164, 1_"?", MatchNext.180, S.182, "any.any")
 , {180} tableEntry(MatchNext, 1_".", S.181, Reduce.71, ".any")
 , {181} tableEntry(MatchNT.S.179, 1_"?", Reduce.70, S.182, "any")
 , {182} tableEntry(MatchNT.!Match.164, 1_"?", Reduce.71, Fail, "any")
 , {183} tableEntry(Match, 1_"let", MatchAny.184, Match.188, "let any = any")
 , {184} tableEntry(MatchAny, 1_"?", MatchNext.185, S.203, "any = any")
 , {185} tableEntry(MatchNext, 1_"=", S.186, Match.204, "= any")
 , {186} tableEntry(MatchNT.S.43, 1_"?", S.187, Match.188, "any")
 , {187} tableEntry(MatchNT.Match.173, 1_"?", Reduce.72, Match.188, "")
 , {188} tableEntry(Match, 1_"assert", S.189, Match.193, "assert any report any")
 , {189} tableEntry(MatchNT.S.43, 1_"?", Match.190, Match.193, "any report any")
 , {190} tableEntry(Match, 1_"report", S.191, Match.193, "report any")
 , {191} tableEntry(MatchNT.S.43, 1_"?", S.192, Match.193, "any")
 , {192} tableEntry(MatchNT.Match.173, 1_"?", Reduce.73, Match.193, "")
 , {193} tableEntry(Match, 1_"{", S.194, Match.197, "{}")
 , {194} tableEntry(MatchNT.Match.237, 1_"?", Match.195, Match.197, "}")
 , {195} tableEntry(Match, 1_"}", S.196, Match.197, "}")
 , {196} tableEntry(MatchNT.Match.173, 1_"?", Reduce.74, Match.197, "")
 , {197} tableEntry(Match, 1_"for", S.198, Match.202, "for any = any do any")
 , {198} tableEntry(MatchNT.S.209, 1_"?", Match.199, Match.202, "any = any do any")
 , {199} tableEntry(Match, 1_"do", S.200, Match.202, "do any")
 , {200} tableEntry(MatchNT.S.43, 1_"?", S.201, Match.202, "any")
 , {201} tableEntry(MatchNT.Match.173, 1_"?", Reduce.75, Match.202, "")
 , {202} tableEntry(Match, 1_"for", S.203, Fail, "for any = any while any do any")
 , {203} tableEntry(MatchNT.S.209, 1_"?", Match.204, Fail, "any = any while any do any")
 , {204} tableEntry(Match, 1_"while", S.205, Fail, "while any do any")
 , {205} tableEntry(MatchNT.S.43, 1_"?", Match.206, Fail, "any do any")
 , {206} tableEntry(Match, 1_"do", S.207, Fail, "do any")
 , {207} tableEntry(MatchNT.S.43, 1_"?", S.208, Fail, "any")
 , {208} tableEntry(MatchNT.Match.173, 1_"?", Reduce.76, Fail, "")
 , {209} tableEntry(MatchNT.S.220, 1_"?", MatchNext.210, S.214, "any = any, any ∈ any")
 , {210} tableEntry(MatchNext, 1_",", MatchAny.211, Match.215, ", any ∈ any")
 , {211} tableEntry(MatchAny, 1_"?", MatchNext.212, MatchAny.216, "any ∈ any")
 , {212} tableEntry(MatchNext, 1_"∈", S.213, Match.217, "∈ any")
 , {213} tableEntry(MatchNT.S.43, 1_"?", Reduce.77, S.214, "any")
 , {214} tableEntry(MatchNT.S.220, 1_"?", Match.215, S.219, "any = any, any /in any")
 , {215} tableEntry(Match, 1_",", MatchAny.216, S.219, ", any /in any")
 , {216} tableEntry(MatchAny, 1_"?", Match.217, S.219, "any /in any")
 , {217} tableEntry(Match, 1_"/in", S.218, S.219, "/in any")
 , {218} tableEntry(MatchNT.S.43, 1_"?", Reduce.78, S.219, "any")
 , {219} tableEntry(MatchNT.S.220, 1_"?", Reduce.79, Fail, "any = any")
 , {220} tableEntry(MatchNT.!Match.224, 1_"?", S.221, Fail, "any = any")
 , {221} tableEntry(MatchNT.Match.222, 1_"?", Reduce.80, Fail, "")
 , {222} tableEntry(Match, 1_",", S.223, Success*, ", any = any")
 , {223} tableEntry(MatchNT.!Match.224, 1_"?", Reduce(81, Match.222), Success*, "any = any")
 , {224} tableEntry(!Match, 1_"while", Fail, MatchAny.225, "while any = any")
 , {225} tableEntry(MatchAny, 1_"?", Match.226, Fail, "any = any")
 , {226} tableEntry(Match, 1_"=", S.227, Fail, "= any")
 , {227} tableEntry(MatchNT.S.43, 1_"?", Reduce.82, Fail, "any")
 , {228} tableEntry(MatchNT.Match.183, 1_"?", Reduce(83, S.228), Success*, "{}")
 , {229} tableEntry(MatchNT.MatchAny.233, 1_"?", S.230, Fail, "any")
 , {230} tableEntry(MatchNT.Match.231, 1_"?", Reduce.84, Fail, "")
 , {231} tableEntry(Match, 1_",", S.232, Success*, ", any")
 , {232} tableEntry(MatchNT.MatchAny.233, 1_"?", Reduce(85, Match.231), Success*, "any")
 , {233} tableEntry(MatchAny, 1_"?", Match.234, S.236, "any:any")
 , {234} tableEntry(Match, 1_":", S.235, S.236, ":any")
 , {235} tableEntry(MatchNT.S.179, 1_"?", Reduce.86, S.236, "any")
 , {236} tableEntry(MatchNT.S.179, 1_"?", Reduce.87, Fail, "any")
 , {237} tableEntry(Match, 1_"{", S.238, S.240, "{}")
 , {238} tableEntry(MatchNT.Match.237, 1_"?", Match.239, S.240, "}")
 , {239} tableEntry(Match, 1_"}", Reduce(88, Match.237), S.240, "}")
 , {240} tableEntry(MatchNT.!Match.241, 1_"?", Reduce(89, Match.237), Success*, "")
 , {241} tableEntry(!Match, 1_"{", All, !Match.242, "{any")
 , {242} tableEntry(!Match, 1_"}", All, MatchAny.243, "} any")
 , {243} tableEntry(MatchAny, 1_"?", Discard*.!Match.241, All, "any")
]

function =(seq.word, bindinfo) boolean true

function =(seq.word, word) boolean true

use standard

use seq.tableEntry

use otherseq.frame

use stack.frame

use otherseq.bindinfo

use PEGrules

function _(i:int, R:reduction) bindinfo (i + 1)_toseq.R

function recovery(parsestk:stack.frame) seq.word
for acc = "", frame ∈ toseq.parsestk
do
 if action.Sstate.frame ∈ [Match, S] then
 acc + recover.(index.Sstate.frame)_mytable
 else acc,
acc

type reduction is toseq:seq.bindinfo

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.bindinfo
, faili:int
, failresult:seq.bindinfo

type runresult is stk:stack.frame

Function status(a:runresult) word
if Sstate.top.stk.a ≠ Reduce.1 then
1_"Failed"
else if i.top.stk.a = {length of input} faili.top.stk.a then
1_"Match"
else 1_"MatchPrefix"

Function result(a:runresult) bindinfo 1^result.top.stk.a

function parse(
 myinput0:seq.word
 , table:seq.tableEntry
 , initAttr:bindinfo
 , common:commonType
) runresult
let myinput = packed(myinput0 + endMark)
let packedTable = packed.table
for
 maxi = 0
 , maxStk = empty:stack.frame
 , stk = empty:stack.frame
 , state = startstate
 , i = 1
 , inputi = 1_myinput
 , result = [initAttr]
 , faili = 1
 , failresult = [initAttr]
while not(state = Reduce.1 ∨ state = Reduce.0)
do
 let actionState = action.state,
  if actionState = Fail then
   {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
   let top = top.stk
   let newstk = pop.stk,
   next(
    maxi
    , maxStk
    , newstk
    , if is!.Sstate.top then Sstate.top else Fstate.top
    , faili.top
    , idxNB(myinput, faili.top)
    , failresult.top
    , faili.top
    , failresult.top
   )
  else if actionState = Success* then
   {goto Sstate.top.stk, pop.stk, keep result}
   let top = top.stk,
   next(maxi, maxStk, pop.stk, Sstate.top, i, inputi, result.top + result, faili.top, failresult.top)
  else if actionState = SuccessDiscard* then
   {goto Sstate.top.stk, pop.stk, keep result}
   let top = top.stk,
   next(maxi, maxStk, pop.stk, Sstate.top, i, inputi, result.top, faili.top, failresult.top)
  else if actionState = Discard* then
   let top = top.stk,
    if faili = i then
    next(maxi, maxStk, pop.stk, Sstate.top, i, inputi, result.top, faili.top, failresult.top)
    else
     let newmaxStk = if i ≥ maxi then stk else maxStk,
     next(max(maxi, i), newmaxStk, stk, nextState.state, i, inputi, result.top, i, result.top)
  else if actionState = All then
   let top = top.stk
   let att = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
   next(maxi, maxStk, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
  else if actionState = Reduce then
   {Reduce}
   if nextState.state ≠ S.0 then
    let att = [action(reduceNo.state, reduction.result, i, myinput, common, stk)]
    let top = top.stk
    let newmaxStk = if i ≥ maxi then stk else maxStk,
     if faili = i then
     next(maxi, maxStk, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
     else next(max(i, maxi), newmaxStk, stk, nextState.state, i, inputi, att, i, att)
   else
    let top = top.stk,
     if is!.Sstate.top then
      {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
      let newstk = pop.stk
      let newi = faili.top
      let ini = idxNB(myinput, newi),
      next(maxi, maxStk, newstk, Fstate.top, newi, ini, failresult.top, faili.top, failresult.top)
     else
      let att = [action(reduceNo.state, reduction.result, i, myinput, common, stk)],
       if i ≥ maxi then
       next(i, stk, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
       else next(maxi, maxStk, pop.stk, Sstate.top, i, inputi, result.top + att, faili.top, failresult.top)
  else if actionState = Match then
   let te = idxNB(packedTable, index.state),
    if inputi ≠ match.te then
     {fail}
     next(maxi, maxStk, stk, Fstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
    else next(maxi, maxStk, stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
  else if actionState = !Match then
   let te = idxNB(packedTable, index.state),
    if inputi = match.te then
     {fail}
     next(maxi, maxStk, stk, Sstate.te, faili, idxNB(myinput, faili), failresult, faili, failresult)
    else next(maxi, maxStk, stk, Fstate.te, i, inputi, result, faili, failresult)
  else if actionState = MatchAny then
   let te = idxNB(packedTable, index.state),
    if inputi = endMark then
    {fail} next(maxi, maxStk, stk, Fstate.te, i, inputi, result, faili, failresult)
    else
     let reslt =
      if action.Sstate.te = Discard* then
      result
      else result + toAttribute(1^result, [inputi])
     let ini = idxNB(myinput, i + 1),
     next(maxi, maxStk, stk, Sstate.te, i + 1, ini, reslt, faili, failresult)
  else if actionState = MatchNext then
   let te = idxNB(packedTable, index.state),
    if inputi = match.te then
    next(maxi, maxStk, stk, Sstate.te, i + 1, idxNB(myinput, i + 1), result, faili, failresult)
    else next(maxi, maxStk, stk, Fstate.te, i, inputi, result, faili, failresult)
  else
   {match non Terminal}
   let te = idxNB(packedTable, index.state)
   assert action.action.te = MatchNT report "PROBLEM PEG^(state)"
   let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult))
   let tmp = [toAttribute(1^result, empty:seq.word)],
   next(maxi, maxStk, newstk, nextState.action.te, i, inputi, tmp, i, tmp),
runresult.push(maxStk, frame(state, state, maxi, result, n.myinput, result)) 