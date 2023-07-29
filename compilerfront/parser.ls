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
let r = parse(input, mytable, b, commonType(types, outText, input))
assert not(success.r ∧ i.top.stk.r ≠ n.input + 1)
report
 let place = i.top.stk.r
 let m = "<* literal syntax error *>",
 "^(m)
  /br^(prettyNoChange.subseq(input, 1, place - 1))
  /br^(m)
  /br part of unprocessed input: ^(subseq(input, place, place + 10))"
assert success.r report errormessage("syntax error", input,-i.top.stk.r, pop.stk.r),
code.result.r

function toAttribute(b:bindinfo, w:seq.word) bindinfo
bindinfo(dict.b, empty:seq.symbol, empty:seq.mytype, w)

Function errormessage(
 message:seq.word
 , input:seq.word
 , place:int
 , parsestk:stack.frame
) seq.word
let m = "<* literal^(if place < 0 then "syntax error" else message) *>"
let ending = recovery(Sstate.top.parsestk, pop.parsestk, recoverTable)
let pp = prettyNoChange(subseq(input, 1, abs.place - 1) + ending)
let debug =
 if false then
  for txt = "/br", f ∈ toseq.parsestk do txt + %.Sstate.f,
   txt
   + "/br"
   + showZ(subseq(input, 1, abs.place - 1) + ending)
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
let t = m + debug + "/br" + subseq(pp, 1, idx)
let unprocessed = subseq(input, abs.place, abs.place + 10),
(if not.isempty.t ∧ 1^t ∈ "/keyword" then t >> 1 + addback else t + addback)
 + "/br^(m)
 /br"
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
     else ifthenelse(arg1code, [Littrue], arg2code, typeboolean)
    ,
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
     else [lookupbysig(static, dict, [1_op], types, place, parsestk)]
    ,
    next(arg1code + arg2code + f, [resulttype.1_f], start + len, ops << 2)
 ,
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
  code.exp + cvt
,
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
 ,
  [Start.1_types.thenpart]
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
 "cannot find 1^(if n.name = 1 then name else [1_name, 1_":"] + name << 1)"
 + "(^(for acc = "", @e ∈ paratypes do acc + %.@e + ",", acc >> 1))"
 , input.static
 , place
 , parsestk
)
assert n.f = 1
report errormessage(
 "found more than one^(for acc = "", @e ∈ toseq.f do acc + library.module.@e + "." + %.@e, acc)"
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
  0
 ,
 0
,
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
  + symbol(builtinmod.rt, "createthreadZ", typeptr, processtype)
 ,
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
     report errormessage("illformed real literal", input.static, place, parsestk)
     ,
     place_input.static
   ,
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
{we declare accumulators after all initial values are calculated since initial values may change size of symboldict. }
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
  ,
   [Start.typeint]
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
   ,
    accumTypes
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
      + [lastidx, totallength, EqOp]
    ,
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
       + Define.value.totallength
,
bindinfo(restorenext.dict.vars, newcode, [typeint], "")

function mergeText(static:commonType, a:seq.symbol, b:seq.symbol) seq.symbol
if outText.static ∧ not.isempty.a ∧ not.isempty.b then
a + b + symbol(internalmod, "$mergecode", typeint, typeint, typeint)
else a + b

function slash word 1_"/"

function /All word 1_"All"

function PEGgen(
 seqElementType:word
 , attributeType:bindinfo
 , runresultType:runresult
 , R:reduction
 , place:int
 , parsestk:stack.frame
 , error:boolean
 , common:commonType
) seq.boolean
[
 "match2code carrot" = 1_"^"
 , "/ slash" = slash
 , "/ dq" = 1_dq
 , "/ any" = 1_"/1"
 ,
  "S function Name (FPL) Type Declare' E"
  = checktype(common, 3_R, 4_R, 5_R, place, parsestk)
 , "/ function Name Type Declare' E" = checktype(common, 2_R, 3_R, 4_R, place, parsestk)
 ,
  "/ Function Name (FPL) Type Declare' E"
  = checktype(common, 3_R, 4_R, 5_R, place, parsestk)
 , "/ Function Name Type Declare' E" = checktype(common, 2_R, 3_R, 4_R, place, parsestk)
 , "String dq String' str2 dq" = strExp(common, 1_R, 2_R, "", true, place, parsestk)
 , "* String' str2 carrot (E)" = strExp(common, 0_R, 1_R, 2_R, place, parsestk)
 , "/ str2 carrot" = strExp(common, 0_R, 1_R, "^", false, place, parsestk)
 , "/ str2" = strExp(common, 0_R, 1_R, "", false, place, parsestk)
 , "* str2 ! dq ! carrot any" = /All
 , "E Or" = 1_R
 , "EL E EL'" = bindinfo(dict.1_R, code.1_R + code.2_R, types.1_R + types.2_R, "")
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
 ,
  "/ {N} Unary"
  = 
   if outText.common then
   bindinfo(
    dict.2_R
    ,
     [Words.text.1_R]
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
 , "/ [EL]" = seq(common, 1_R, place, parsestk)
 , "/ String" = 1_R
 ,
  "/ Declare Declare' E"
  = bindinfo(
   dict.0_R
   , mergeText(common, mergeText(common, code.1_R, code.2_R), code.3_R)
   , types.3_R
   , ""
  )
 , "/ if E then E IF else E" = ifExp(common, 1_R, 2_R, 3_R, 4_R, place, parsestk)
 , "/ Name (EL)" = unaryop(common, dict.1_R, place, parsestk, text.1_R, 2_R)
 , "/ Name" = bindlit2(common, 1_R, place, parsestk)
 ,
  "Name Id:Type"
  = bindinfo(dict.1_R, empty:seq.symbol, empty:seq.mytype, text.1_R + text.2_R)
 , "/ Id" = 1_R
 , "Id !, !] !) !:!.! dq any" = 1_R
 , "comma?," = 0_R
 , "/" = 0_R
 , "* IF else if E then E" = ifExp(common, 0_R, 1_R, 2_R, place, parsestk)
 ,
  "Type Id.Type"
  = bindinfo(dict.2_R, empty:seq.symbol, empty:seq.mytype, text.1_R + "." + text.2_R)
 , "/ Id" = 1_R
 , "Declare let any = E comma?" = letExp(common, 1_R, 2_R, place, parsestk)
 , "/ assert E report E comma?" = assertExp(common, 1_R, 2_R, place, parsestk)
 ,
  "/ {N} comma?"
  = 
   if outText.common then
   bindinfo(
    dict.0_R
    , code.0_R + Words.text.1_R + symbol(internalmod, "{", seqof.typeword, typeint)
    , empty:seq.mytype
    , ""
   )
   else 0_R
 ,
  "/ for ForDeclare do E comma?"
  = forbody(common, 1_R, bindinfo(dict.0_R, [Littrue], [typeboolean], ""), 2_R, place, parsestk)
 , "/ for ForDeclare while E do E comma?" = forbody(common, 1_R, 2_R, 3_R, place, parsestk)
 ,
  "ForDeclare AccumList, any ∈ E"
  = forSeqExp(common, 1_R, text.2_R, 3_R, place, parsestk)
 , "/ AccumList, any /in E" = forSeqExp(common, 1_R, text.2_R, 3_R, place, parsestk)
 , "/ AccumList" = forSeqExp(common, 1_R, ".", 1_R, place, parsestk)
 ,
  "AccumList Accum AccumList'"
  = bindinfo(dict.0_R, code.1_R + code.2_R, types.1_R + types.2_R, text.1_R + text.2_R)
 ,
  "* AccumList', Accum"
  = bindinfo(dict.0_R, code.0_R + code.1_R, types.0_R + types.1_R, text.0_R + text.1_R)
 , "Accum ! while any = E" = bindinfo(dict.0_R, code.2_R, types.2_R, text.1_R)
 ,
  "* Declare' Declare"
  = bindinfo(dict.1_R, mergeText(common, code.0_R, code.1_R), empty:seq.mytype, "")
 ,
  "FPL FP FPL'"
  = declarePara(dict.1_R, text.1_R + text.2_R, types.1_R + types.2_R)
 ,
  "* FPL', FP"
  = bindinfo(dict.0_R, empty:seq.symbol, types.0_R + types.1_R, text.0_R + text.1_R)
 , "FP any:Type" = addpara(common, text.1_R, 2_R, place, parsestk)
 , "/ Type" = addpara(common, 0_R, ":", 1_R, place, parsestk)
 , "C {N}" = toAttribute(1_R, "{^(text.1_R)}")
 ,
  "* N C"
  = bindinfo(dict.0_R, empty:seq.symbol, empty:seq.mytype, text.0_R + text.1_R)
 ,
  "/ str1"
  = bindinfo(dict.0_R, empty:seq.symbol, empty:seq.mytype, text.0_R + text.1_R)
 ,
  "* str1 ! {!} any"
  = bindinfo(dict.0_R, empty:seq.symbol, empty:seq.mytype, text.0_R + text.1_R)
]

<<<< Below is auto generated code >>>>

/br Non-termials:Accum AccumList AccumList' And And' Atom C Compare Compare' Declare Declare' E EL
EL' FP FPL FPL' ForDeclare IF Id N Name Or Or' Power Power' Product Product' S String String' Sum Sum'
Type Unary comma? str1 str2
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
/br EL ← E EL'
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
/br Atom ← (E) / [EL] / String
/br / Declare Declare' E
/br / if E then E IF else E
/br / Name (EL)
/br / Name
/br Name ← Id:Type / Id
/br Id ← !, !] !) !:!.! dq any
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
/br C ← {N}
/br * N ← C / str1
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
bindinfo(dict.1_R, code.1_R + code.2_R, types.1_R + types.2_R, "")
else if partno = 13 then
bindinfo(dict.0_R, code.0_R + code.1_R, types.0_R + types.1_R, "")
else if partno = 14 then
binaryops(common, 1_R, 2_R, place, parsestk)
else if partno = 15 then
binary(0_R, "∨", 1_R)
else if partno = 16 then
binary(0_R, "∨", 1_R)
else if partno = 17 then
binary(0_R, "⊻", 1_R)
else if partno = 18 then
binaryops(common, 1_R, 2_R, place, parsestk)
else if partno = 19 then
binary(0_R, "∧", 1_R)
else if partno = 20 then
binary(0_R, "∧", 1_R)
else if partno = 21 then
binaryops(common, 1_R, 2_R, place, parsestk)
else if partno = 22 then
binary(0_R, "=", 1_R)
else if partno = 23 then
binary(0_R, "≠", 1_R)
else if partno = 24 then
binary(0_R, ">", 1_R)
else if partno = 25 then
binary(0_R, "<", 1_R)
else if partno = 26 then
binary(0_R, ">1", 1_R)
else if partno = 27 then
binary(0_R, ">2", 1_R)
else if partno = 28 then
binary(0_R, "≥", 1_R)
else if partno = 29 then
binary(0_R, "≥", 1_R)
else if partno = 30 then
binary(0_R, "≤", 1_R)
else if partno = 31 then
binary(0_R, "≤", 1_R)
else if partno = 32 then
binary(0_R, "≠", 1_R)
else if partno = 33 then
binaryops(common, 1_R, 2_R, place, parsestk)
else if partno = 34 then
binary(0_R, "-", 1_R)
else if partno = 35 then
binary(0_R, "+", 1_R)
else if partno = 36 then
binary(0_R, "∈", 1_R)
else if partno = 37 then
binary(0_R, "∈", 1_R)
else if partno = 38 then
binary(0_R, "∉", 1_R)
else if partno = 39 then
binary(0_R, "∉", 1_R)
else if partno = 40 then
binaryops(common, 1_R, 2_R, place, parsestk)
else if partno = 41 then
binary(0_R, "*", 1_R)
else if partno = 42 then
binary(0_R, ">>", 1_R)
else if partno = 43 then
binary(0_R, "<<", 1_R)
else if partno = 44 then
binary(0_R, [slash], 1_R)
else if partno = 45 then
binary(0_R, "mod", 1_R)
else if partno = 46 then
binary(0_R, "∩", 1_R)
else if partno = 47 then
binary(0_R, "∪", 1_R)
else if partno = 48 then
binary(0_R, "∩", 1_R)
else if partno = 49 then
binary(0_R, "∪", 1_R)
else if partno = 50 then
binary(0_R, "\", 1_R)
else if partno = 51 then
unaryop(common, dict.1_R, place, parsestk, "-", 1_R)
else if partno = 52 then
unaryop(common, dict.1_R, place - 1, parsestk, text.1_R, 2_R)
else if partno = 53 then
 if outText.common then
 bindinfo(
  dict.2_R
  ,
   [Words.text.1_R]
   + code.2_R
   + symbol(internalmod, "{", seqof.typeword, 1_types.2_R, 1_types.2_R)
  , types.2_R
  , ""
 )
 else 2_R
else if partno = 54 then
1_R
else if partno = 55 then
binaryops(common, 1_R, 2_R, place, parsestk)
else if partno = 56 then
binary(0_R, "_", 1_R)
else if partno = 57 then
binary(0_R, "^", 1_R)
else if partno = 58 then
1_R
else if partno = 59 then
seq(common, 1_R, place, parsestk)
else if partno = 60 then
1_R
else if partno = 61 then
bindinfo(
 dict.0_R
 , mergeText(common, mergeText(common, code.1_R, code.2_R), code.3_R)
 , types.3_R
 , ""
)
else if partno = 62 then
ifExp(common, 1_R, 2_R, 3_R, 4_R, place, parsestk)
else if partno = 63 then
unaryop(common, dict.1_R, place, parsestk, text.1_R, 2_R)
else if partno = 64 then
bindlit2(common, 1_R, place, parsestk)
else if partno = 65 then
bindinfo(dict.1_R, empty:seq.symbol, empty:seq.mytype, text.1_R + text.2_R)
else if partno = 66 then
1_R
else if partno = 67 then
1_R
else if partno = 68 then
0_R
else if partno = 69 then
0_R
else if partno = 70 then
ifExp(common, 0_R, 1_R, 2_R, place, parsestk)
else if partno = 71 then
bindinfo(dict.2_R, empty:seq.symbol, empty:seq.mytype, text.1_R + "." + text.2_R)
else if partno = 72 then
1_R
else if partno = 73 then
letExp(common, 1_R, 2_R, place, parsestk)
else if partno = 74 then
assertExp(common, 1_R, 2_R, place, parsestk)
else if partno = 75 then
 if outText.common then
 bindinfo(
  dict.0_R
  , code.0_R + Words.text.1_R + symbol(internalmod, "{", seqof.typeword, typeint)
  , empty:seq.mytype
  , ""
 )
 else 0_R
else if partno = 76 then
forbody(common, 1_R, bindinfo(dict.0_R, [Littrue], [typeboolean], ""), 2_R, place, parsestk)
else if partno = 77 then
forbody(common, 1_R, 2_R, 3_R, place, parsestk)
else if partno = 78 then
forSeqExp(common, 1_R, text.2_R, 3_R, place, parsestk)
else if partno = 79 then
forSeqExp(common, 1_R, text.2_R, 3_R, place, parsestk)
else if partno = 80 then
forSeqExp(common, 1_R, ".", 1_R, place, parsestk)
else if partno = 81 then
bindinfo(dict.0_R, code.1_R + code.2_R, types.1_R + types.2_R, text.1_R + text.2_R)
else if partno = 82 then
bindinfo(dict.0_R, code.0_R + code.1_R, types.0_R + types.1_R, text.0_R + text.1_R)
else if partno = 83 then
bindinfo(dict.0_R, code.2_R, types.2_R, text.1_R)
else if partno = 84 then
bindinfo(dict.1_R, mergeText(common, code.0_R, code.1_R), empty:seq.mytype, "")
else if partno = 85 then
declarePara(dict.1_R, text.1_R + text.2_R, types.1_R + types.2_R)
else if partno = 86 then
bindinfo(dict.0_R, empty:seq.symbol, types.0_R + types.1_R, text.0_R + text.1_R)
else if partno = 87 then
addpara(common, text.1_R, 2_R, place, parsestk)
else if partno = 88 then
addpara(common, 0_R, ":", 1_R, place, parsestk)
else if partno = 89 then
toAttribute(1_R, "{^(text.1_R)}")
else if partno = 90 then
bindinfo(dict.0_R, empty:seq.symbol, empty:seq.mytype, text.0_R + text.1_R)
else if partno = 91 then
bindinfo(dict.0_R, empty:seq.symbol, empty:seq.mytype, text.0_R + text.1_R)
else if partno = 92 then
bindinfo(dict.0_R, empty:seq.symbol, empty:seq.mytype, text.0_R + text.1_R)
else 0_R

function mytable seq.tblEle
[
 tblEle(S.2, 1_"S", Reduce.1, Fail)
 , tblEle(Match, 1_"function", S.3, S.10)
 , tblEle(S.198, 1_"Name", S.4, P.11)
 , tblEle(MatchNext, 1_"(", S.5, S.12)
 , tblEle(S.269, 1_"FPL", S.6, S.10)
 , tblEle(Match, 1_")", S.7, S.10)
 , tblEle(S.217, 1_"Type", S.8, S.10)
 , tblEle(S.267, 1_"Declare'", S.9, S.10)
 , tblEle(S.46, 1_"E", Reduce.2, S.10)
 , tblEle(Match, 1_"function", S.11, S.15)
 , tblEle(S.198, 1_"Name", S.12, S.15)
 , tblEle(S.217, 1_"Type", S.13, S.15)
 , tblEle(S.267, 1_"Declare'", S.14, S.15)
 , tblEle(S.46, 1_"E", Reduce.3, S.15)
 , tblEle(Match, 1_"Function", S.16, S.23)
 , tblEle(S.198, 1_"Name", S.17, P.24)
 , tblEle(MatchNext, 1_"(", S.18, S.25)
 , tblEle(S.269, 1_"FPL", S.19, S.23)
 , tblEle(Match, 1_")", S.20, S.23)
 , tblEle(S.217, 1_"Type", S.21, S.23)
 , tblEle(S.267, 1_"Declare'", S.22, S.23)
 , tblEle(S.46, 1_"E", Reduce.4, S.23)
 , tblEle(Match, 1_"Function", S.24, Fail)
 , tblEle(S.198, 1_"Name", S.25, Fail)
 , tblEle(S.217, 1_"Type", S.26, Fail)
 , tblEle(S.267, 1_"Declare'", S.27, Fail)
 , tblEle(S.46, 1_"E", Reduce.5, Fail)
 , tblEle(Match, 1_dq, S.29, Fail)
 , tblEle(S.32, 1_"String'", S.30, Fail)
 , tblEle(S.43, 1_"str2", S.31, Fail)
 , tblEle(Match, 1_dq, Reduce.6, Fail)
 , tblEle(S.43, 1_"str2", S.33, S.38)
 , tblEle(MatchNext, 1_"^", S.34, S.39)
 , tblEle(MatchNext, 1_"(", S.35, S.40)
 , tblEle(S.46, 1_"E", S.36, S.38)
 , tblEle(Match, 1_")", S.37, S.38)
 , tblEle(Reduce.7, 1_"?", S.32, S.0)
 , tblEle(S.43, 1_"str2", S.39, S.41)
 , tblEle(MatchNext, 1_"^", S.40, S.42)
 , tblEle(Reduce.8, 1_"?", S.32, S.0)
 , tblEle(S.43, 1_"str2", S.42, Success*)
 , tblEle(Reduce.9, 1_"?", S.32, S.0)
 , tblEle(!Match, 1_dq, S.44, All)
 , tblEle(!Match, 1_"^", S.45, All)
 , tblEle(MatchAny, 1_"any", Discard*.43, All)
 , tblEle(S.52, 1_"Or", Reduce.11, Fail)
 , tblEle(S.46, 1_"E", S.48, Fail)
 , tblEle(S.49, 1_"EL'", Reduce.12, Fail)
 , tblEle(Match, 1_",", S.50, Success*)
 , tblEle(S.46, 1_"E", S.51, Success*)
 , tblEle(Reduce.13, 1_"?", S.49, S.0)
 , tblEle(S.63, 1_"And", S.53, Fail)
 , tblEle(S.54, 1_"Or'", Reduce.14, Fail)
 , tblEle(Match, 1_"∨", S.55, S.57)
 , tblEle(S.63, 1_"And", S.56, S.57)
 , tblEle(Reduce.15, 1_"?", S.54, S.0)
 , tblEle(Match, 1_"/or", S.58, S.60)
 , tblEle(S.63, 1_"And", S.59, S.60)
 , tblEle(Reduce.16, 1_"?", S.54, S.0)
 , tblEle(Match, 1_"⊻", S.61, Success*)
 , tblEle(S.63, 1_"And", S.62, Success*)
 , tblEle(Reduce.17, 1_"?", S.54, S.0)
 , tblEle(S.71, 1_"Compare", S.64, Fail)
 , tblEle(S.65, 1_"And'", Reduce.18, Fail)
 , tblEle(Match, 1_"∧", S.66, S.68)
 , tblEle(S.71, 1_"Compare", S.67, S.68)
 , tblEle(Reduce.19, 1_"?", S.65, S.0)
 , tblEle(Match, 1_"/and", S.69, Success*)
 , tblEle(S.71, 1_"Compare", S.70, Success*)
 , tblEle(Reduce.20, 1_"?", S.65, S.0)
 , tblEle(S.106, 1_"Sum", S.72, Fail)
 , tblEle(S.73, 1_"Compare'", Reduce.21, Fail)
 , tblEle(Match, 1_"=", S.74, S.76)
 , tblEle(S.106, 1_"Sum", S.75, S.76)
 , tblEle(Reduce.22, 1_"?", S.73, S.0)
 , tblEle(Match, 1_"≠", S.77, S.79)
 , tblEle(S.106, 1_"Sum", S.78, S.79)
 , tblEle(Reduce.23, 1_"?", S.73, S.0)
 , tblEle(Match, 1_">", S.80, S.82)
 , tblEle(S.106, 1_"Sum", S.81, S.82)
 , tblEle(Reduce.24, 1_"?", S.73, S.0)
 , tblEle(Match, 1_"<", S.83, S.85)
 , tblEle(S.106, 1_"Sum", S.84, S.85)
 , tblEle(Reduce.25, 1_"?", S.73, S.0)
 , tblEle(Match, 1_">1", S.86, S.88)
 , tblEle(S.106, 1_"Sum", S.87, S.88)
 , tblEle(Reduce.26, 1_"?", S.73, S.0)
 , tblEle(Match, 1_">2", S.89, S.91)
 , tblEle(S.106, 1_"Sum", S.90, S.91)
 , tblEle(Reduce.27, 1_"?", S.73, S.0)
 , tblEle(Match, 1_"≥", S.92, S.94)
 , tblEle(S.106, 1_"Sum", S.93, S.94)
 , tblEle(Reduce.28, 1_"?", S.73, S.0)
 , tblEle(Match, 1_"/ge", S.95, S.97)
 , tblEle(S.106, 1_"Sum", S.96, S.97)
 , tblEle(Reduce.29, 1_"?", S.73, S.0)
 , tblEle(Match, 1_"≤", S.98, S.100)
 , tblEle(S.106, 1_"Sum", S.99, S.100)
 , tblEle(Reduce.30, 1_"?", S.73, S.0)
 , tblEle(Match, 1_"/le", S.101, S.103)
 , tblEle(S.106, 1_"Sum", S.102, S.103)
 , tblEle(Reduce.31, 1_"?", S.73, S.0)
 , tblEle(Match, 1_"/ne", S.104, Success*)
 , tblEle(S.106, 1_"Sum", S.105, Success*)
 , tblEle(Reduce.32, 1_"?", S.73, S.0)
 , tblEle(S.126, 1_"Product", S.107, Fail)
 , tblEle(S.108, 1_"Sum'", Reduce.33, Fail)
 , tblEle(Match, 1_"-", S.109, S.111)
 , tblEle(S.126, 1_"Product", S.110, S.111)
 , tblEle(Reduce.34, 1_"?", S.108, S.0)
 , tblEle(Match, 1_"+", S.112, S.114)
 , tblEle(S.126, 1_"Product", S.113, S.114)
 , tblEle(Reduce.35, 1_"?", S.108, S.0)
 , tblEle(Match, 1_"∈", S.115, S.117)
 , tblEle(S.126, 1_"Product", S.116, S.117)
 , tblEle(Reduce.36, 1_"?", S.108, S.0)
 , tblEle(Match, 1_"/in", S.118, S.120)
 , tblEle(S.126, 1_"Product", S.119, S.120)
 , tblEle(Reduce.37, 1_"?", S.108, S.0)
 , tblEle(Match, 1_"∉", S.121, S.123)
 , tblEle(S.126, 1_"Product", S.122, S.123)
 , tblEle(Reduce.38, 1_"?", S.108, S.0)
 , tblEle(Match, 1_"/nin", S.124, Success*)
 , tblEle(S.126, 1_"Product", S.125, Success*)
 , tblEle(Reduce.39, 1_"?", S.108, S.0)
 , tblEle(S.158, 1_"Unary", S.127, Fail)
 , tblEle(S.128, 1_"Product'", Reduce.40, Fail)
 , tblEle(Match, 1_"*", S.129, S.131)
 , tblEle(S.158, 1_"Unary", S.130, S.131)
 , tblEle(Reduce.41, 1_"?", S.128, S.0)
 , tblEle(Match, 1_">>", S.132, S.134)
 , tblEle(S.158, 1_"Unary", S.133, S.134)
 , tblEle(Reduce.42, 1_"?", S.128, S.0)
 , tblEle(Match, 1_"<<", S.135, S.137)
 , tblEle(S.158, 1_"Unary", S.136, S.137)
 , tblEle(Reduce.43, 1_"?", S.128, S.0)
 , tblEle(Match, slash, S.138, S.140)
 , tblEle(S.158, 1_"Unary", S.139, S.140)
 , tblEle(Reduce.44, 1_"?", S.128, S.0)
 , tblEle(Match, 1_"mod", S.141, S.143)
 , tblEle(S.158, 1_"Unary", S.142, S.143)
 , tblEle(Reduce.45, 1_"?", S.128, S.0)
 , tblEle(Match, 1_"∩", S.144, S.146)
 , tblEle(S.158, 1_"Unary", S.145, S.146)
 , tblEle(Reduce.46, 1_"?", S.128, S.0)
 , tblEle(Match, 1_"∪", S.147, S.149)
 , tblEle(S.158, 1_"Unary", S.148, S.149)
 , tblEle(Reduce.47, 1_"?", S.128, S.0)
 , tblEle(Match, 1_"/cap", S.150, S.152)
 , tblEle(S.158, 1_"Unary", S.151, S.152)
 , tblEle(Reduce.48, 1_"?", S.128, S.0)
 , tblEle(Match, 1_"/cup", S.153, S.155)
 , tblEle(S.158, 1_"Unary", S.154, S.155)
 , tblEle(Reduce.49, 1_"?", S.128, S.0)
 , tblEle(Match, 1_"\", S.156, Success*)
 , tblEle(S.158, 1_"Unary", S.157, Success*)
 , tblEle(Reduce.50, 1_"?", S.128, S.0)
 , tblEle(Match, 1_"-", S.159, S.160)
 , tblEle(S.158, 1_"Unary", Reduce.51, S.160)
 , tblEle(S.202, 1_"Id", S.161, S.163)
 , tblEle(Match, 1_".", S.162, S.163)
 , tblEle(S.158, 1_"Unary", Reduce.52, S.163)
 , tblEle(Match, 1_"{", S.164, S.167)
 , tblEle(S.281, 1_"N", S.165, S.167)
 , tblEle(Match, 1_"}", S.166, S.167)
 , tblEle(S.158, 1_"Unary", Reduce.53, S.167)
 , tblEle(S.168, 1_"Power", Reduce.54, Fail)
 , tblEle(S.176, 1_"Atom", S.169, Fail)
 , tblEle(S.170, 1_"Power'", Reduce.55, Fail)
 , tblEle(Match, 1_"_", S.171, S.173)
 , tblEle(S.158, 1_"Unary", S.172, S.173)
 , tblEle(Reduce.56, 1_"?", S.170, S.0)
 , tblEle(Match, 1_"^", S.174, Success*)
 , tblEle(S.158, 1_"Unary", S.175, Success*)
 , tblEle(Reduce.57, 1_"?", S.170, S.0)
 , tblEle(Match, 1_"(", S.177, S.179)
 , tblEle(S.46, 1_"E", S.178, S.179)
 , tblEle(Match, 1_")", Reduce.58, S.179)
 , tblEle(Match, 1_"[", S.180, S.182)
 , tblEle(S.47, 1_"EL", S.181, S.182)
 , tblEle(Match, 1_"]", Reduce.59, S.182)
 , tblEle(S.28, 1_"String", Reduce.60, S.183)
 , tblEle(S.221, 1_"Declare", S.184, S.186)
 , tblEle(S.267, 1_"Declare'", S.185, S.186)
 , tblEle(S.46, 1_"E", Reduce.61, S.186)
 , tblEle(Match, 1_"if", S.187, S.193)
 , tblEle(S.46, 1_"E", S.188, S.193)
 , tblEle(Match, 1_"then", S.189, S.193)
 , tblEle(S.46, 1_"E", S.190, S.193)
 , tblEle(S.211, 1_"IF", S.191, S.193)
 , tblEle(Match, 1_"else", S.192, S.193)
 , tblEle(S.46, 1_"E", Reduce.62, S.193)
 , tblEle(S.198, 1_"Name", S.194, S.197)
 , tblEle(MatchNext, 1_"(", S.195, Reduce.64)
 , tblEle(S.47, 1_"EL", S.196, S.197)
 , tblEle(Match, 1_")", Reduce.63, S.197)
 , tblEle(S.198, 1_"Name", Reduce.64, Fail)
 , tblEle(S.202, 1_"Id", S.199, S.201)
 , tblEle(MatchNext, 1_":", S.200, Reduce.66)
 , tblEle(S.217, 1_"Type", Reduce.65, S.201)
 , tblEle(S.202, 1_"Id", Reduce.66, Fail)
 , tblEle(!Match, 1_",", S.203, Fail)
 , tblEle(!Match, 1_"]", S.204, Fail)
 , tblEle(!Match, 1_")", S.205, Fail)
 , tblEle(!Match, 1_":", S.206, Fail)
 , tblEle(!Match, 1_".", S.207, Fail)
 , tblEle(!Match, 1_dq, S.208, Fail)
 , tblEle(MatchAny, 1_"any", Reduce.67, Fail)
 , tblEle(Match, 1_",", Reduce.68, S.210)
 , tblEle(Reduce.69, 1_"?", S.0, S.0)
 , tblEle(Match, 1_"else", S.212, Success*)
 , tblEle(Match, 1_"if", S.213, Success*)
 , tblEle(S.46, 1_"E", S.214, Success*)
 , tblEle(Match, 1_"then", S.215, Success*)
 , tblEle(S.46, 1_"E", S.216, Success*)
 , tblEle(Reduce.70, 1_"?", S.211, S.0)
 , tblEle(S.202, 1_"Id", S.218, S.220)
 , tblEle(MatchNext, 1_".", S.219, Reduce.72)
 , tblEle(S.217, 1_"Type", Reduce.71, S.220)
 , tblEle(S.202, 1_"Id", Reduce.72, Fail)
 , tblEle(Match, 1_"let", S.222, S.226)
 , tblEle(MatchAny, 1_"any", S.223, S.226)
 , tblEle(Match, 1_"=", S.224, S.226)
 , tblEle(S.46, 1_"E", S.225, S.226)
 , tblEle(S.209, 1_"comma?", Reduce.73, S.226)
 , tblEle(Match, 1_"assert", S.227, S.231)
 , tblEle(S.46, 1_"E", S.228, S.231)
 , tblEle(Match, 1_"report", S.229, S.231)
 , tblEle(S.46, 1_"E", S.230, S.231)
 , tblEle(S.209, 1_"comma?", Reduce.74, S.231)
 , tblEle(Match, 1_"{", S.232, S.235)
 , tblEle(S.281, 1_"N", S.233, S.235)
 , tblEle(Match, 1_"}", S.234, S.235)
 , tblEle(S.209, 1_"comma?", Reduce.75, S.235)
 , tblEle(Match, 1_"for", S.236, S.240)
 , tblEle(S.247, 1_"ForDeclare", S.237, P.241)
 , tblEle(MatchNext, 1_"do", S.238, S.242)
 , tblEle(S.46, 1_"E", S.239, S.240)
 , tblEle(S.209, 1_"comma?", Reduce.76, S.240)
 , tblEle(Match, 1_"for", S.241, Fail)
 , tblEle(S.247, 1_"ForDeclare", S.242, Fail)
 , tblEle(Match, 1_"while", S.243, Fail)
 , tblEle(S.46, 1_"E", S.244, Fail)
 , tblEle(Match, 1_"do", S.245, Fail)
 , tblEle(S.46, 1_"E", S.246, Fail)
 , tblEle(S.209, 1_"comma?", Reduce.77, Fail)
 , tblEle(S.258, 1_"AccumList", S.248, S.252)
 , tblEle(MatchNext, 1_",", S.249, S.253)
 , tblEle(MatchAny, 1_"any", S.250, S.252)
 , tblEle(MatchNext, 1_"∈", S.251, S.255)
 , tblEle(S.46, 1_"E", Reduce.78, S.252)
 , tblEle(S.258, 1_"AccumList", S.253, S.257)
 , tblEle(MatchNext, 1_",", S.254, Reduce.80)
 , tblEle(MatchAny, 1_"any", S.255, S.257)
 , tblEle(Match, 1_"/in", S.256, S.257)
 , tblEle(S.46, 1_"E", Reduce.79, S.257)
 , tblEle(S.258, 1_"AccumList", Reduce.80, Fail)
 , tblEle(S.263, 1_"Accum", S.259, Fail)
 , tblEle(S.260, 1_"AccumList'", Reduce.81, Fail)
 , tblEle(Match, 1_",", S.261, Success*)
 , tblEle(S.263, 1_"Accum", S.262, Success*)
 , tblEle(Reduce.82, 1_"?", S.260, S.0)
 , tblEle(!Match, 1_"while", S.264, Fail)
 , tblEle(MatchAny, 1_"any", S.265, Fail)
 , tblEle(Match, 1_"=", S.266, Fail)
 , tblEle(S.46, 1_"E", Reduce.83, Fail)
 , tblEle(S.221, 1_"Declare", S.268, Success*)
 , tblEle(Reduce.84, 1_"?", S.267, S.0)
 , tblEle(S.274, 1_"FP", S.270, Fail)
 , tblEle(S.271, 1_"FPL'", Reduce.85, Fail)
 , tblEle(Match, 1_",", S.272, Success*)
 , tblEle(S.274, 1_"FP", S.273, Success*)
 , tblEle(Reduce.86, 1_"?", S.271, S.0)
 , tblEle(MatchAny, 1_"any", S.275, S.277)
 , tblEle(Match, 1_":", S.276, S.277)
 , tblEle(S.217, 1_"Type", Reduce.87, S.277)
 , tblEle(S.217, 1_"Type", Reduce.88, Fail)
 , tblEle(Match, 1_"{", S.279, Fail)
 , tblEle(S.281, 1_"N", S.280, Fail)
 , tblEle(Match, 1_"}", Reduce.89, Fail)
 , tblEle(S.278, 1_"C", S.282, S.283)
 , tblEle(Reduce.90, 1_"?", S.281, S.0)
 , tblEle(S.285, 1_"str1", S.284, Success*)
 , tblEle(Reduce.91, 1_"?", S.281, S.0)
 , tblEle(!Match, 1_"{", S.286, Success*)
 , tblEle(!Match, 1_"}", S.287, Success*)
 , tblEle(MatchAny, 1_"any", S.288, Success*)
 , tblEle(Reduce.92, 1_"?", S.285, S.0)
]

function recoverTable seq.recoveryEntry
[
 recoveryEntry(Match, [1_"Function", 1_"any", 1_"any", 1_"any"], Reduce.1)
 , recoveryEntry(Match, [1_"function"], S.3)
 , recoveryEntry(Match, [1_"any"], S.4)
 , recoveryEntry(Match, [1_"("], S.5)
 , recoveryEntry(Match, [1_"any"], S.6)
 , recoveryEntry(Match, [1_")"], S.7)
 , recoveryEntry(Match, [1_"any"], S.8)
 , recoveryEntry(Match, "", S.9)
 , recoveryEntry(Match, [1_"any"], Reduce.2)
 , recoveryEntry(Match, [1_"function"], S.11)
 , recoveryEntry(Match, [1_"any"], S.12)
 , recoveryEntry(Match, [1_"any"], S.13)
 , recoveryEntry(Match, "", S.14)
 , recoveryEntry(Match, [1_"any"], Reduce.3)
 , recoveryEntry(Match, [1_"Function"], S.16)
 , recoveryEntry(Match, [1_"any"], S.17)
 , recoveryEntry(Match, [1_"("], S.18)
 , recoveryEntry(Match, [1_"any"], S.19)
 , recoveryEntry(Match, [1_")"], S.20)
 , recoveryEntry(Match, [1_"any"], S.21)
 , recoveryEntry(Match, "", S.22)
 , recoveryEntry(Match, [1_"any"], Reduce.4)
 , recoveryEntry(Match, [1_"Function"], S.24)
 , recoveryEntry(Match, [1_"any"], S.25)
 , recoveryEntry(Match, [1_"any"], S.26)
 , recoveryEntry(Match, "", S.27)
 , recoveryEntry(Match, [1_"any"], Reduce.5)
 , recoveryEntry(Match, [1_dq], S.29)
 , recoveryEntry(Match, "", S.30)
 , recoveryEntry(Match, "", S.31)
 , recoveryEntry(Match, [1_dq], Reduce.6)
 , recoveryEntry(Match, "", S.33)
 , recoveryEntry(Match, [1_"^"], S.34)
 , recoveryEntry(Match, [1_"("], S.35)
 , recoveryEntry(Match, [1_"any"], S.36)
 , recoveryEntry(Match, [1_")"], S.37)
 , recoveryEntry(Reduce.7, "", S.32)
 , recoveryEntry(Match, "", S.39)
 , recoveryEntry(Match, [1_"^"], S.40)
 , recoveryEntry(Reduce.8, "", S.32)
 , recoveryEntry(Match, "", S.42)
 , recoveryEntry(Reduce.9, "", S.32)
 , recoveryEntry(!Match, "", S.44)
 , recoveryEntry(!Match, "", S.45)
 , recoveryEntry(Match, [1_"any"], Discard*.43)
 , recoveryEntry(Match, [1_"any"], Reduce.11)
 , recoveryEntry(Match, [1_"any"], S.48)
 , recoveryEntry(Match, "", Reduce.12)
 , recoveryEntry(Match, [1_","], S.50)
 , recoveryEntry(Match, [1_"any"], S.51)
 , recoveryEntry(Reduce.13, "", S.49)
 , recoveryEntry(Match, [1_"any"], S.53)
 , recoveryEntry(Match, "", Reduce.14)
 , recoveryEntry(Match, [1_"∨"], S.55)
 , recoveryEntry(Match, [1_"any"], S.56)
 , recoveryEntry(Reduce.15, "", S.54)
 , recoveryEntry(Match, [1_"/or"], S.58)
 , recoveryEntry(Match, [1_"any"], S.59)
 , recoveryEntry(Reduce.16, "", S.54)
 , recoveryEntry(Match, [1_"⊻"], S.61)
 , recoveryEntry(Match, [1_"any"], S.62)
 , recoveryEntry(Reduce.17, "", S.54)
 , recoveryEntry(Match, [1_"any"], S.64)
 , recoveryEntry(Match, "", Reduce.18)
 , recoveryEntry(Match, [1_"∧"], S.66)
 , recoveryEntry(Match, [1_"any"], S.67)
 , recoveryEntry(Reduce.19, "", S.65)
 , recoveryEntry(Match, [1_"/and"], S.69)
 , recoveryEntry(Match, [1_"any"], S.70)
 , recoveryEntry(Reduce.20, "", S.65)
 , recoveryEntry(Match, [1_"any"], S.72)
 , recoveryEntry(Match, "", Reduce.21)
 , recoveryEntry(Match, [1_"="], S.74)
 , recoveryEntry(Match, [1_"any"], S.75)
 , recoveryEntry(Reduce.22, "", S.73)
 , recoveryEntry(Match, [1_"≠"], S.77)
 , recoveryEntry(Match, [1_"any"], S.78)
 , recoveryEntry(Reduce.23, "", S.73)
 , recoveryEntry(Match, [1_">"], S.80)
 , recoveryEntry(Match, [1_"any"], S.81)
 , recoveryEntry(Reduce.24, "", S.73)
 , recoveryEntry(Match, [1_"<"], S.83)
 , recoveryEntry(Match, [1_"any"], S.84)
 , recoveryEntry(Reduce.25, "", S.73)
 , recoveryEntry(Match, [1_">1"], S.86)
 , recoveryEntry(Match, [1_"any"], S.87)
 , recoveryEntry(Reduce.26, "", S.73)
 , recoveryEntry(Match, [1_">2"], S.89)
 , recoveryEntry(Match, [1_"any"], S.90)
 , recoveryEntry(Reduce.27, "", S.73)
 , recoveryEntry(Match, [1_"≥"], S.92)
 , recoveryEntry(Match, [1_"any"], S.93)
 , recoveryEntry(Reduce.28, "", S.73)
 , recoveryEntry(Match, [1_"/ge"], S.95)
 , recoveryEntry(Match, [1_"any"], S.96)
 , recoveryEntry(Reduce.29, "", S.73)
 , recoveryEntry(Match, [1_"≤"], S.98)
 , recoveryEntry(Match, [1_"any"], S.99)
 , recoveryEntry(Reduce.30, "", S.73)
 , recoveryEntry(Match, [1_"/le"], S.101)
 , recoveryEntry(Match, [1_"any"], S.102)
 , recoveryEntry(Reduce.31, "", S.73)
 , recoveryEntry(Match, [1_"/ne"], S.104)
 , recoveryEntry(Match, [1_"any"], S.105)
 , recoveryEntry(Reduce.32, "", S.73)
 , recoveryEntry(Match, [1_"any"], S.107)
 , recoveryEntry(Match, "", Reduce.33)
 , recoveryEntry(Match, [1_"-"], S.109)
 , recoveryEntry(Match, [1_"any"], S.110)
 , recoveryEntry(Reduce.34, "", S.108)
 , recoveryEntry(Match, [1_"+"], S.112)
 , recoveryEntry(Match, [1_"any"], S.113)
 , recoveryEntry(Reduce.35, "", S.108)
 , recoveryEntry(Match, [1_"∈"], S.115)
 , recoveryEntry(Match, [1_"any"], S.116)
 , recoveryEntry(Reduce.36, "", S.108)
 , recoveryEntry(Match, [1_"/in"], S.118)
 , recoveryEntry(Match, [1_"any"], S.119)
 , recoveryEntry(Reduce.37, "", S.108)
 , recoveryEntry(Match, [1_"∉"], S.121)
 , recoveryEntry(Match, [1_"any"], S.122)
 , recoveryEntry(Reduce.38, "", S.108)
 , recoveryEntry(Match, [1_"/nin"], S.124)
 , recoveryEntry(Match, [1_"any"], S.125)
 , recoveryEntry(Reduce.39, "", S.108)
 , recoveryEntry(Match, [1_"any"], S.127)
 , recoveryEntry(Match, "", Reduce.40)
 , recoveryEntry(Match, [1_"*"], S.129)
 , recoveryEntry(Match, [1_"any"], S.130)
 , recoveryEntry(Reduce.41, "", S.128)
 , recoveryEntry(Match, [1_">>"], S.132)
 , recoveryEntry(Match, [1_"any"], S.133)
 , recoveryEntry(Reduce.42, "", S.128)
 , recoveryEntry(Match, [1_"<<"], S.135)
 , recoveryEntry(Match, [1_"any"], S.136)
 , recoveryEntry(Reduce.43, "", S.128)
 , recoveryEntry(Match, [slash], S.138)
 , recoveryEntry(Match, [1_"any"], S.139)
 , recoveryEntry(Reduce.44, "", S.128)
 , recoveryEntry(Match, [1_"mod"], S.141)
 , recoveryEntry(Match, [1_"any"], S.142)
 , recoveryEntry(Reduce.45, "", S.128)
 , recoveryEntry(Match, [1_"∩"], S.144)
 , recoveryEntry(Match, [1_"any"], S.145)
 , recoveryEntry(Reduce.46, "", S.128)
 , recoveryEntry(Match, [1_"∪"], S.147)
 , recoveryEntry(Match, [1_"any"], S.148)
 , recoveryEntry(Reduce.47, "", S.128)
 , recoveryEntry(Match, [1_"/cap"], S.150)
 , recoveryEntry(Match, [1_"any"], S.151)
 , recoveryEntry(Reduce.48, "", S.128)
 , recoveryEntry(Match, [1_"/cup"], S.153)
 , recoveryEntry(Match, [1_"any"], S.154)
 , recoveryEntry(Reduce.49, "", S.128)
 , recoveryEntry(Match, [1_"\"], S.156)
 , recoveryEntry(Match, [1_"any"], S.157)
 , recoveryEntry(Reduce.50, "", S.128)
 , recoveryEntry(Match, [1_"-"], S.159)
 , recoveryEntry(Match, [1_"any"], Reduce.51)
 , recoveryEntry(Match, [1_"any"], S.161)
 , recoveryEntry(Match, [1_"."], S.162)
 , recoveryEntry(Match, [1_"any"], Reduce.52)
 , recoveryEntry(Match, [1_"{"], S.164)
 , recoveryEntry(Match, "", S.165)
 , recoveryEntry(Match, [1_"}"], S.166)
 , recoveryEntry(Match, [1_"any"], Reduce.53)
 , recoveryEntry(Match, [1_"any"], Reduce.54)
 , recoveryEntry(Match, [1_"any"], S.169)
 , recoveryEntry(Match, "", Reduce.55)
 , recoveryEntry(Match, [1_"_"], S.171)
 , recoveryEntry(Match, [1_"any"], S.172)
 , recoveryEntry(Reduce.56, "", S.170)
 , recoveryEntry(Match, [1_"^"], S.174)
 , recoveryEntry(Match, [1_"any"], S.175)
 , recoveryEntry(Reduce.57, "", S.170)
 , recoveryEntry(Match, [1_"("], S.177)
 , recoveryEntry(Match, [1_"any"], S.178)
 , recoveryEntry(Match, [1_")"], Reduce.58)
 , recoveryEntry(Match, [1_"["], S.180)
 , recoveryEntry(Match, [1_"any"], S.181)
 , recoveryEntry(Match, [1_"]"], Reduce.59)
 , recoveryEntry(Match, [1_dq, 1_dq], Reduce.60)
 , recoveryEntry(Match, [1_"{", 1_"}"], S.184)
 , recoveryEntry(Match, "", S.185)
 , recoveryEntry(Match, [1_"any"], Reduce.61)
 , recoveryEntry(Match, [1_"if"], S.187)
 , recoveryEntry(Match, [1_"any"], S.188)
 , recoveryEntry(Match, [1_"then"], S.189)
 , recoveryEntry(Match, [1_"any"], S.190)
 , recoveryEntry(Match, "", S.191)
 , recoveryEntry(Match, [1_"else"], S.192)
 , recoveryEntry(Match, [1_"any"], Reduce.62)
 , recoveryEntry(Match, [1_"any"], S.194)
 , recoveryEntry(Match, [1_"("], S.195)
 , recoveryEntry(Match, [1_"any"], S.196)
 , recoveryEntry(Match, [1_")"], Reduce.63)
 , recoveryEntry(Match, [1_"any"], Reduce.64)
 , recoveryEntry(Match, [1_"any"], S.199)
 , recoveryEntry(Match, [1_":"], S.200)
 , recoveryEntry(Match, [1_"any"], Reduce.65)
 , recoveryEntry(Match, [1_"any"], Reduce.66)
 , recoveryEntry(!Match, "", S.203)
 , recoveryEntry(!Match, "", S.204)
 , recoveryEntry(!Match, "", S.205)
 , recoveryEntry(!Match, "", S.206)
 , recoveryEntry(!Match, "", S.207)
 , recoveryEntry(!Match, "", S.208)
 , recoveryEntry(Match, [1_"any"], Reduce.67)
 , recoveryEntry(Match, [1_","], Reduce.68)
 , recoveryEntry(Reduce.69, "", S.0)
 , recoveryEntry(Match, [1_"else"], S.212)
 , recoveryEntry(Match, [1_"if"], S.213)
 , recoveryEntry(Match, [1_"any"], S.214)
 , recoveryEntry(Match, [1_"then"], S.215)
 , recoveryEntry(Match, [1_"any"], S.216)
 , recoveryEntry(Reduce.70, "", S.211)
 , recoveryEntry(Match, [1_"any"], S.218)
 , recoveryEntry(Match, [1_"."], S.219)
 , recoveryEntry(Match, [1_"any"], Reduce.71)
 , recoveryEntry(Match, [1_"any"], Reduce.72)
 , recoveryEntry(Match, [1_"let"], S.222)
 , recoveryEntry(Match, [1_"any"], S.223)
 , recoveryEntry(Match, [1_"="], S.224)
 , recoveryEntry(Match, [1_"any"], S.225)
 , recoveryEntry(Match, "", Reduce.73)
 , recoveryEntry(Match, [1_"assert"], S.227)
 , recoveryEntry(Match, [1_"any"], S.228)
 , recoveryEntry(Match, [1_"report"], S.229)
 , recoveryEntry(Match, [1_"any"], S.230)
 , recoveryEntry(Match, "", Reduce.74)
 , recoveryEntry(Match, [1_"{"], S.232)
 , recoveryEntry(Match, "", S.233)
 , recoveryEntry(Match, [1_"}"], S.234)
 , recoveryEntry(Match, "", Reduce.75)
 , recoveryEntry(Match, [1_"for"], S.236)
 , recoveryEntry(Match, [1_"any", 1_"=", 1_"any"], S.237)
 , recoveryEntry(Match, [1_"do"], S.238)
 , recoveryEntry(Match, [1_"any"], S.239)
 , recoveryEntry(Match, "", Reduce.76)
 , recoveryEntry(Match, [1_"for"], S.241)
 , recoveryEntry(Match, [1_"any", 1_"=", 1_"any"], S.242)
 , recoveryEntry(Match, [1_"while"], S.243)
 , recoveryEntry(Match, [1_"any"], S.244)
 , recoveryEntry(Match, [1_"do"], S.245)
 , recoveryEntry(Match, [1_"any"], S.246)
 , recoveryEntry(Match, "", Reduce.77)
 , recoveryEntry(Match, [1_"any", 1_"=", 1_"any"], S.248)
 , recoveryEntry(Match, [1_","], S.249)
 , recoveryEntry(Match, [1_"any"], S.250)
 , recoveryEntry(Match, [1_"∈"], S.251)
 , recoveryEntry(Match, [1_"any"], Reduce.78)
 , recoveryEntry(Match, [1_"any", 1_"=", 1_"any"], S.253)
 , recoveryEntry(Match, [1_","], S.254)
 , recoveryEntry(Match, [1_"any"], S.255)
 , recoveryEntry(Match, [1_"/in"], S.256)
 , recoveryEntry(Match, [1_"any"], Reduce.79)
 , recoveryEntry(Match, [1_"any", 1_"=", 1_"any"], Reduce.80)
 , recoveryEntry(Match, [1_"any", 1_"=", 1_"any"], S.259)
 , recoveryEntry(Match, "", Reduce.81)
 , recoveryEntry(Match, [1_","], S.261)
 , recoveryEntry(Match, [1_"any", 1_"=", 1_"any"], S.262)
 , recoveryEntry(Reduce.82, "", S.260)
 , recoveryEntry(!Match, "", S.264)
 , recoveryEntry(Match, [1_"any"], S.265)
 , recoveryEntry(Match, [1_"="], S.266)
 , recoveryEntry(Match, [1_"any"], Reduce.83)
 , recoveryEntry(Match, [1_"{", 1_"}"], S.268)
 , recoveryEntry(Reduce.84, "", S.267)
 , recoveryEntry(Match, [1_"any"], S.270)
 , recoveryEntry(Match, "", Reduce.85)
 , recoveryEntry(Match, [1_","], S.272)
 , recoveryEntry(Match, [1_"any"], S.273)
 , recoveryEntry(Reduce.86, "", S.271)
 , recoveryEntry(Match, [1_"any"], S.275)
 , recoveryEntry(Match, [1_":"], S.276)
 , recoveryEntry(Match, [1_"any"], Reduce.87)
 , recoveryEntry(Match, [1_"any"], Reduce.88)
 , recoveryEntry(Match, [1_"{"], S.279)
 , recoveryEntry(Match, "", S.280)
 , recoveryEntry(Match, [1_"}"], Reduce.89)
 , recoveryEntry(Match, [1_"{", 1_"}"], S.282)
 , recoveryEntry(Reduce.90, "", S.281)
 , recoveryEntry(Match, "", S.284)
 , recoveryEntry(Reduce.91, "", S.281)
 , recoveryEntry(!Match, "", S.286)
 , recoveryEntry(!Match, "", S.287)
 , recoveryEntry(Match, [1_"any"], S.288)
 , recoveryEntry(Reduce.92, "", S.285)
]

use seq.recoveryEntry

function recovery(state:state, stk:stack.frame, table:seq.recoveryEntry) seq.word
if isempty.stk then
""
else if action.state = S.0 then
 let te = (index.state)_table,
  if action.te = Match ∨ action.te = MatchNext ∨ action.te = MatchAny then
  match.te + recovery(Sstate.te, stk, table)
  else
   assert action.action.te = actionReduce report "Not handled 1^(action.te),",
   recovery(Sstate.top.stk, pop.stk, table)
else if action.state = actionReduce then
recovery(Sstate.top.stk, pop.stk, table)
else "Not handled 2^(state)"

function =(seq.word, bindinfo) boolean true

function =(seq.word, word) boolean true

use standard

use seq.tblEle

use otherseq.frame

use stack.frame

use otherseq.bindinfo

use PEGrules

function _(i:int, R:reduction) bindinfo (i + 1)_toseq.R

type tblEle is action:state, match:word, Sstate:state, Fstate:state

type reduction is toseq:seq.bindinfo

type frame is
Sstate:state
, Fstate:state
, i:int
, result:seq.bindinfo
, faili:int
, failresult:seq.bindinfo

type runresult is stk:stack.frame

Function success(a:runresult) boolean Sstate.top.stk.a ≠ Fail

Function result(a:runresult) bindinfo 1^result.top.stk.a

function parse(
 myinput:seq.word
 , table:seq.tblEle
 , initAttr:bindinfo
 , common:commonType
) runresult
let packedTable = packed.table
for
 reduceLen = 0
 , maxStack = empty:stack.frame
 , stk = empty:stack.frame
 , state = startstate
 , i = 1
 , result = [initAttr]
 , faili = 1
 , failresult = [initAttr]
while not(
 index.state = 1 ∧ action.state = actionReduce
 ∨ action.state = Fail ∧ n.toseq.stk < 2
)
do
 let actionState = action.state,
  if actionState = Fail ∨ actionState = actionReduce ∧ not.isempty.stk ∧ is!.Sstate.top.stk then
   {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
   let top = top.stk
   let newstk = pop.stk,
    if action.Fstate.top = actionP then
    next(reduceLen, maxStack, newstk, S.index.Fstate.top, i.top, result.top, faili.top, failresult.top)
    else next(
     reduceLen
     , maxStack
     , newstk
     , if is!.Sstate.top ∧ state = Fail then Sstate.top else Fstate.top
     , faili.top
     , failresult.top
     , faili.top
     , failresult.top
    )
  else if actionState = Success* then
   {goto Sstate.top.stk, pop.stk, keep result}
   let top = top.stk,
   next(reduceLen, maxStack, pop.stk, Sstate.top, i, result.top + result, faili.top, failresult.top)
  else if actionState = actionDiscard* then
  next(reduceLen, maxStack, stk, S.index.state, i, result, i, result)
  else if actionState = All then
   let top = top.stk
   let reduction = [toAttribute(1^result, subseq(myinput, i.top, i - 1))],
   next(reduceLen, maxStack, pop.stk, Sstate.top, i, result.top + reduction, faili.top, failresult.top)
  else if actionState = actionReduce then
   {actionReduce}
   let top = top.stk,
    if i ≥ reduceLen then
     let reduction = [action(index.state, reduction.result, i, myinput, common, stk)],
     next(
      {reduceLen} i
      , {maxStack} stk
      , pop.stk
      , Sstate.top
      , i
      , result.top + reduction
      , faili.top
      , failresult.top
     )
    else
     let reduction = [action(index.state, reduction.result,-reduceLen, myinput, common, maxStack)],
     next(reduceLen, maxStack, pop.stk, Sstate.top, i, result.top + reduction, faili.top, failresult.top)
  else
   let iz = index.state
   let te = idxNB(packedTable, iz)
   let actionTe = action.action.te,
    if actionTe = S.0 then
     {match non Terminal}
     let newstk = push(stk, frame(Sstate.te, Fstate.te, i, result, faili, failresult))
     let tmp = [toAttribute(1^result, empty:seq.word)],
     next(reduceLen, maxStack, newstk, action.te, i, tmp, i, tmp)
    else if actionTe = actionReduce then
     let reduction = [action(index.action.te, reduction.result, i, myinput, common, stk)]
     let top = top.stk
     let newreducelen = if i ≥ reduceLen then i else reduceLen
     let newMaxStack = if i ≥ reduceLen then stk else maxStack,
      if faili = i then
      next(
       newreducelen
       , newMaxStack
       , pop.stk
       , Sstate.top
       , i
       , result.top + reduction
       , faili.top
       , failresult.top
      )
      else next(newreducelen, newMaxStack, stk, Sstate.te, i, reduction, i, reduction)
    else if actionTe = Match then
     if i > n.myinput ∨ i_myinput ≠ match.te then
     {fail} next(reduceLen, maxStack, stk, Fstate.te, faili, failresult, faili, failresult)
     else next(reduceLen, maxStack, stk, Sstate.te, i + 1, result, faili, failresult)
    else if actionTe = MatchNext then
     if i > n.myinput ∨ i_myinput ≠ match.te then
     {fail} next(reduceLen, maxStack, stk, Fstate.te, i, result, faili, failresult)
     else next(reduceLen, maxStack, stk, Sstate.te, i + 1, result, faili, failresult)
    else if actionTe = !Match then
     if i ≤ n.myinput ∧ i_myinput = match.te then
     {fail} next(reduceLen, maxStack, stk, Fstate.te, faili, failresult, faili, failresult)
     else next(reduceLen, maxStack, stk, Sstate.te, i, result, faili, failresult)
    else
     assert actionTe = MatchAny report "PROBLEM PEG",
      if i > n.myinput then
      {fail} next(reduceLen, maxStack, stk, Fstate.te, i, result, faili, failresult)
      else
       let newresult =
        if action.Sstate.te = actionDiscard* then
        result
        else result + toAttribute(1^result, [i_myinput])
       ,
       next(reduceLen, maxStack, stk, Sstate.te, i + 1, newresult, faili, failresult)
,
runresult.push(maxStack, frame(state, state, reduceLen, result, i, result)) 