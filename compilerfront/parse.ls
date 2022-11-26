Module parse

use UTF8

use parsersupport.bindinfo

use stack.stkele.bindinfo

use seq.char

use mytype

use seq.mytype

use standard

use symbol

use otherseq.symbol

use set.symbol

use symboldict

Export type:bindinfo {From symboldict}

function fixNM(t:seq.word) seq.word
if length.t = 1 then t else [t_1, ":"_1] + t << 1

function forward(stk:bindinfo, token:bindinfo) bindinfo
bindinfo(dict.stk, empty:seq.symbol, empty:seq.mytype, tokentext.token)

function attribute:bindinfo(w:seq.word) bindinfo
bindinfo(empty:symboldict, empty:seq.symbol, empty:seq.mytype, w)

Function text(b:bindinfo) seq.word tokentext.b

function dict(r:reduction.bindinfo) symboldict dict.last.r

Function bindinfo(dict:symboldict, types:seq.mytype, tokentext:seq.word) bindinfo
bindinfo(dict, empty:seq.symbol, types, tokentext)

function resolvetype(text:seq.word, common:commoninfo, place:int, parsestk:stack.stkele.bindinfo) mytype
let a = resolvetype(types.common, text)
assert not.isempty.a report errormessage("cannot resolve type $(text)", common, place, parsestk)
a_1

Function parse(dict:symboldict, headeronly:boolean) bindinfo
let a = sortedlextable:bindinfo
parse:bindinfo(bindinfo(dict, empty:seq.mytype, ""), a, input.common.dict, headeronly)

function addbody(R:reduction.bindinfo, common:commoninfo, place:int, parsestk:stack.stkele.bindinfo) bindinfo
let exp = R_2
let returntype = last.types.R_1
assert mode.common ∈ "symbol" ∨ returntype = (types.exp)_1
report
 errormessage("function type of $(returntype) does not match expression type $((types.exp)_1)"
  , common
  , place
  , parsestk)
let codewithcomments = 
 code.R_1 + code.exp
 + constantseq(length.code.R_1, symbol(internalmod, "{", seqof.typeword, returntype, returntype))
bindinfo(dict.R, codewithcomments, types.R_1, text.R_1)

function createfunc(R:reduction.bindinfo
 , common:commoninfo
 , place:int
 , parsestk:stack.stkele.bindinfo
 , funcname:seq.word
 , PL:bindinfo
 , functypebind:bindinfo) bindinfo
let paralist = if mode.common ∈ "symbol" then types.PL else empty:seq.mytype
let returntype = resolvetype(text.functypebind, common, place, parsestk)
let newdict = 
 if mode.common ∈ "symbol" then
  dict.R
 else
  addparameters(PL, common, place, parsestk)
if length.funcname > 1 then
 bindinfo(newdict
  , empty:seq.symbol
  , [resolvetype(funcname << 1, common, place, parsestk)] + paralist + returntype
  , funcname)
else
 bindinfo(newdict, empty:seq.symbol, paralist + returntype, funcname)

function errormessage(message:seq.word, common:commoninfo, place:int, parsestk:stack.stkele.bindinfo) seq.word
errormessage:bindinfo(message, input.common, place, parsestk)

function addparameters(b:bindinfo, common:commoninfo, place:int, parsestk:stack.stkele.bindinfo) symboldict
for flds = dict.b, idx = 1, paratype ∈ types.b do
 assert isempty.lookupbysig(flds, [(text.b)_idx]) ∨ (text.b)_idx = ":"_1
 report errormessage("duplciate symbol:" + (text.b)_idx, common, place, parsestk)
 next(flds + Local((text.b)_idx, paratype, idx), idx + 1)
/for (flds)

function lookupbysig(dict:symboldict
 , name:seq.word
 , paratypes:seq.mytype
 , common:commoninfo
 , place:int
 , parsestk:stack.stkele.bindinfo) symbol
let sym3 = 
 if length.name = 1 then
  symbol(internalmod, name, paratypes, typeint)
 else
  symbol4(internalmod
   , name_1
   , resolvetype(name << 1, common, place, parsestk)
   , paratypes
   , typeint)
let f0 = lookupbysig(dict, sym3)
let f = 
 if cardinality.f0 < 2 then
  f0
 else
  for acc = empty:set.symbol, sy ∈ toseq.f0 do
   if isunbound.sy then acc else acc + sy
  /for (acc)
assert not.isempty.f
report
 errormessage(
  "cannot find 1 $(fixNM.name) ($(for acc = "", @e ∈ paratypes do acc + %.@e + "
   ," /for (acc >> 1)))"
  , common
  , place
  , parsestk)
assert cardinality.f = 1
report
 errormessage(
  "found more than one $(for acc = "", @e ∈ toseq.f do acc + library.module.@e + "
   ." + %.@e /for (acc))"
  , common
  , place
  , parsestk)
let discard = 
 for acc = 0, sym2 ∈ requires(dict, f_1) do
  let xxx = lookupbysig(dict, sym2)
  assert not.isempty.xxx ∨ isAbstract.module.f_1
  report errormessage("using symbol $(f_1) requires unbound $(sym2)", common, place, parsestk)
  0
 /for (0)
f_1

function bindlit(R:reduction.bindinfo) bindinfo
let chars = decodeword.first.text.R_1
let rt = 
 if length.chars > 1 ∧ chars_2 ∈ decodeword.first."Xx" then typebits else typeint
bindinfo(dict.R
 , [
  if mode.common.dict.R = "text"_1 then
   symbol(internalmod, text.R_1, rt)
  else
   Lit.cvttoint.chars
  ]
 , [rt]
 , "")

function opaction(R:reduction.bindinfo, input:commoninfo, place:int, parsestk:stack.stkele.bindinfo) bindinfo
let op = tokentext.R_2
let dict = dict.R_1
let types = types.R_1 + types.R_3
if op = "∧" ∧ types = [typeboolean, typeboolean] ∧ mode.input ∈ "body" then
 bindinfo(dict
  , ifthenelse(code.R_1, code.R_3, [Litfalse], typeboolean)
  , [typeboolean]
  , "")
else if op = "∨" ∧ types = [typeboolean, typeboolean] ∧ mode.input ∈ "body" then
 bindinfo(dict
  , ifthenelse(code.R_1, [Littrue], code.R_3, typeboolean)
  , [typeboolean]
  , "")
else
 let f = 
  if op = "≠" then
   [lookupbysig(dict, "=", types, input, place, parsestk), NotOp]
  else if op = "∉" then
   [lookupbysig(dict, "∈", types, input, place, parsestk), NotOp]
  else if op = "≥" then
   [lookupbysig(dict, "<", types, input, place, parsestk), NotOp]
  else if op = "≤" then
   [lookupbysig(dict, ">", types, input, place, parsestk), NotOp]
  else
   [lookupbysig(dict, [op_1], types, input, place, parsestk)]
 bindinfo(dict, code.R_1 + code.R_3 + f, [resulttype.first.f], "")

function unaryop(R:reduction.bindinfo
 , common:commoninfo
 , place:int
 , parsestk:stack.stkele.bindinfo
 , op:seq.word
 , exp:bindinfo) bindinfo
if op_1 = "process"_1 ∧ length.types.exp = 1 then
 let rt = resolvetype(types.common, %.(types.exp)_1)_1
 let processtype = processof.rt
 let dcws = deepcopyseqword
 let newcode = 
  [PreFref, deepcopySym.rt, PreFref, dcws, PreFref, last.code.exp]
  + subseq(code.exp, 1, length.code.exp - 1)
  + symbol(builtinmod.rt
   , "createthreadY"
   , [typeint, typeint, typeint] + paratypes.last.code.exp
   , processtype)
 bindinfo(dict.R
  , if mode.common ∈ "text" then
   code.exp + symbol(internalmod, "process", rt, rt)
  else
   newcode
  , [processtype]
  , "")
else if op_1 = "$"_1 ∧ length.types.exp = 2 ∧ first.types.exp = seqof.typeword then
 let f = 
  lookupbysig(dict.R, "+", [seqof.typeword, seqof.typeword], common, place, parsestk)
 let newcode = 
  if (types.exp)_2 = seqof.typeword then
   code.exp + f
  else
   let cvt = lookupbysig(dict.R, "%", [(types.exp)_2], common, place, parsestk)
   assert resulttype.cvt = seqof.typeword
   report
    errormessage("Expected function $(cvt) to have return type of seq.word", common, place, parsestk)
   code.exp + cvt + f
 bindinfo(dict.R, newcode, [resulttype.f], "")
else
 let f = lookupbysig(dict.R, op, types.exp, common, place, parsestk)
 let tmp = 
  if mode.common ∉ "text" ∧ op_1 = "next"_1 ∧ name.module.f ∈ "$for" then
   code.exp + Local(toint.first.%.parameter.para.module.f + nopara.f + 4)
   + symbol(internalmod, "next", paratypes.f + typeint, typeint)
  else
   code.exp + f
 bindinfo(dict.R, tmp, [resulttype.f], "")

function ifexp(R:reduction.bindinfo
 , ifpart:bindinfo
 , thenpart:bindinfo
 , elsepart:bindinfo
 , input:commoninfo
 , place:int
 , parsestk:stack.stkele.bindinfo) bindinfo
assert (types.ifpart)_1 = typeboolean
report
 errormessage("cond of if must be boolean but is $((types.ifpart)_1)", input, place, parsestk)
assert types.thenpart = types.elsepart
report errormessage("then and else types are different", input, place, parsestk)
bindinfo(dict.R
 , ifthenelse(code.ifpart, code.thenpart, code.elsepart, (types.thenpart)_1)
 , types.thenpart
 , "")

function addpara(dict:symboldict, name:seq.word, typ:bindinfo, place:int, parsestk:stack.stkele.bindinfo) bindinfo
bindinfo(dict
 , empty:seq.symbol
 , [resolvetype(tokentext.typ, common.dict, place, parsestk)]
 , name)

function addpara(dict:symboldict
 , name:seq.word
 , typ:bindinfo
 , place:int
 , parsestk:stack.stkele.bindinfo
 , old:bindinfo) bindinfo
bindinfo(dict
 , empty:seq.symbol
 , types.old + [resolvetype(tokentext.typ, common.dict, place, parsestk)]
 , text.old + name)

function forlocaldeclare(dict:symboldict
 , code:seq.symbol
 , seqtype:mytype
 , elename:seq.word
 , acctypes:seq.mytype
 , accnames:seq.word
 , input:commoninfo
 , place:int
 , parsestk:stack.stkele.bindinfo) bindinfo
assert isseq.seqtype
report
 errormessage("final expression in for list must be a sequence but it is of type:$(seqtype)"
  , input
  , place
  , parsestk)
{keep track so right next is used in nested fors}
let oldnesting = lookupbysig(dict, "for")
let dict0 = if isempty.oldnesting then dict else dict - oldnesting
let basetype = typebase(cardinality.dict0 + 2)
let resultsym = symbol(moduleref("internallib $for", basetype), "next", acctypes, basetype)
let nestingsym = 
 symbol(moduleref("internallib $for", basetype), "for", empty:seq.mytype, basetype)
let dict1 = dict0 + resultsym + nestingsym
for accdict = dict1, i = 1, name ∈ accnames do
 next(accdict + Local(name, acctypes_i, cardinality.accdict), i + 1)
/for (
 let lastidx = cardinality.accdict
 bindinfo(
  accdict + Local(toword.lastidx, seqtype, lastidx)
  + Local(elename_1, parameter.seqtype, lastidx + 1)
  + Local(toword(lastidx + 2), typeint, lastidx + 2)
  + Local(toword(lastidx + 3), typeint, lastidx + 3)
  + Local(toword(lastidx + 4), typeint, lastidx + 4)
  , code
  , acctypes + parameter.seqtype
  , accnames + elename)
)

function lookupbysig(dict:symboldict, name:seq.word) set.symbol
lookupbysig(dict, symbol(internalmod, name, typeint))

function forbody(dict:symboldict
 , vars:bindinfo
 , forbody:bindinfo
 , exitexp:bindinfo
 , endexp:bindinfo
 , input:commoninfo
 , place:int
 , parsestk:stack.stkele.bindinfo) bindinfo
let checktypes = 
 if tokentext.exitexp = "for" ∨ first.types.exitexp = typeboolean then
  {while type is OK. now check body type}
  if length.types.vars > 2 then
   if resulttype.lookupbysig(dict.vars, "for")_1 = (types.forbody)_1 then
    ""
   else
    "incorrect body type:$((types.forbody)_1)"
  else if first.types.vars = first.types.forbody then
   ""
  else
   "Type of body expression $(first.types.vars) must match accumaltor type $(first.types.forbody)"
 else
  "while expresssion type must be boolean"
assert isempty.checktypes report errormessage(checktypes, input, place, parsestk)
let resulttype = first.types.endexp
let newcode = 
 if mode.input ∈ "text" then
  code.vars + if tokentext.exitexp = "for" then [Littrue] else code.exitexp /if
  + code.forbody
  + code.endexp
  + Words.tokentext.vars
  + symbol(internalmod
   , "$fortext"
   , types.vars + typeboolean + (types.forbody)_1 + resulttype + seqof.typeword
   , resulttype)
 else
  let forbodytype = resulttype.lookupbysig(dict.vars, "for")_1
  let firstvar = toint.first.%.parameter.forbodytype
  let lastidx = Local(firstvar + length.types.vars - 1)
  let theseq = Local(value.lastidx + 2)
  let totallength = Local(value.lastidx + 3)
  let masterindex = Local(value.lastidx + 4)
  let theseqtype = last.types.vars
  let reverse = name.last.code.vars ∈ "reverse" ∧ name.module.last.code.vars ∈ "otherseq"
  let continue = if length.types.vars = 2 then [masterindex, continue.length.types.vars] else [Exit]
  let setElement = 
   [lastidx
    , if reverse then Lit.-1 else Lit.1
    , PlusOp
    , Define.value.masterindex
    , {let sequenceele = seq_(idx)} theseq
    , masterindex
    , symbol(builtinmod.typeint, "idxNB", seqof.theseqtype, typeint, theseqtype)
    , Define(value.lastidx + 1)]
  let header = 
   if reverse then
    code.vars >> 1 + Define.value.theseq + theseq + GetSeqLength
    + Define.value.totallength
    + totallength
    + Lit.1
    + PlusOp
    + Loopblock(types.vars >> 1 + typeint, firstvar, resulttype)
    + [lastidx, Lit.1, EqOp]
   else
    code.vars + Define.value.theseq + theseq + GetSeqLength + Define.value.totallength
    + Lit.0
    + Loopblock(types.vars >> 1 + typeint, firstvar, resulttype)
    + [lastidx, totallength, EqOp]
  header
  + if tokentext.exitexp = "for" then
   [Br2(1, 2)] + code.endexp + Exit + setElement
  else
   [Br2(2, 1)] + setElement + {3 while condition} code.exitexp + Br2(2, 1)
   + code.endexp
   + Exit
  /if
  + code.forbody
  + continue
  + if length.types.vars = 2 ∧ tokentext.exitexp = "for" ∧ islocal.first.code.forbody
  ∧ value.first.code.forbody = firstvar then
   let last = last.code.forbody
   if name.last ∈ "+" ∧ name.module.last ∈ "seq"
   ∧ para.module.last = parameter.first.types.forbody then
    [EndBlock, symbol(internalmod, "checkfornoop", resulttype, resulttype)]
   else
    [EndBlock]
  else
   [EndBlock]
bindinfo(dict, newcode, [resulttype], "")

function action(ruleno:int
 , dupinput:seq.word
 , place:int
 , R:reduction.bindinfo
 , parsestk:stack.stkele.bindinfo) bindinfo
{Alphabet.= ():>]-for * comment, [_/if is I if # then else let assert report ∧ ∨ $wordlist
 while /for W do wl wlend T X F2 A E FP NM L D F F1 G HH}
{RulePrecedence | HH HH comment | comment | let | assert | if | for | W | wl | I | [
 | $wordlist | (| E NM | E comment E | E E_E |_| E W.E | E E * E | E-E | * | E E-E |-| E E >
 E | E E = E | = | > | E E ∧ E | ∧ | E E ∨ E | ∨ | /for | E if E then E else E /if | /if | E if E then
 E else E | E assert E report D E | A W = E | E let A E | D E |}
let common = common.dict.R
if ruleno = {F HH E} 1 then
 addbody(R, common, place, parsestk)
else if ruleno = {F HH} 2 then
 R_1
else if ruleno = {HH HH comment} 3 then
 if mode.common ∈ "text" then
  bindinfo(dict.R, code.R_1 + Words.tokentext.R_2, types.R_1, "")
 else
  R_1
else if ruleno = {HH W NM (FP) T} 4 then
 createfunc(R, common, place, parsestk, tokentext.R_2, R_4, R_6)
else if ruleno = {HH W_(FP) T} 5 then
 createfunc(R, common, place, parsestk, tokentext.R_2, R_4, R_6)
else if ruleno = {HH W-(FP) T} 6 then
 createfunc(R, common, place, parsestk, tokentext.R_2, R_4, R_6)
else if ruleno = {HH W = (FP) T} 7 then
 createfunc(R, common, place, parsestk, tokentext.R_2, R_4, R_6)
else if ruleno = {HH W > (FP) T} 8 then
 createfunc(R, common, place, parsestk, tokentext.R_2, R_4, R_6)
else if ruleno = {HH W * (FP) T} 9 then
 createfunc(R, common, place, parsestk, tokentext.R_2, R_4, R_6)
else if ruleno = {HH W ∧ (FP) T} 10 then
 createfunc(R, common, place, parsestk, tokentext.R_2, R_4, R_6)
else if ruleno = {HH W ∨ (FP) T} 11 then
 createfunc(R, common, place, parsestk, tokentext.R_2, R_4, R_6)
else if ruleno = {HH W NM T} 12 then
 createfunc(R, common, place, parsestk, tokentext.R_2, R_2, R_3)
else if ruleno = {HH W NM is FP} 13 then
 let tp = 
  resolvetype(if isAbstract.modname.common then tokentext.R_2 + ".T" else tokentext.R_2
   , common
   , place
   , parsestk)
 bindinfo(dict.R, empty:seq.symbol, [tp] + types.R_4, text.R_4)
else if ruleno = {FP T} 14 then
 addpara(dict.R, ":", R_1, place, parsestk)
else if ruleno = {FP FP, T} 15 then
 addpara(dict.R, ":", R_3, place, parsestk, R_1)
else if ruleno = {FP W:T} 16 then
 addpara(dict.R, tokentext.R_1, R_3, place, parsestk)
else if ruleno = {FP FP, W:T} 17 then
 addpara(dict.R, tokentext.R_3, R_5, place, parsestk, R_1)
else if ruleno = {FP comment W:T} 18 then
 addpara(dict.R, tokentext.R_2, R_4, place, parsestk)
else if ruleno = {FP FP, comment W:T} 19 then
 addpara(dict.R, tokentext.R_4, R_6, place, parsestk, R_1)
else if ruleno = {NM W} 20 then
 R_1
else if ruleno = {NM W:T} 21 then
 bindinfo(dict.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1 + tokentext.R_3)
else if ruleno = {T W} 22 then
 R_1
else if ruleno = {T W.T} 23 then
 bindinfo(dict.R
  , empty:seq.symbol
  , empty:seq.mytype
  , tokentext.R_1 + "." + tokentext.R_3)
else if ruleno = {E NM} 24 then
 if mode.common ∈ "body text" then
  let f = lookupbysig(dict.R, text.R_1, empty:seq.mytype, common, place, parsestk)
  bindinfo(dict.R, [f], [resulttype.f], "")
 else
  R_1
else if ruleno = {E NM (L)} 25 then
 unaryop(R, common, place, parsestk, tokentext.R_1, R_3)
else if ruleno = {E (E)} 26 then
 R_2
else if ruleno = {E if E then E else E} 27 then
 ifexp(R, R_2, R_4, R_6, common, place, parsestk)
else if ruleno = {E if E then E else E /if} 28 then
 ifexp(R, R_2, R_4, R_6, common, place, parsestk)
else if ruleno = {E E_E} 29 then
 opaction(R, common, place, parsestk)
else if ruleno = {E-E} 30 then
 unaryop(R, common, place, parsestk, tokentext.R_1, R_2)
else if ruleno = {E W.E} 31 then
 unaryop(R, common, place, parsestk, tokentext.R_1, R_3)
else if ruleno = {E E * E} 32 then
 opaction(R, common, place, parsestk)
else if ruleno = {E E-E} 33 then
 opaction(R, common, place, parsestk)
else if ruleno = {E E = E} 34 then
 opaction(R, common, place, parsestk)
else if ruleno = {E E > E} 35 then
 opaction(R, common, place, parsestk)
else if ruleno = {E E ∧ E} 36 then
 opaction(R, common, place, parsestk)
else if ruleno = {E E ∨ E} 37 then
 opaction(R, common, place, parsestk)
else if ruleno = {L E} 38 then
 R_1
else if ruleno = {L L, E} 39 then
 bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3, "")
else if ruleno = {E [L]} 40 then
 let types = types.R_2
 assert for acc = true, @e ∈ types do acc ∧ types_1 = @e /for (acc)
 report errormessage("types do not match in build", common, place, parsestk)
 bindinfo(dict.R, code.R_2 + Sequence(types_1, length.types), [seqof.types_1], "")
else if ruleno = {A W = E} 41 then
 let name = tokentext.R_1
 assert isempty.lookupbysig(dict.R, name)
 report errormessage("duplicate symbol:$(name)", common, place, parsestk)
 let newdict = dict.R + Local(name_1, (types.R_3)_1, cardinality.dict.R)
 bindinfo(newdict, code.R_3 + Define(name_1, cardinality.dict.R), types.R_3, name)
else if ruleno = {E let A E} 42 then
 let letsym = 
  if mode.common ∈ "text" then
   [symbol(internalmod, "let", typeint, first.types.R_3, first.types.R_3)]
  else
   empty:seq.symbol
 bindinfo(dict.R_1, code.R_2 + code.R_3 + letsym, types.R_3, "")
else if ruleno = {E assert E report D E} 43 then
 assert (types.R_2)_1 = typeboolean
 report errormessage("condition in assert must be boolean in:", common, place, parsestk)
 assert (types.R_4)_1 = seqof.typeword
 report errormessage("report in assert must be seq of word in:", common, place, parsestk)
 let typ = (types.R_5)_1
 let assertsym = symbol(builtinmod.typ, "assert", seqof.typeword, typ)
 bindinfo(dict.R
  , [Start.(types.R_5)_1] + code.R_2 + Br2(1, 2) + code.R_5 + Exit
  + code.R_4
  + assertsym
  + Exit
  + if mode.common ∈ "text" then
   symbol(internalmod, "report", typeint)
  else
   EndBlock
  , types.R_5
  , "")
else if ruleno = {E I} 44 then
 bindlit.R
else if ruleno = {E I.I} 45 then
 bindinfo(dict.R
  , [Words(tokentext.R_1 + "." + tokentext.R_3), makerealSymbol]
  , [typereal]
  , "")
else if ruleno = {E $wordlist} 46 then
 let s = tokentext.R_1
 bindinfo(dict.R
  , [Words.if mode.common ∈ "text" then s else subseq(s, 2, length.s - 1)]
  , [seqof.typeword]
  , "")
else if ruleno = {E comment E} 47 then
 if mode.common ∈ "text" then
  bindinfo(dict.R
   , [Words.tokentext.R_1] + code.R_2
   + symbol(internalmod, "{", seqof.typeword, first.types.R_2, first.types.R_2)
   , types.R_2
   , "")
 else
  R_2
else if ruleno = {F1 W = E} 48 then
 let name = tokentext.R_1
 assert isempty.lookupbysig(dict.R, name)
 report errormessage("duplicate symbol:$(name)", common, place, parsestk)
 bindinfo(dict.R_1, code.R_3, types.R_3, name)
else if ruleno = {F1 F1, W = E} 49 then
 let name = tokentext.R_3
 assert isempty.lookupbysig(dict.R, name)
 report errormessage("duplicate symbol:$(name)", common, place, parsestk)
 bindinfo(dict.R
  , code.R_1 + code.R_5
  , types.R_1 + types.R_5
  , tokentext.R_1 + tokentext.R_3)
else if ruleno = {F2 F1, W-E} 50 then
 let name = tokentext.R_3
 assert isempty.lookupbysig(dict.R, name)
 report errormessage("duplicate symbol:$(name)", common, place, parsestk)
 forlocaldeclare(dict.R
  , code.R_1 + code.R_5
  , last.types.R_5
  , [last.tokentext.R_3]
  , types.R_1
  , tokentext.R_1
  , common
  , place
  , parsestk)
else if ruleno = {E for F2 do E /for (E)} 51 then
 forbody(dict.R_1, R_2, R_4, R_1, R_7, common, place, parsestk)
else if ruleno = {E for F2 while E do E /for (E)} 52 then
 forbody(dict.R_1, R_2, R_6, R_4, R_9, common, place, parsestk)
else if ruleno = {D E} 53 then
 R_1
else if ruleno = {X wl E} 54 then
 binary2(R, common, place, parsestk, R_1, R_2, false)
else if ruleno = {X X wl E} 55 then
 let B = binary2(R, common, place, parsestk, R_1, R_2, true)
 unaryop(R
  , common
  , place
  , parsestk
  , "$"
  , bindinfo(dict.R, code.B + code.R_3, types.B + types.R_3, ""))
else if ruleno = {E X wlend} 56 then
 binary2(R, common, place, parsestk, R_1, R_2, true)
else if ruleno = {G F #} 57 then
 R_1
else
 {ruleno}
 assert false report "invalid rule number" + toword.ruleno
 R_1

function binary2(R:reduction.bindinfo
 , common:commoninfo
 , place:int
 , parsestk:stack.stkele.bindinfo
 , arg1:bindinfo
 , arg2:bindinfo
 , switch:boolean) bindinfo
let code = 
 if switch then
  let s1 = tokentext.arg2
  let s2 = subseq(s1, 2, length.s1 - 1)
  code.arg1 + Words.if mode.common ∈ "text" then dq.s2 else s2
 else
  let s1 = tokentext.arg1
  let s2 = subseq(s1, 2, length.s1 - 1)
  [Words.if mode.common ∈ "text" then dq.s2 else s2] + code.arg2
let types = if switch then types.arg1 + seqof.typeword else [seqof.typeword] + types.arg2
unaryop(R, common, place, parsestk, "$", bindinfo(dict.R, code, types, "")) 