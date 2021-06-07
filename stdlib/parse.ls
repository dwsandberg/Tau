Module parse

use UTF8

use format

use standard

use symbolE

use parsersupport.bindinfo

use seq.char

use seq.mytype

use seq.symbol

use set.symbol

use set.word

use seq.token.bindinfo

use seq.seq.mytype

use seq.seq.symbol

use encoding.seq.token.bindinfo

use seq.seq.token.bindinfo

Export getheader(s:seq.word)seq.word

Export type:bindinfo

type bindinfo is dict:set.symbol, code:seq.symbol, types:seq.mytype, tokentext:seq.word

Export dict(bindinfo)set.symbol

Function parsedcode(b:bindinfo)seq.symbol code.b

Export types(bindinfo)seq.mytype

Function funcparametertypes(t:bindinfo)seq.mytype
 for acc = empty:seq.mytype, @e = subseq(types.t, 3, length.types.t)do acc + parameter.@e /for(acc)

Function funcname(t:bindinfo)seq.word text.t

Function funcreturntype(t:bindinfo)mytype(types.t)_2

/function expect(stateno:int)seq.word let l = @(+, kk(stateno),"", arithseq(length.tokenlist, 1, 1))toseq(asset.l-asset."-=_^∧ ∨ *")

/function kk(stateno:int, token:int)seq.word if 0 ≠ actiontable_(length.tokenlist * stateno + token)then [ tokenlist_token]else empty:seq.word

function errormessage(message:seq.word, input:seq.word, place:int)seq.word
" /< literal" + message + " />" + prettynoparse.subseq(input, 1, place)

Function parse(dict:set.symbol, input:seq.word)bindinfo parse(bindinfo(dict, empty:seq.symbol, empty:seq.mytype,""), input)

/ Function cachevalue seq.encodingpair.seq.token.bindinfo encoding:seq.encodingpair.seq.token.bindinfo

/ use seq.encodingpair.seq.token.bindinfo

/ use encoding.seq.token.bindinfo

Function parse(b:bindinfo, input:seq.word)bindinfo let a = sortedlextable:bindinfo
 parse:bindinfo(b, a, input)

let a = if length.cachevalue = 0 then let discard = encode(sortedlextable:bindinfo){ data.(cachevalue)_1 } else data.(cachevalue)_1

function forward(stk:bindinfo, token:bindinfo)bindinfo bindinfo(dict.stk, empty:seq.symbol, empty:seq.mytype, tokentext.token)

function attribute:bindinfo(w:seq.word)bindinfo bindinfo(empty:set.symbol, empty:seq.symbol, empty:seq.mytype, w)

function text(b:bindinfo)seq.word tokentext.b

function hash(l:seq.token.bindinfo)int length.l

function assignencoding(p:seq.encodingpair.seq.token.bindinfo, a:seq.token.bindinfo)int assignrandom(p, a)

function bindlit(R:reduction.bindinfo)bindinfo
let chars = decodeword.first.text.R_1
 if length.chars > 1 ∧ chars_2 ∈ decodeword.first."Xx"then
  bindinfo(dict.R, [ Lit.cvttoint.chars], [ typebits],"")
 else bindinfo(dict.R, [ Lit.cvttoint.chars], [ typeint],"")

function opaction(R:reduction.bindinfo, input:seq.word, place:int)bindinfo
let op = tokentext.R_2
let dict = dict.R_1
let types = types.R_1 + types.R_3
 if op = "∧" ∧ types = [ typeboolean, typeboolean]then
  bindinfo(dict, ifthenelse(code.R_1, code.R_3, [ Litfalse], typeboolean), [ typeboolean],"")
 else if op = "∨" ∧ types = [ typeboolean, typeboolean]then
  bindinfo(dict, ifthenelse(code.R_1, [ Littrue], code.R_3, typeboolean), [ typeboolean],"")
 else if op = "≠"then
 let f = lookupbysig(dict,"=", types, input, place)
 bindinfo(dict, code.R_1 + code.R_3 + f + NotOp, [ resulttype.f],"")
 else if op = "∉"then
 let f = lookupbysig(dict,"∈", types, input, place)
 bindinfo(dict, code.R_1 + code.R_3 + f + NotOp, [ resulttype.f],"")
 else if op = "≥"then
 let f = lookupbysig(dict,"<", types, input, place)
 bindinfo(dict, code.R_1 + code.R_3 + f + NotOp, [ resulttype.f],"")
 else if op = "≤"then
 let f = lookupbysig(dict,">", types, input, place)
 bindinfo(dict, code.R_1 + code.R_3 + f + NotOp, [ resulttype.f],"")
 else
  let f = lookupbysig(dict, [ op_1], types, input, place)
  bindinfo(dict, code.R_1 + code.R_3 + f, [ resulttype.f],"")

function unaryop(R:reduction.bindinfo, input:seq.word, place:int, op:seq.word, exp:bindinfo)bindinfo
 if op_1 = "process"_1 then
 let nopara = nopara.last.code.exp
 let rt =(types.exp)_1
 let dcrt = deepcopysym(dict.R, rt)
 assert cardinality.dcrt = 1 report errormessage("parameter type" + print.rt + "is undefined in", input, place)
  let dcws = deepcopysym(dict.R, seqof.typeword)
  assert cardinality.dcws = 1 report errormessage("type word seq is require for process in", input, place)
   let processtype = typeref."process process."
   let newcode = [ Fref.dcrt_1, Fref.dcws_1, Fref.last.code.exp]
   + subseq(code.exp, 1, length.code.exp - 1)
   + symbol3(moduleref("builtin", typeint),"createthreadY", [ typeint, typeint, typeint] + paratypes.last.code.exp, addabstract(processtype, resulttype.last.code.exp))
   bindinfo(dict.R, newcode, [ addabstract(processtype, rt)],"")
 else
  let f = lookupbysig(dict.R, op, types.exp, input, place)
  bindinfo(dict.R, code.exp + f, [ resulttype.f],"")

function addparameter(dict:set.symbol, orgsize:int, input:seq.word, place:int, m:mytype)set.symbol
let parametername = fldname.m
let parametertype = fldtype.m
 assert isempty.lookupLocal(dict, [ parametername]) ∨ parametername = ":"_1 report errormessage("duplciate symbol:" + parametername, input, place)
 let parano = cardinality.dict - orgsize + 1
  dict + Parameter(parametername, parametertype, parano)

function lookupbysig(dict:set.symbol, name:seq.word, paratypes:seq.mytype, input:seq.word, place:int)symbol
let f = lookup(dict, name, paratypes)
assert not.isempty.f report errormessage("cannot find 1" + name + "("
 + for acc ="", @e = paratypes do list(acc,",", print.@e)/for(acc)
 + ")", input, place)
 assert cardinality.f = 1 report errormessage("found more that one"
  + for acc ="", @e = toseq.f do acc + print.@e /for(acc), input, place)
  f_1

function createfunc(R:reduction.bindinfo, input:seq.word, place:int, funcname:seq.word, paralist:seq.mytype, functypebind:bindinfo, exp:bindinfo)bindinfo
let functype = gettype.functypebind
 assert functype = (types.exp)_1 ∨ (types.exp)_1 ∈ [ typeref."internal1 headdict."]report errormessage("function type of" + print.functype + "does not match expression type" + print.(types.exp)_1, input, place)
 bindinfo(dict.R, code.exp, [ typeref."unused headdict. ", functype] + paralist, funcname)

function isdefined(R:reduction.bindinfo, input:seq.word, place:int, type:mytype)bindinfo
let dict = dict.R
 if cardinality.dict < 25 ∨ type ∈ [ typeT, typeint, typereal] ∨ isabstract.type then
  bindinfo(dict, empty:seq.symbol, [ type],"")
 else
  let a = lookup(dict,"type:" + print.type, [ type])
  assert cardinality.a = 1 report errormessage("parameter type" + print.type + "is undefined in", input, place)
   bindinfo(dict, empty:seq.symbol, [ type],"")

function gettype(b:bindinfo)mytype(types.b)_1

function dict(r:reduction.bindinfo)set.symbol dict.last.r

function ifexp(R:reduction.bindinfo, ifpart:bindinfo, thenpart:bindinfo, elsepart:bindinfo, input:seq.word, place:int)bindinfo
 assert(types.ifpart)_1 = typeboolean report errormessage("cond of if must be boolean", input, place)
 assert types.thenpart = types.elsepart report errormessage("then and else types are different", input, place)
  bindinfo(dict.R, ifthenelse(code.ifpart, code.thenpart, code.elsepart,(types.thenpart)_1), types.thenpart,"")

function action(ruleno:int, input:seq.word, place:int, R:reduction.bindinfo)bindinfo
 if ruleno = { G F # }1 then R_1
 else if ruleno = { F W NM(FP)T E }2 then
  createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W_(FP)T E }3 then
  createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W-(FP)T E }4 then
  createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W =(FP)T E }5 then
  createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W >(FP)T E }6 then
  createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W *(FP)T E }7 then
  createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W ∧(FP)T E }8 then
  createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W ∨(FP)T E }9 then
  createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W NM T E }10 then
  createfunc(R, input, place, tokentext.R_2, empty:seq.mytype, R_3, R_4)
 else if ruleno = { F W NM is P }11 then
  bindinfo(dict.R, empty:seq.symbol, types.R_4,"record" + tokentext.R_2)
 else if ruleno = { FP P }12 then
  bindinfo(for acc = dict.R, @e = types.R_1 do addparameter(acc, cardinality.dict.R, input, place, @e)/for(acc), empty:seq.symbol, types.R_1,"")
 else if ruleno = { P T }13 then
  bindinfo(dict.R, empty:seq.symbol, [ addabstract(typeref.":internal.", gettype.R_1)],"")
 else if ruleno = { P P, T }14 then
  bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ addabstract(typeref.":internal.", gettype.R_3)],"")
 else if ruleno = { P W:T }15 then
  bindinfo(dict.R, empty:seq.symbol, [ addabstract(typeref(tokentext.R_1 + "internal."), gettype.R_3)],"")
 else if ruleno = { P P, W:T }16 then
  bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ addabstract(typeref(tokentext.R_3 + "internal."), gettype.R_5)],"")
 else if ruleno = { P comment W:T }17 then
  bindinfo(dict.R, empty:seq.symbol, [ addabstract(typeref(tokentext.R_2 + "internal."), gettype.R_4)],"")
 else if ruleno = { P P, comment W:T }18 then
  bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ addabstract(typeref(tokentext.R_4 + "internal."), gettype.R_6)],"")
 else if ruleno = { E NM }19 then
 let id = tokentext.R_1
 let f = lookupbysig(dict.R, id, empty:seq.mytype, input, place)
 bindinfo(dict.R, [ f], [ resulttype.f],"")
 else if ruleno = { E NM(L)}20 then unaryop(R, input, place, tokentext.R_1, R_3)
 else if ruleno = { E(E)}21 then R_2
 else if ruleno = { E if E then E else E }22 then ifexp(R, R_2, R_4, R_6, input, place)
 else if ruleno = { E if E then E else E fi }23 then
  ifexp(R, R_2, R_4, R_6, input, place)
 else if ruleno = { E E_E }24 then opaction(R, input, place)
 else if ruleno = { E-E }25 then unaryop(R, input, place, tokentext.R_1, R_2)
 else if ruleno = { E W.E }26 then unaryop(R, input, place, tokentext.R_1, R_3)
 else if ruleno = { E E * E }27 then opaction(R, input, place)
 else if ruleno = { E E-E }28 then opaction(R, input, place)
 else if ruleno = { E E = E }29 then opaction(R, input, place)
 else if ruleno = { E E > E }30 then opaction(R, input, place)
 else if ruleno = { E E ∧ E }31 then opaction(R, input, place)
 else if ruleno = { E E ∨ E }32 then opaction(R, input, place)
 else if ruleno = { L E }33 then R_1
 else if ruleno = { L L, E }34 then
  bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3,"")
 else if ruleno = { E [ L]}35 then
 let types = types.R_2
  assert for acc = true, @e = types do acc ∧ types_1 = @e /for(acc)report errormessage("types do not match in build", input, place)
  bindinfo(dict.R, code.R_2 + Sequence(types_1, length.types), [ seqof.types_1],"")
 else if ruleno = { A W = E }36 then
 let name = tokentext.R_1
  assert isempty.lookupLocal(dict.R, name)report errormessage("duplicate symbol:" + name, input, place)
  let newdict = dict.R + Local(name,(types.R_3)_1)
  bindinfo(newdict, code.R_3 + Define.name, types.R_3, name)
 else if ruleno = { E let A E }37 then
  bindinfo(dict.R_1, code.R_2 + code.R_3, types.R_3,"")
 else if ruleno = { E assert E report D E }38 then
  assert(types.R_2)_1 = typeboolean report errormessage("condition in assert must be boolean in:", input, place)
  assert(types.R_4)_1 = seqof.typeword report errormessage("report in assert must be seq of word in:", input, place)
   let assertsym = symbol4(moduleref("builtin",(types.R_5)_1),"assert"_1, typeT, [ seqof.typeword],(types.R_5)_1)
   bindinfo(dict.R, ifthenelse(code.R_2, code.R_5, code.R_4 + assertsym,(types.R_5)_1), types.R_5,"")
 else if ruleno = { E I }39 then bindlit.R
 else if ruleno = { E I.I }40 then
  bindinfo(dict.R
  , [ Words(tokentext.R_1 + "." + tokentext.R_3), symbol3(moduleref."UTF8","makereal", seqof.typeword, typereal)]
  , [ typereal]
  ,""
  )
 else if ruleno = { T W }41 then isdefined(R, input, place, typeref(tokentext.R_1 + "?."))
 else if ruleno = { T W.T }42 then
  isdefined(R, input, place, addabstract(typeref(tokentext.R_1 + "internal."),(types.R_3)_1))
 else if ruleno = { E $wordlist }43 then
 let s = tokentext.R_1
  bindinfo(dict.R, [ Words.subseq(s, 2, length.s - 1)], [ seqof.typeword],"")
 else if ruleno = { E comment E }44 then R_2
 else if ruleno = { NM W }45 then R_1
 else if ruleno = { NM W:T }46 then
  bindinfo(dict.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1 + ":" + print.(types.R_3)_1)
 else if ruleno = { F1 W = E }47 then
 let name = tokentext.R_1
  assert isempty.lookupLocal(dict.R, name)report errormessage("duplicate symbol:" + name, input, place)
  bindinfo(dict.R_1, code.R_3, types.R_3, name)
 else if ruleno = { F1 F1, W = E }48 then
 let name = tokentext.R_3
  assert isempty.lookupLocal(dict.R, name)report errormessage("duplicate symbol:" + name, input, place)
  bindinfo(dict.R, code.R_1 + code.R_5, types.R_1 + types.R_5, tokentext.R_1 + tokentext.R_3)
 else if ruleno = { F2 F1 }49 then forlocaldeclare(R_1, input, place)
 else if ruleno = { E for F2 do E end(E)}50 then
  forbody(dict.R_1, R_2, R_4, R_1, R_7, input, place)
 else if ruleno = { E for F2 while E do E end(E)}51 then
  forbody(dict.R_1, R_2, R_6, R_4, R_9, input, place)
 else
  assert ruleno = { D E }52 report"invalid rule number" + toword.ruleno
   R_1

function forlocaldeclare(a:bindinfo, input:seq.word, place:int)bindinfo
let seqtype = last.types.a
 assert isseq.seqtype report"final expression in for list must be a sequence but it is of type:" + print.seqtype
  assert length.types.a ≠ 1 report errormessage("For must have at least one accumulator" + print.length.types.a, input, place)
  let elename = [ last.tokentext.a]
  let elesym = symbol3(moduleref("$for", parameter.seqtype), elename, empty:seq.mytype, parameter.seqtype)
  let dict1 = if length.types.a > 1 then
   { keep track so right next is used in nested fors }
   let resultsym = symbol3(moduleref."$for","next", types.a >> 1, 
      addabstract(typeref."$base . .",typeref([toword.place]+". ."))
   )
   let nestingsym = symbol3(tomodref.resulttype.resultsym,"for", empty:seq.mytype, resulttype.resultsym)
   let oldnesting = lookupLocal(dict.a,"for")
   if isempty.oldnesting then dict.a else dict.a - oldnesting /if + resultsym + nestingsym
  else dict.a
  let accumulators = for acc = empty:seq.symbol, i = 1, name = tokentext.a >> 1 do
   next(acc + symbol3(moduleref("$for",(types.a)_i), [ name], empty:seq.mytype,(types.a)_i), i + 1)
  /for(acc)
  bindinfo(dict1 ∪ asset(accumulators + elesym), code.a + accumulators + elesym, types.a, elename)

function forbody(dict:set.symbol, vars:bindinfo, forbody:bindinfo, exitexp:bindinfo, endexp:bindinfo, input:seq.word, place:int)bindinfo
let checktypes = if tokentext.exitexp = "for" ∨ first.types.exitexp = typeboolean then
 { while type is OK. now check body type }
 if length.types.vars > 2 then
  if resulttype.lookupLocal(dict.vars,"for")_1 = (types.forbody)_1 then""
  else"incorrect body type:" + print.(types.forbody)_1
 else if first.types.vars = first.types.forbody then""
 else
 "Type of body expression" + print.first.types.vars + "must match accumaltor type"
  + print.first.types.forbody
else"while expresssion type must be boolean"
assert isempty.checktypes report errormessage(checktypes, input, place)
 let resulttype = first.types.endexp
 let sym = symbol3(moduleref("builtin", typeint),"forexp", types.vars + types.vars >> 1 + parameter.last.types.vars + typeptr + typeboolean
 + resulttype, resulttype)
 let newcode = code.vars + code.forbody
 + if tokentext.exitexp = "for"then [ Littrue]else code.exitexp /if
 + code.endexp
 + sym
  bindinfo(dict, newcode, [ resulttype],"") 