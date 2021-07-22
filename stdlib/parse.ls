Module parse

use UTF8

use format

use mytype

use set.mytype

use standard

use symbol

use parsersupport.bindinfo

use seq.char

use seq.mytype

use seq.symbol

use set.symbol

use symboldict

Function parsedcode(b:bindinfo)seq.symbol code.b

Export getheader(s:seq.word)seq.word

Function tosymfromparse(t:bindinfo, module:modref)symbol
let name = text.t
let funcreturntype=last.types.t 
let paratypes = for acc = empty:seq.mytype, @e =  subseq(types.t,if length.name=1 then 1 else 2,length.types.t -1) do acc + @e /for(acc)
 if length.name = 1 then
  if name = "true"then Littrue
  else if name = "false"then Litfalse else symbol(module, name, paratypes, funcreturntype)
 else
  let typeinname=first.types.t
   symbol4(module, name_1, typeinname, paratypes, funcreturntype)


Function typeflds(b:bindinfo) seq.mytype 
for acc=empty:seq.mytype,idx=1,t=types.b << 1 do
 next(acc+addabstract(typeref([(text.b)_idx] +"internal."), t),idx+1)
/for(acc)

function fixNM(t:seq.word) seq.word
if length.t=1  then t else [t_1,":"_1]+(t << 1)

Export type:bindinfo

function forward(stk:bindinfo, token:bindinfo)bindinfo bindinfo(dict.stk, empty:seq.symbol, empty:seq.mytype, tokentext.token)

function attribute:bindinfo(w:seq.word)bindinfo bindinfo(empty:symboldict, empty:seq.symbol, empty:seq.mytype, w)

Function text(b:bindinfo)seq.word tokentext.b

function dict(r:reduction.bindinfo) symboldict dict.last.r

Function bindinfo(dict:symboldict, types:seq.mytype, tokentext:seq.word)bindinfo  bindinfo(dict, empty:seq.symbol, types, tokentext)





function resolvetype(text:seq.word, common:commoninfo, place:int)mytype
let a = resolvetype(types.common, text,mode.common /in "gather use")
let w = for acc = EOL, t = toseq.types.common do acc + print.t /for(acc + EOL)
assert not.isempty.a report errormessage("cannot resolve type" + text + w, common, place)
 a_1

Function parse(dict:symboldict)bindinfo
let a = sortedlextable:bindinfo
 parse:bindinfo(bindinfo(dict, empty:seq.mytype,""), a, input.common.dict)

function createfunc(R:reduction.bindinfo, common:commoninfo, place:int, funcname:seq.word, paralist:seq.mytype, functypebind:bindinfo, exp:bindinfo)bindinfo
let returntype = resolvetype(text.functypebind, common, place)
 assert mode.common ∈  "symbol gather" ∨ returntype = (types.exp)_1 report 
 errormessage("function type of" + print.returntype + "does not match expression type" + print.(types.exp)_1, common, place)
 if length.funcname > 1 then
   bindinfo(dict.R, code.exp, [ resolvetype(funcname << 1, common, place)] + paralist + returntype, funcname)
 else bindinfo(dict.R, code.exp, paralist + returntype, funcname)

function errormessage(message:seq.word, common:commoninfo, place:int)seq.word
" /< literal" + message + " />" + print.modname.common + prettynoparse.subseq(input.common, 1, place)

function addparameters(b:bindinfo, common:commoninfo,place:int)bindinfo
 let flds = for flds = dict.b, idx=1, paratype = types.b do 
 assert isempty.lookupbysig(flds, [ (text.b)_idx]) ∨ (text.b)_idx = ":"_1 report errormessage("duplciate symbol:" + (text.b)_idx, common, place)
 next(flds + Local((text.b)_idx, paratype, idx), idx + 1)
  /for(flds)
  bindinfo(flds , empty:seq.symbol, if mode.common =first."gather" then types.b else empty:seq.mytype ,"")

function lookupbysig(dict:symboldict, name:seq.word, paratypes:seq.mytype, common:commoninfo, place:int)symbol
let sym3 = if length.name = 1 then symbol(internalmod, name, paratypes, typeint)
else symbol4(internalmod, name_1, resolvetype(name << 1, common, place), paratypes, typeint)
let f = lookupbysig( dict, sym3)
assert not.isempty.f report errormessage("cannot find 1" + fixNM.name + "("
 + for acc ="", @e = paratypes do list(acc,",", print.@e)/for(acc)
 + ")", common, place)
 assert cardinality.f = 1 report errormessage("found more than one"
  + for acc ="", @e = toseq.f do acc + print.@e /for(acc), common, place)
  let discard = for acc ="", sym2 = requires(dict,f_1) do
    let xxx = lookupbysig( dict,  sym2)
  assert not.isempty.xxx ∨ isabstract.module.f_1 report
     errormessage("require unbound" + print.f_1 + print.sym2, common, place)
   {let kk=print.sym2+print.xxx_1}
   let discard2=if not.isempty.xxx then 
   let discard =encode.requireencoding(sym2,xxx_1) 1 else 1
   { assert  kk /in[ "encoding.indexedword:=(indexedword, indexedword)boolean wordfreq:=(indexedword, indexedword)boolean"
    ,"seq.bits:=(bits, bits)boolean bits:=(bits, bits)boolean"
    ,"encoding.ccc:=(ccc, ccc)boolean testseq:=(ccc, ccc)boolean"
    ,"encoding.ccc:hash(ccc)int testseq:hash(ccc)int"
    ,"seq.typereal:=(typereal, typereal)boolean testseq:=(typereal, typereal)boolean"] report "requires"+kk
   } acc
  /for(acc)
  f_1
  
  use encoding.requireencoding
  
type requireencoding is  a:symbol,b:symbol

function hash(a:requireencoding) int  hash.a.a

function =(x:requireencoding,y:requireencoding) boolean a.x=a.y

function assignencoding(p:seq.encodingpair.requireencoding, a:requireencoding)int 
 assignrandom(p, a)
 
use seq.symdef

Function requirematch seq.symdef
for acc=empty:seq.symdef,  p=encoding:seq.encodingpair.requireencoding do 
  acc+  symdef(a.data.p, for   paras= empty:seq.symbol,   i=arithseq(nopara.a.data.p,1,1) do paras+Local.i /for(paras+b.data.p)) 
  /for(acc)

function bindlit(R:reduction.bindinfo)bindinfo
let chars = decodeword.first.text.R_1
let rt= if length.chars > 1 ∧ chars_2 ∈ decodeword.first."Xx"then   typebits else typeint  
 bindinfo(dict.R
 , [ if mode.common.dict.R = "text"_1 then symbol(internalmod, text.R_1, rt)else Lit.cvttoint.chars]
 , [ rt]
 ,""
 )

function opaction(R:reduction.bindinfo, input:commoninfo, place:int)bindinfo
let op = tokentext.R_2
let dict = dict.R_1
let types = types.R_1 + types.R_3
 if op = "∧" ∧ types = [ typeboolean, typeboolean] ∧ mode.input ∈ "body"then
  bindinfo(dict, ifthenelse(code.R_1, code.R_3, [ Litfalse], typeboolean), [ typeboolean],"")
 else if op = "∨" ∧ types = [ typeboolean, typeboolean] ∧ mode.input ∈ "body"then
  bindinfo(dict, ifthenelse(code.R_1, [ Littrue], code.R_3, typeboolean), [ typeboolean],"")
 else 
  let f = if op = "≠"then [ lookupbysig(dict,"=", types, input, place), NotOp]
  else if op = "∉"then [ lookupbysig(dict,"∈", types, input, place), NotOp]
  else if op = "≥"then [ lookupbysig(dict,"<", types, input, place), NotOp]
  else if op = "≤"then [ lookupbysig(dict,">", types, input, place), NotOp]
  else [ lookupbysig(dict, [ op_1], types, input, place)]
  bindinfo(dict, code.R_1 + code.R_3 +  f, [ resulttype.first.f],"")

function unaryop(R:reduction.bindinfo, common:commoninfo, place:int, op:seq.word, exp:bindinfo)bindinfo
 if op_1 = "process"_1 then
    let rt= resolvetype(types.common,print.(types.exp)_1)_1
    let processtype = processof.rt
   let dcws =symbol4(moduleref("seq",typeword),"type"_1,seqof.typeword , [seqof.typeword ]  ,seqof.typeword )
   let newcode = [PreFref,deepcopySym.rt,PreFref,dcws,PreFref,last.code.exp]
   + subseq(code.exp, 1, length.code.exp - 1)
   + symbol(builtinmod.rt,"createthreadY", [ typeint, typeint, typeint] + paratypes.last.code.exp,processtype)
   bindinfo(dict.R
   , if mode.common ∈ "text"then code.exp + symbol(internalmod,"process", rt, rt)else newcode
 , [ processtype],"")
 else
  let f = lookupbysig(dict.R, op, types.exp, common, place)
  bindinfo(dict.R, code.exp + f, [ resulttype.f],"")
    

function ifexp(R:reduction.bindinfo, ifpart:bindinfo, thenpart:bindinfo, elsepart:bindinfo, input:commoninfo, place:int)bindinfo
 assert(types.ifpart)_1 = typeboolean report errormessage("cond of if must be boolean but is" + print.(types.ifpart)_1, input, place)
 assert types.thenpart = types.elsepart report errormessage("then and else types are different", input, place)
  bindinfo(dict.R, ifthenelse(code.ifpart, code.thenpart, code.elsepart,(types.thenpart)_1), types.thenpart,"")

 function addpara(dict:symboldict,name:seq.word,typ:bindinfo,place:int) bindinfo
  bindinfo(dict,empty:seq.symbol, [ resolvetype(tokentext.typ, common.dict, place)],name)

function addpara(dict:symboldict,name:seq.word,typ:bindinfo,place:int,old:bindinfo) bindinfo
  bindinfo(dict,empty:seq.symbol, types.old+[ resolvetype(tokentext.typ, common.dict, place)],text.old+name)

function action(ruleno:int, dupinput:seq.word, place:int, R:reduction.bindinfo)bindinfo
 let common=common.dict.R
 if ruleno = { G F # }1 then R_1
 else if ruleno = { F W NM(FP)T E }2 then
  createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W_(FP)T E }3 then
  createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W-(FP)T E }4 then
  createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W =(FP)T E }5 then
  createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W >(FP)T E }6 then
  createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W *(FP)T E }7 then
  createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W ∧(FP)T E }8 then
  createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W ∨(FP)T E }9 then
  createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)
 else if ruleno = { F W NM T E }10 then
  createfunc(R, common, place, tokentext.R_2, empty:seq.mytype, R_3, R_4)
 else if ruleno = { F W NM is P }11 then
 let tp = resolvetype(if isabstract.modname.common then tokentext.R_2 + ".T"else tokentext.R_2, common, place)
 bindinfo(dict.R,empty:seq.symbol, [ tp] + types.R_4, text.R_4)
 else if ruleno = { FP P }12 then 
 if mode.common ∉ "symbol"then  addparameters(R_1, common,place) else R_1
 else if ruleno = { P T }13 then addpara(dict.R,":",R_1,place)
 else if ruleno = { P P, T }14 then addpara(dict.R,":",R_3,place,R_1)
 else if ruleno = { P W:T }15 then addpara(dict.R,tokentext.R_1,R_3,place)
 else if ruleno = { P P, W:T }16 then addpara(dict.R,tokentext.R_3,R_5,place,R_1)
 else if ruleno = { P comment W:T }17 then addpara(dict.R,tokentext.R_2,R_4,place)
 else if ruleno = { P P, comment W:T }18 then addpara(dict.R,tokentext.R_4,R_6,place,R_1)
  else if ruleno = { E NM }19 then
   if mode.common /in "body text" then
 let f = lookupbysig(dict.R, text.R_1, empty:seq.mytype, common, place)
 bindinfo(dict.R, [ f], [ resulttype.f],"")
 else R_1
 else if ruleno = { E NM(L)}20 then unaryop(R, common, place, tokentext.R_1, R_3)
 else if ruleno = { E(E)}21 then R_2
 else if ruleno = { E if E then E else E }22 then ifexp(R, R_2, R_4, R_6, common, place)
 else if ruleno = { E if E then E else E fi }23 then
  ifexp(R, R_2, R_4, R_6, common, place)
 else if ruleno = { E E_E }24 then opaction(R, common, place)
 else if ruleno = { E-E }25 then unaryop(R, common, place, tokentext.R_1, R_2)
 else if ruleno = { E W.E }26 then unaryop(R, common, place, tokentext.R_1, R_3)
 else if ruleno = { E E * E }27 then opaction(R, common, place)
 else if ruleno = { E E-E }28 then opaction(R, common, place)
 else if ruleno = { E E = E }29 then opaction(R, common, place)
 else if ruleno = { E E > E }30 then opaction(R, common, place)
 else if ruleno = { E E ∧ E }31 then opaction(R, common, place)
 else if ruleno = { E E ∨ E }32 then opaction(R, common, place)
 else if ruleno = { L E }33 then R_1
 else if ruleno = { L L, E }34 then
  bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3,"")
 else if ruleno = { E [ L]}35 then
 let types = types.R_2
  assert for acc = true, @e = types do acc ∧ types_1 = @e /for(acc)report errormessage("types do not match in build", common, place)
  bindinfo(dict.R, code.R_2 + Sequence(types_1, length.types), [ seqof.types_1],"")
 else if ruleno = { A W = E }36 then
 let name = tokentext.R_1
  assert isempty.lookupbysig(dict.R, name)report errormessage("duplicate symbol:" + name, common, place)
  let newdict = dict.R + Local(name_1,(types.R_3)_1, cardinality.dict.R)
  bindinfo(newdict, code.R_3 + Define(name_1, cardinality.dict.R), types.R_3, name)
 else if ruleno = { E let A E }37 then
 let letsym = if mode.common ∈ "text"then
  [ symbol(internalmod,"let", typeint, first.types.R_3, first.types.R_3)]
  else empty:seq.symbol
  bindinfo(dict.R_1, code.R_2 + code.R_3+ letsym, types.R_3,"")
 else if ruleno = { E assert E report D E }38 then
  assert(types.R_2)_1 = typeboolean report errormessage("condition in assert must be boolean in:", common, place)
  assert(types.R_4)_1 = seqof.typeword report errormessage("report in assert must be seq of word in:", common, place)
   let typ=(types.R_5)_1
   let assertsym=symbol(builtinmod.typ,"assert", seqof.typeword, typ)
   bindinfo(dict.R, [ Start.(types.R_5)_1] + code.R_2 + Br2(1, 2)
    + code.R_5
    + Exit
    + code.R_4
    + assertsym
    + Exit
    + if mode.common ∈ "text"then symbol(internalmod,"report", typeint)else EndBlock, types.R_5,"")
 else if ruleno = { E I }39 then bindlit.R
 else if ruleno = { E I.I }40 then
  bindinfo(dict.R
  , [ Words(tokentext.R_1 + "." + tokentext.R_3), symbol(moduleref."UTF8","makereal", seqof.typeword, typereal)]
  , [ typereal]
  ,""
  )
 else if ruleno = { T W }41 then R_1
 else if ruleno = { T W.T }42 then
  bindinfo(dict.R,empty:seq.symbol, empty:seq.mytype, tokentext.R_1 + "." + tokentext.R_3)
 else if ruleno = { E $wordlist }43 then
 let s = tokentext.R_1
  bindinfo(dict.R
  , [ Words.if mode.common ∈ "text"then s else subseq(s, 2, length.s - 1)]
  , [ seqof.typeword]
  ,""
  )
 else if ruleno = { E comment E }44 then
  if mode.common ∈ "text"then
   bindinfo(dict.R, [ Words.tokentext.R_1] + code.R_2
   + symbol(internalmod,"{", seqof.typeword, first.types.R_2, first.types.R_2), types.R_2,"")
    else  R_2
 else if ruleno = { NM W }45 then R_1
 else if ruleno = { NM W:T }46 then
  bindinfo(dict.R,empty:seq.symbol, empty:seq.mytype, tokentext.R_1 + tokentext.R_3)
 else if ruleno = { F1 W = E }47 then
 let name = tokentext.R_1
  assert isempty.lookupbysig( dict.R, name )report errormessage("duplicate symbol:" + name, common, place)
  bindinfo(dict.R_1, code.R_3, types.R_3, name)
 else if ruleno = { F1 F1, W = E }48 then
 let name = tokentext.R_3
  assert isempty.lookupbysig(dict.R, name)report errormessage("duplicate symbol:" + name, common, place)
  bindinfo(dict.R, code.R_1 + code.R_5, types.R_1 + types.R_5, tokentext.R_1 + tokentext.R_3)
 else if ruleno = { F2 F1 }49 then forlocaldeclare(R_1, common, place)
 else if ruleno = { E for F2 do E end(E)}50 then
  forbody(dict.R_1, R_2, R_4, R_1, R_7, common, place)
 else if ruleno = { E for F2 while E do E end(E)}51 then
  forbody(dict.R_1, R_2, R_6, R_4, R_9, common, place)
 else
  assert ruleno = { D E }52 report"invalid rule number" + toword.ruleno
   R_1

function forlocaldeclare(a:bindinfo, input:commoninfo, place:int)bindinfo
let seqtype = last.types.a
 assert isseq.seqtype report errormessage("final expression in for list must be a sequence but it is of type:" + print.seqtype, input, place)
  assert length.types.a ≠ 1 report errormessage("For must have at least one accumulator" + print.length.types.a, input, place)
  let elename = [ last.tokentext.a]
  let elesym = symbol(moduleref("$for", parameter.seqtype), elename, empty:seq.mytype, parameter.seqtype)
  let dict1 = if length.types.a > 1 then
   { keep track so right next is used in nested fors }
   let basetype = typebase.place
   let resultsym = symbol(moduleref("$for",basetype),"next", types.a >> 1, basetype)
   let nestingsym = symbol(moduleref("$for",basetype),"for", empty:seq.mytype, basetype)
   let oldnesting = lookupbysig(dict.a,"for")
   if isempty.oldnesting then dict.a else dict.a - oldnesting /if + resultsym + nestingsym
  else dict.a
  let accumulators = for acc = empty:seq.symbol, i = 1, name = tokentext.a >> 1 do
   next(acc + symbol(moduleref("$for",(types.a)_i), [ name], empty:seq.mytype,(types.a)_i), i + 1)
  /for(acc)
  bindinfo(dict1 ∪ asset(accumulators + elesym), code.a + accumulators + elesym, types.a, elename)

function forbody(dict:symboldict, vars:bindinfo, forbody:bindinfo, exitexp:bindinfo, endexp:bindinfo, input:commoninfo, place:int)bindinfo
let checktypes = if tokentext.exitexp = "for" ∨ first.types.exitexp = typeboolean then
 { while type is OK. now check body type }
 if length.types.vars > 2 then
  if resulttype.lookupbysig(dict.vars,"for")_1 = (types.forbody)_1 then""
  else"incorrect body type:" + print.(types.forbody)_1
 else if first.types.vars = first.types.forbody then""
 else
 "Type of body expression" + print.first.types.vars + "must match accumaltor type"
  + print.first.types.forbody
else"while expresssion type must be boolean"
assert isempty.checktypes report errormessage(checktypes, input, place)
 let resulttype = first.types.endexp
 let sym = symbol(moduleref("builtin", typeint),"forexp", types.vars + types.vars >> 1 + parameter.last.types.vars + (types.forbody)_1
 + typeboolean
 + resulttype, resulttype)
  let newcode = code.vars + code.forbody
  + if tokentext.exitexp = "for"then [ Littrue]else code.exitexp /if
  + code.endexp
  + sym
   bindinfo(dict, newcode, [ resulttype],"") 