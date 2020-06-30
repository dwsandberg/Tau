
Module parse

run mylib testnew

use parsersupport.bindinfo

use seq.seq.token.bindinfo

use seq.token.bindinfo

use format

use seq.int

use mangle

use blockseq.seq.mytype

use seq.seq.mytype

use seq.mytype

use stdlib

use blockseq.seq.symbol

use seq.seq.symbol

use seq.symbol

use set.symbol

use symbol

use funcsig

use seq.sig

use set.word


Function deepcopymangle(type:mytype)word 
mangle("deepcopy"_1, mytype(towords.type + "process"), [ type])


Function type:bindinfo internaltype export

type bindinfo is record dict:set.symbol, code:seq.word, types:seq.mytype, tokentext:seq.word


function dict(bindinfo)set.symbol export

Function codex(b:bindinfo)seq.word  code.b

function types(bindinfo)seq.mytype export

Function funcparametertypes(t:bindinfo)seq.mytype @(+, parameter, empty:seq.mytype, subseq(types.t, 3, length.types.t))

Function funcname(t:bindinfo)word(towords.(types.t)_1)_1

Function funcreturntype(t:bindinfo)mytype(types.t)_2

/function bindinfo(dict:set.symbol, code:seq.word, types:seq.mytype)bindinfo 
  bindinfo(dict,code,types,"")


/function expect(stateno:int)seq.word let l = @(+, kk(stateno),"", arithseq(length.tokenlist, 1, 1))toseq(asset.l - asset."- =_^∧ ∨ *")

/function kk(stateno:int, token:int)seq.word if 0 ≠ actiontable_(length.tokenlist * stateno + token)then [ tokenlist_token]else empty:seq.word

function errormessage(message:seq.word, input:seq.word, place:int)seq.word message + prettynoparse.subseq(input, 1, place)

Function parse(dict:set.symbol, input:seq.word)bindinfo parse(bindinfo(dict,"", empty:seq.mytype,""), input)

Function parse(b:bindinfo, input:seq.word)bindinfo
 let a = if length.orderadded.cachelex = 0 then
 let discard = encode(cachelex, sortedlextable:bindinfo)
   {(orderadded.cachelex)_1 }
 else(orderadded.cachelex)_1
  // let a = sortedlextable:bindinfo //
  // assert isempty.dict.b report @(+, print,"", toseq.dict.b)+ stacktrace //
  parse:bindinfo(b, a, input)

function forward(stk:bindinfo, token:bindinfo)bindinfo bindinfo(dict.stk, "", types.token,code.token)

function attribute:bindinfo(w:seq.word)bindinfo bindinfo(empty:set.symbol, w, empty:seq.mytype,w)

function text(b:bindinfo)seq.word tokentext.b

function hash(l:seq.token.bindinfo)int length.l

function assignencoding(l:int, a:seq.token.bindinfo) int assignrandom(l,a)


type cachelex is encoding seq.token.bindinfo

function opaction(R:reduction.bindinfo, input:seq.token.bindinfo)bindinfo
 let op =(text.R_2)_1
 let dict = dict.R_1
 let types = types.R_1 + types.R_3
 let f = lookupbysig(dict, op, types, input, place.R)
  bindinfo(dict, code.R_1 + code.R_3 + mangledname.f, [ resulttype.f],"")

function unaryop(R:reduction.bindinfo, input:seq.token.bindinfo, op:seq.word, exp:bindinfo)bindinfo
 if op_1 = "process"_1 then
 let nopara = manglednopara.last.code.exp
  let rt =(types.exp)_1
  let prt = mytype(towords.rt + "process")
  let newcode =  
    "FREF" + deepcopymangle.rt
  + "FREF"+ deepcopymangle.mytype."word seq"
  + "FREF" + last.code.exp
  + "LIT" + toword.nopara
  + subseq(code.exp, 1, length.code.exp - 1)
  + "RECORD"
  + toword(nopara + 4)
  +"process2ZbuiltinZint"
   bindinfo(dict.R, newcode, [ mytype(towords.rt + "process")],"")
 else
  let f = lookupbysig(dict.R, op_1, types.exp, input, place.R)
   bindinfo(dict.R, code.exp + mangledname.f, [ resulttype.f],"")

function apply(term1:bindinfo, term2:bindinfo, term3:bindinfo, term4:bindinfo, input:seq.token.bindinfo, place:int)bindinfo
 let dict = dict.term1
  assert abstracttype.(types.term4)_1 = "seq"_1 report errormessage("last term of apply must be seq", input, place)
  let sym2types = types.term2 + [ parameter.(types.term4)_1]
  let sym2 = lookupbysig(dict,(text.term2)_1, sym2types, input, place)
  let sym1types = types.term1 + types.term3 + [ resulttype.sym2]
  let sym1 = lookupbysig(dict,(text.term1)_1, sym1types, input, place)
   assert(types.term3)_1 = resulttype.sym1 report errormessage("term3 not same as init" + print.(types.term3)_1 + print.resulttype.sym1, input, place)
   let pseqtype = mytype(towords.parameter.(types.term4)_1 + "pseq"_1)
    let idx=  mangle("_"_1, mytype(towords.parameter.(types.term4)_1 + "seq"_1), [ pseqtype , mytype."int"])
   let x = lookupbysig(dict,"_"_1, [ pseqtype, mytype."int"], input, place)
    bindinfo(dict, code.term1 + code.term2 + code.term3
    + code.term4
    + "FREF"
    + mangledname.sym2
    + "FREF"
    + mangledname.sym1
    + "FREF"
    + idx
    + "APPLY"
    + toword(length.types.term1 + length.types.term2 + 5), types.term3,"")

function addparameter(orgsize:int, input:seq.token.bindinfo, place:int, dict:set.symbol, m:mytype)set.symbol
 assert isempty.lookup(dict, abstracttype.m, empty:seq.mytype) ∨ abstracttype.m = ":"_1 report errormessage("duplciate symbol:" + abstracttype.m, input, place)
 let parano = toword(cardinality.dict - orgsize + 1)
  dict + symbol(abstracttype.m, mytype.[ parano,"para"_1], empty:seq.mytype, parameter.m)

function lookupbysig(dict:set.symbol, name:word, paratypes:seq.mytype, input:seq.token.bindinfo, place:int)symbol
 let f = lookup(dict, name, paratypes)
  assert not.isempty.f report errormessage("cannot find 1" + name + "(" + @(seperator(","), print,"", paratypes)
  + ")", input, place)
   if cardinality.f > 1 ∧ name = merge."empty:seq.T"then
   // hack to get tools to compile // f_1
   else
    assert cardinality.f = 1 report errormessage("found more that one" + @(+, print,"", toseq.f), input, place)
     f_1

/function backoffcomment(s:seq.token.bindinfo, match:word, i:int)seq.token.bindinfo if(text(s_i))_1 = match then subseq(s, 1, i - 1)else backoffcomment(s, match, i - 1)

function createfunc(R:reduction.bindinfo, input:seq.token.bindinfo, funcname:seq.word, paralist:seq.mytype, functypebind:bindinfo, exp:bindinfo)bindinfo
 let functype = mytype.gettype.functypebind
  assert functype = (types.exp)_1 ∨ (types.exp)_1 in [ mytype."internal", mytype."internal1"]report errormessage("function type of" + print.functype + "does not match expression type" + print.(types.exp)_1, input, place.R)
  bindinfo(dict.R, code.exp, [ mytype.funcname, functype] + paralist,"")

function isdefined(R:reduction.bindinfo, input:seq.token.bindinfo, typ:seq.word)bindinfo
 let dict = dict.R
  if cardinality.dict < 25 ∨ typ in ["T","int"]
  ∨ subseq(typ, 1, 1) = "T"then
  bindinfo(dict, [ toword.place.R], [ mytype.typ],"")
  else
   let a = lookup(dict, merge("type:" + print.mytype.typ), empty:seq.mytype)
    assert cardinality.a = 1 ∨ print.mytype.typ in ["?"]report errormessage("parameter type" + print.mytype.typ + "is undefined in", // + @(+, print,"", toseq.dict), // input, place.R)
     bindinfo(dict, [ toword.place.R], [ mytype.typ],"")

function gettype(b:bindinfo)seq.word towords.(types.b)_1

function dict(r:reduction.bindinfo)set.symbol dict.last.r

/function printdict(b:bindinfo)

Function action(ruleno:int, input:seq.token.bindinfo, R:reduction.bindinfo)bindinfo
 // assert ruleno in [ 37, 5]report"rule"+ toword.ruleno //
 if ruleno = // G F # // 1 then R_1
 else if ruleno = // F W NM(FP)T E // 2 then
 createfunc(R, input, text.R_2, types.R_4, R_6, R_7)
 else if ruleno = // F W NM T E // 3 then
 createfunc(R, input, text.R_2, empty:seq.mytype, R_3, R_4)
 else if ruleno = // F W W is W P // 4 then
 assert(text.R_4)_1 in "record encoding sequence"report errormessage("Expected record encoding or sequence after is in type definition got:" + text.R_4, input, place.R)
   bindinfo(dict.R, text.R_4 + text.R_2 , types.R_5,text.R_4 + text.R_2)
 else if ruleno = // F T // 5 then R_1
 else if ruleno = // FP P // 6 then
 bindinfo(@(addparameter(cardinality.dict.R, input, place.R), identity, dict.R, types.R_1),"", types.R_1,"")
 else if ruleno = // P T // 7 then
 bindinfo(dict.R,"", [ mytype(gettype.R_1 + ":")],"")
 else if ruleno = // P P, T // 8 then
 bindinfo(dict.R,"", types.R_1 + [ mytype(gettype.R_3 + ":")],"")
 else if ruleno = // P W:T // 9 then
 bindinfo(dict.R, "", [ mytype(gettype.R_3 + text.R_1)],"")
 else if ruleno = // P P, W:T // 10 then
 bindinfo(dict.R, "", types.R_1 + [ mytype(gettype.R_5 + text.R_3)],"")
 else if ruleno = // P comment W:T // 11 then
 bindinfo(dict.R,"", [ mytype(gettype.R_4 + text.R_2)],"")
 else if ruleno = // P P, comment W:T // 12 then
 bindinfo(dict.R,"", types.R_1 + [ mytype(gettype.R_6 + text.R_4)],"")
 else if ruleno = // E NM // 13 then
 let id = text.R_1
  assert length.text.R_1  > 0 report "???? 13"
  let f = lookupbysig(dict.R, id_1, empty:seq.mytype, input, place.R)
   bindinfo(dict.R, [ mangledname.f], [ resulttype.f],"")
 else if ruleno = // E NM(L)// 14 then unaryop(R, input, text.R_1, R_3)
 else if ruleno = // E(E)// 15 then R_2
 else if ruleno = // E { E } // 16 then R_2
 else if ruleno = // E if E then E else E // 17 then
 let thenpart = R_4
   assert(types.R_2)_1 = mytype."boolean"report errormessage("cond of if must be boolean", input, place.R)
    assert types.R_4 = types.R_6 report errormessage("then and else types are different", input, place.R)
    let newcode = code.R_2 +"LIT 2 LIT 3 BR 3"+ code.R_4 +"EXITBLOCK 1" + code.R_6 +"EXITBLOCK 1 BLOCK 3"
     bindinfo(dict.R, newcode ,types.thenpart,"")
 else if ruleno = // E E^E // 18 then opaction(R, input)
 else if ruleno = // E E_E // 19 then opaction(R, input)
 else if ruleno = // E - E // 20 then unaryop(R, input, text.R_1, R_2)
 else if ruleno = // E W.E // 21 then unaryop(R, input, text.R_1, R_3)
 else if ruleno = // E N.E // 22 then unaryop(R, input, text.R_1, R_3)
 else if ruleno = // E E * E // 23 then opaction(R, input)
 else if ruleno = // E E - E // 24 then opaction(R, input)
 else if ruleno = // E E = E // 25 then opaction(R, input)
 else if ruleno = // E E > E // 26 then opaction(R, input)
 else if ruleno = // E E ∧ E // 27 then opaction(R, input)
 else if ruleno = // E E ∨ E // 28 then opaction(R, input)
 else if ruleno = // L E // 29 then R_1
 else  if ruleno = // L L, E // 30 then
 bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3,"")
 else if ruleno = // E [ L]// 31 then
 let types = types.R_2
   assert @(∧, =(types_1), true, types)report errormessage("types do not match in build", input, place.R)
    bindinfo(dict.R,"LIT 0 LIT" + toword.length.types + code.R_2 + "RECORD"
    + toword(length.types + 2), [ mytype(towords.types_1 + "seq")],"")
 else if ruleno = // A let W = E // 32 then
 let e = R_4
  let name =(text.R_2)_1
   assert isempty.lookup(dict.R, name, empty:seq.mytype)report errormessage("duplicate symbol:" + name, input, place.R)
   let newdict = dict.R + symbol(name, mytype."local", empty:seq.mytype,(types.e)_1)
    bindinfo(newdict, code.e + "DEFINE" + name, types.e,text.R_2)
 else if ruleno = // E A E // 33 then
   let name=(text.R_1)_1
  let f = lookup(dict.R, name, empty:seq.mytype)
   assert not.isempty.f report"internal error/could not find local symbol to delete from dict with name" + name
    bindinfo(dict.R_1 - f_1,  code.R_1 + code.R_2 ,// + "SET" + name, // types.R_2,"")
 else if ruleno = // E assert E report E E // 34 then
 assert(types.R_2)_1 = mytype."boolean"report errormessage("condition in assert must be boolean in:", input, place.R)
   assert(types.R_4)_1 = mytype."word seq"report errormessage("report in assert must be seq of word in:", input, place.R)
   let newcode= code.R_2 +"LIT 2 LIT 3 BR 3"+ code.R_5 +"EXITBLOCK 1" + code.R_4 +"assertZbuiltinZwordzseq EXITBLOCK 1 BLOCK 3"
    bindinfo(dict.R, newcode, types.R_5,"")
 else if ruleno = // E I // 35 then
 bindinfo(dict.R,"LIT" + text.R_1, [ mytype."int"],"")
 else if ruleno = // E I.I // 36 then
 bindinfo(dict.R,"WORDS 3" + text.R_1 + "." + text.R_3 + "makerealZUTF8Zwordzseq", [ mytype."real"],"")
 else if ruleno = // T W // 37 then isdefined(R, input, text.R_1)
 else if ruleno = // T W.T // 38 then
 isdefined(R, input, towords.(types.R_3)_1 + text.R_1)
 else if ruleno = // E $wordlist // 39 then
 let s = text.R_1
   bindinfo(dict.R,"WORDS" + toword(length.s - 2) + subseq(s, 2, length.s - 1), [ mytype."word seq"],"")
 else if ruleno = // E comment E // 40 then R_2
  else if ruleno = // N_// 41 then R_1
 else if ruleno = // N - // 42 then R_1
 else if ruleno = // N = // 43 then R_1
 else if ruleno = // N > // 44 then R_1
 else if ruleno = // N * // 45 then R_1
 else if ruleno = // N ∧ // 46 then R_1
 else if ruleno = // N ∨ // 47 then R_1
 else if ruleno = // K W.E // 48 then
 bindinfo(dict.R,   code.R_3, types.R_3,text.R_1)
 else if ruleno = // K N.E // 49 then
 bindinfo(dict.R,  code.R_3, types.R_3,text.R_1)
 else if ruleno = // K NM(L)// 50 then
 bindinfo(dict.R, code.R_3, types.R_3,text.R_1)
 else if ruleno = // K NM // 51 then  bindinfo(dict.R, "", types.R_1,text.R_1)
 else if ruleno = // NM W // 52 then assert length.text.R_1  > 0 report "???? 52"+code.R_1 R_1
 else if ruleno = // NM N // 53 then assert length.text.R_1  > 0 report "???? 53"  R_1
 else if ruleno = // NM W:T // 54 then
  let t=[ merge(text.R_1 + ":" + print.(types.R_3)_1)]
 bindinfo(dict.R, "", empty:seq.mytype,t)
 else
  assert ruleno = // E @(K, K, E, E)// 55 report"invalid rule number" + toword.ruleno
   apply(R_3, R_5, R_7, R_9, input, place.R)