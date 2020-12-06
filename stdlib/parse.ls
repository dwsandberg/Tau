Module parse

use parsersupport.bindinfo

use encoding.seq.token.bindinfo

use seq.seq.token.bindinfo

use seq.token.bindinfo

use format

use seq.int

use seq.seq.mytype

use seq.mytype

use stdlib

use seq.seq.symbol

use seq.symbol

use set.symbol

use symbol

use set.word

Export getheader(s:seq.word)seq.word

Export type:bindinfo

type bindinfo is record dict:set.symbol, code:seq.symbol, types:seq.mytype, tokentext:seq.word

Export dict(bindinfo)set.symbol

Function parsedcode(b:bindinfo)seq.symbol code.b

Export types(bindinfo)seq.mytype

Function funcparametertypes(t:bindinfo)seq.mytype subseq(types.t, 3, length.types.t) @@ +(empty:seq.mytype, parameter.@e)

Function funcname(t:bindinfo)seq.word text.t

Function funcreturntype(t:bindinfo)mytype(types.t)_2

/function expect(stateno:int)seq.word let l = @(+, kk(stateno),"", arithseq(length.tokenlist, 1, 1))toseq(asset.l-asset."-=_^∧ ∨ *")

/function kk(stateno:int, token:int)seq.word if 0 ≠ actiontable_(length.tokenlist * stateno + token)then [ tokenlist_token]else empty:seq.word

function errormessage(message:seq.word, input:seq.word, place:int)seq.word message + prettynoparse.subseq(input, 1, place)

Function parse(dict:set.symbol, input:seq.word)bindinfo parse(bindinfo(dict, empty:seq.symbol, empty:seq.mytype,""), input)

/ Function cachevalue seq.encodingpair.seq.token.bindinfo encoding:seq.encodingpair.seq.token.bindinfo

/ use seq.encodingpair.seq.token.bindinfo

/ use encoding.seq.token.bindinfo

Function testparse seq.word  
let b = parse(bindinfo(empty:set.symbol, empty:seq.symbol, empty:seq.mytype,""), 
' function a(b:seq.int) int  b @ +(0,@i) ')
 "OK"

Function parse(b:bindinfo, input:seq.word)bindinfo
 // let a = if length.cachevalue = 0 then let discard = encode(sortedlextable:bindinfo){data.(cachevalue)_1 } else data.(cachevalue)_1 //
 let a = sortedlextable:bindinfo
  parse:bindinfo(b, a, input)

function forward(stk:bindinfo, token:bindinfo)bindinfo bindinfo(dict.stk, empty:seq.symbol, empty:seq.mytype, tokentext.token)

function attribute:bindinfo(w:seq.word)bindinfo bindinfo(empty:set.symbol, empty:seq.symbol, empty:seq.mytype, w)

function text(b:bindinfo)seq.word tokentext.b

function hash(l:seq.token.bindinfo)int length.l

function assignencoding(l:int, a:seq.token.bindinfo)int assignrandom(l, a)

function opaction(R:reduction.bindinfo, input:seq.token.bindinfo)bindinfo
 let op = tokentext.R_2
 let dict = dict.R_1
 let types = types.R_1 + types.R_3
 let f = lookupbysig(dict, [op_1], types, input, place.R)
  bindinfo(dict, code.R_1 + code.R_3 + f, [ resulttype.f],"")

function unaryop(R:reduction.bindinfo, input:seq.token.bindinfo, op:seq.word, exp:bindinfo)bindinfo
 if op_1 = "process"_1 then
 let nopara = nopara.last.code.exp
 let rt =(types.exp)_1
  let dcrt  = deepcopysym(dict.R,rt)
  assert cardinality.dcrt = 1  report errormessage("parameter type" + print.rt+ "is undefined in",  input, place.R)
 let dcws = deepcopysym(dict.R,mytype."word seq")
  assert cardinality.dcws=1 report errormessage("type word seq is require for process in" ,  input, place.R)
    let newcode = [ Fref.dcrt_1, Fref.dcws_1, Fref.last.code.exp, Lit.0, Lit.nopara]
        + subseq(code.exp, 1, length.code.exp - 1)
    + [ newsymbol("kindrecord", mytype."T builtin", [ typeint, typeint] + paratypes.last.code.exp, typeptr), symbol("createthread(int, int, int, ptr)","builtin","ptr")]
   bindinfo(dict.R, newcode, [  typeprocess+rt],"")
 else
  let f = lookupbysig(dict.R, op, types.exp, input, place.R)
   bindinfo(dict.R, code.exp + f, [ resulttype.f],"")

function applypart1( initseq:bindinfo,  name:bindinfo, initacc:bindinfo ,input:seq.token.bindinfo, place:int)bindinfo
   let seqtype=(types.initseq)_1
   let resulttype=(types.initacc)_1
    let s1=newsymbol("@e",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,parameter.seqtype)
    let s2=newsymbol("@i",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,typeint)
 let newdict = dict.initseq + s1 + s2
 let newcode = code.initseq+Define."@seq"+   Local.first."@seq"+ code.initacc 
    +  Local.first."@seq"
    +newsymbol("@acc",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,resulttype)
  bindinfo(newdict,newcode,types.initseq+types.initacc,tokentext.name)
  
function applypart2( part1:bindinfo,args:bindinfo,input:seq.token.bindinfo, place:int) bindinfo
  let seqtype=(types.part1)_1
   let resulttype=(types.part1)_2
     let opname=tokentext.part1
      let s1=newsymbol("@e",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,parameter.seqtype)
    let s2=newsymbol("@i",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,typeint)
        let op = lookupbysig(dict.part1,  opname , [resulttype]+types.args, input, place)
       let paratypes=paratypes.op
      assert abstracttype.seqtype in "seq" report errormessage(" first term of apply must be sequence",input,place)
   assert length.paratypes > 1 ∧ paratypes_1 = resulttype report"First parameter must be the same as the result type in apply"
   let z = if op = symbol("∧(boolean, boolean)","stdlib","boolean")then
   symbol("∧(bits, bits)","bits","bits")
   else if op = symbol("∨(boolean, boolean)","stdlib","boolean")then
   symbol("∨(bits, bits)","bits","bits")
        else op
 let newcode=code.part1+code.args
    + op
     +Fref.pseqidxsym.parameter.seqtype 
    + newsymbol("apply3", abstracttype("builtin"_1, resulttype), [ seqtype, resulttype, seqtype, resulttype, typeint], resulttype)
    bindinfo(dict.args-s1 -s2,     newcode, [resulttype.op],"")

function addparameter(dict:set.symbol,orgsize:int, input:seq.token.bindinfo, place:int,  m:mytype)set.symbol
 assert isempty.lookup(dict, [ abstracttype.m], empty:seq.mytype) ∨ abstracttype.m = ":"_1 report errormessage("duplciate symbol:" + abstracttype.m, input, place)
 let parano = cardinality.dict - orgsize + 1
  dict + Parameter(abstracttype.m, parameter.m, parano)

function lookupbysig(dict:set.symbol, name:seq.word, paratypes:seq.mytype, input:seq.token.bindinfo, place:int)symbol
 let f = lookup(dict, name, paratypes)
  assert not.isempty.f report errormessage("cannot find 1" + name + "(" + paratypes @@ list("",",", print.@e)
  + ")", input, place)
   // + @(+, print,"", toseq.dict)//
   assert cardinality.f = 1 report errormessage("found more that one" + toseq.f @@ +("", print.@e), input, place)
    f_1

function createfunc(R:reduction.bindinfo, input:seq.token.bindinfo, funcname:seq.word, paralist:seq.mytype, functypebind:bindinfo, exp:bindinfo)bindinfo
 let functype = gettype.functypebind
  assert functype = (types.exp)_1 ∨ (types.exp)_1 in [ mytype."internal1"]report errormessage("function type of" + print.functype + "does not match expression type" + print.(types.exp)_1, input, place.R)
   bindinfo(dict.R, code.exp, [ mytype."unused", functype] + paralist, funcname)
   
function isdefined(R:reduction.bindinfo, input:seq.token.bindinfo, type:mytype)bindinfo
 let dict = dict.R
  if cardinality.dict < 25 ∨ type in [ mytype."T", typeint, mytype."real"] ∨ isabstract.type then
  bindinfo(dict, empty:seq.symbol, [type],"")
  else
   let a = lookup(dict,"type:" + print.type,  [type])
    assert cardinality.a = 1 report errormessage("parameter type" + print.type + "is undefined in",  input, place.R)
     bindinfo(dict, empty:seq.symbol, [ type],"")

function gettype(b:bindinfo)mytype (types.b)_1

function dict(r:reduction.bindinfo)set.symbol dict.last.r

function action(ruleno:int, input:seq.token.bindinfo, R:reduction.bindinfo)bindinfo 
 if ruleno = // G F # // 1 then R_1
else if ruleno = // F W NM(FP)T E // 2 then createfunc(R, input, tokentext.R_2, types.R_4, R_6, R_7) 
else if ruleno = // F W N(FP)T E // 3 then createfunc(R, input, tokentext.R_2, types.R_4, R_6, R_7) 
else if ruleno = // F W NM T E // 4 then createfunc(R, input, tokentext.R_2, empty:seq.mytype, R_3, R_4) 
 else if ruleno = // F W NM is W P // 5 then
assert(tokentext.R_4)_1 in"record sequence"report errormessage("Expected record or sequence after is in type definition got:"+ tokentext.R_4, input, place.R)bindinfo(dict.R, empty:seq.symbol, types.R_5, tokentext.R_4 + tokentext.R_2) 
 else if ruleno = // F T // 6 then R_1
else if ruleno = // FP P // 7 then bindinfo(types.R_1 @@ addparameter(dict.R, cardinality.dict.R, input, place.R, @e), empty:seq.symbol, types.R_1,"") 
else if ruleno = // P T // 8 then bindinfo(dict.R, empty:seq.symbol, [ abstracttype(":"_1, gettype.R_1)],"") 
else if ruleno = // P P, T // 9 then bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ abstracttype(":"_1, gettype.R_3)],"") 
else if ruleno = // P W:T // 10 then bindinfo(dict.R, empty:seq.symbol, [ abstracttype((tokentext.R_1)_1, gettype.R_3)],"") 
else if ruleno = // P P, W:T // 11 then bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ abstracttype((tokentext.R_3)_1, gettype.R_5)],"") 
else if ruleno = // P comment W:T // 12 then bindinfo(dict.R, empty:seq.symbol, [ abstracttype((tokentext.R_2)_1, gettype.R_4)],"") 
else if ruleno = // P P, comment W:T // 13 then bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ abstracttype((tokentext.R_4)_1, gettype.R_6)],"") 
 else if ruleno = // E NM // 14 then
 let id = tokentext.R_1
let f = lookupbysig(dict.R, id, empty:seq.mytype, input, place.R)bindinfo(dict.R, [ f], [ resulttype.f],"") 
 else if ruleno = // E NM(L)// 15 then unaryop(R, input, tokentext.R_1, R_3)
 else if ruleno = // E(E)// 16 then R_2
 else if ruleno = // E { E } // 17 then R_2
 else if ruleno = // E if E then E else E // 18 then
 let thenpart = R_4
   assert(types.R_2)_1 = mytype."boolean"report errormessage("cond of if must be boolean", input, place.R)
    assert types.R_4 = types.R_6 report errormessage("then and else types are different", input, place.R)
let newcode = code.R_2 + [ Lit.2, Lit.3, Br]+ code.R_4 + Exit + code.R_6 + [ Exit, Block((types.R_4)_1, 3)]bindinfo(dict.R, newcode, types.thenpart,"") 
else if ruleno = // E E_E // 19 then opaction(R, input) 
else if ruleno = // E-E // 20 then unaryop(R, input, tokentext.R_1, R_2) 
else if ruleno = // E W.E // 21 then unaryop(R, input, tokentext.R_1, R_3) 
else if ruleno = // E E * E // 22 then opaction(R, input) 
else if ruleno = // E E-E // 23 then opaction(R, input) 
else if ruleno = // E E = E // 24 then opaction(R, input) 
else if ruleno = // E E > E // 25 then opaction(R, input) 
else if ruleno = // E E ∧ E // 26 then opaction(R, input) 
else if ruleno = // E E ∨ E // 27 then opaction(R, input) 
else if ruleno = // L E // 28 then R_1 
else if ruleno = // L L, E // 29 then bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3,"") 
else if ruleno = // E [ L]// 30 then 
 let types = types.R_2
assert types @@ ∧(true,(types_1 = @e))report errormessage("types do not match in build", input, place.R)bindinfo(dict.R, [ Lit.0, Lit.length.types]+ code.R_2 + newsymbol("kindrecord", mytype."T builtin", [ typeint, typeint]+ types, typeptr), [ typeseq + types_1],"") 
else if ruleno = // A let W = E // 31 then 
 let e = R_4
  let name = tokentext.R_2
   assert isempty.lookup(dict.R, name, empty:seq.mytype)report errormessage("duplicate symbol:" + name, input, place.R)
let newdict = dict.R + Local(name,(types.e)_1)bindinfo(newdict, code.e + Define.name, types.e, tokentext.R_2) 
else if ruleno = // E A E // 32 then 
 let name = tokentext.R_1
  let f = lookup(dict.R, name, empty:seq.mytype)
assert not.isempty.f report"internal error/could not find local symbol to delete from dict with name"+ name bindinfo(dict.R_1-f_1, code.R_1 + code.R_2, // +"SET"+ name, // types.R_2,"") 
else if ruleno = // E assert E report E E // 33 then 
assert(types.R_2)_1 = mytype."boolean"report errormessage("condition in 
assert must be boolean in:", input, place.R) 
assert(types.R_4)_1 = mytype."word seq"report errormessage("report in 
assert must be seq of word in:", input, place.R) 
let newcode = code.R_2 + [ Lit.2, Lit.3, Br]+ code.R_5 + Exit + code.R_4 + symbol(" 
assert(word seq)", typerep.(types.R_5)_1 +"builtin", typerep.(types.R_5)_1)+ Exit + Block((types.R_5)_1, 3)bindinfo(dict.R, newcode, types.R_5,"") 
else if ruleno = // E I // 34 then bindinfo(dict.R, [ Lit.toint.(tokentext.R_1)_1], [ typeint],"") 
else if ruleno = // E I.I // 35 then bindinfo(dict.R, [ Words(tokentext.R_1 +"."+ tokentext.R_3), symbol("makereal(word seq)","UTF8","real")], [ mytype."real"],"") 
else if ruleno = // T W // 36 then isdefined(R, input, mytype.tokentext.R_1) 
else if ruleno = // T W.T // 37 then isdefined(R, input, abstracttype((tokentext.R_1)_1,(types.R_3)_1)) 
else if ruleno = // E $wordlist // 38 then 
let s = tokentext.R_1 bindinfo(dict.R, [ Words.subseq(s, 2, length.s-1)], [ mytype."word seq"],"") 
else if ruleno = // E comment E // 39 then R_2 
else if ruleno = // N_// 40 then R_1 
else if ruleno = // N-// 41 then R_1 
else if ruleno = // N = // 42 then R_1 
else if ruleno = // N > // 43 then R_1 
else if ruleno = // N * // 44 then R_1 
else if ruleno = // N ∧ // 45 then R_1 
else if ruleno = // N ∨ // 46 then R_1 
else if ruleno = // NM W // 47 then R_1 
else if ruleno = // NM W:T // 48 then bindinfo(dict.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1 +":"+ print.(types.R_3)_1) 
else if ruleno = // D E @@ NM(E, // 49 then applypart1(R_1, R_3,R_5, input, place.R) 
else if ruleno = // D E @@ N(E, // 50 then applypart1(R_1, R_3,R_5, input, place.R) 
else assert ruleno = // E D L)// 51 report"invalid rule number"+ toword.ruleno 
applypart2(R_1, R_2, input, place.R)
