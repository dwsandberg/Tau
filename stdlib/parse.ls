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

Function funcparametertypes(t:bindinfo)seq.mytype @(+, parameter, empty:seq.mytype, subseq(types.t, 3, length.types.t))

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
let b=parse(bindinfo(empty:set.symbol,empty:seq.symbol, empty:seq.mytype,""),
' function a int  f("hi") '
 )"OK"

Function parse(b:bindinfo, input:seq.word)bindinfo
 // let a = if length.cachevalue = 0 then let discard = encode(sortedlextable:bindinfo){data.(cachevalue)_1 } else data.(cachevalue)_1 //
 let a = sortedlextable:bindinfo
  // assert isempty.dict.b report @(+, print,"", toseq.dict.b)+ stacktrace //
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
   let newcode=  
        [Fref.dcrt_1,Fref.dcws_1, Fref.last.code.exp,Lit.0,Lit.nopara]
        + subseq(code.exp, 1, length.code.exp - 1)
     +[newsymbol("kindrecord",mytype."T builtin",[typeint,typeint]+ paratypes.last.code.exp,typeptr)
      ,symbol("createthread(int,int,int,ptr)","builtin","ptr")]
   bindinfo(dict.R, newcode, [  typeprocess+rt],"")
 else
  let f = lookupbysig(dict.R, op, types.exp, input, place.R)
   bindinfo(dict.R, code.exp + f, [ resulttype.f],"")

function placehold(initseq:bindinfo, accsym:bindinfo, initacc:bindinfo, args:bindinfo, input:seq.token.bindinfo, place:int)bindinfo
    let seqtype=first.types.initseq
    let resulttype=first.types.initacc 
    let s1=newsymbol("@e",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,parameter.seqtype)
    let s2=newsymbol("@i",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,typeint)
    let xx=typerep.seqtype+typerep.resulttype+"/"+typerep.first.types.initacc+
     typerep.first.types.args+text.accsym
     let op = lookupbysig(dict.initseq, text.accsym , types.initacc+types.args, input, place)
     let paratypes=paratypes.op
      assert abstracttype.seqtype in "seq" report errormessage(" first term of apply must be sequence",input,place)
      assert length.paratypes > 1 &and  paratypes_1 = resulttype
      report "First parameter must be the same as the result type in apply"
           let z=if op=symbol("∧(boolean, boolean)","stdlib","boolean")
        then symbol("∧(bits, bits)","bits","bits") 
        else if op=symbol("∨(boolean, boolean)","stdlib","boolean")
        then symbol("∨(bits, bits)","bits","bits") 
        else op
     // assert false report  "CHK"+    print.z //  
  let newway=  code.initseq+Define."@seq"+   Local.first."@seq"+ code.initacc 
    +  Local.first."@seq"
    +newsymbol("@acc",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,resulttype)
    +code.args+op
     +Fref.pseqidxsym.parameter.seqtype 
     +newsymbol("apply3",abstracttype("builtin"_1,resulttype )
           ,[ seqtype,resulttype,seqtype,resulttype ,typeint],resulttype )
   //   assert false report "place holdx"+@(+,print,"",newway)    //
 bindinfo(dict.initseq-s1 -s2,     newway , [resulttype.op],"")
 
  assert false report "place hold"
 initseq


function apply(orgdict:set.symbol,term1:bindinfo, term2:bindinfo,   input:seq.token.bindinfo, place:int)bindinfo
    let seqtype=(types.term1)_1
      let resulttype=(types.term2)_1
      let op=last.code.term2
      let z=if op=symbol("∧(boolean, boolean)","stdlib","boolean")
        then symbol("∧(bits, bits)","bits","bits") 
        else if op=symbol("∨(boolean, boolean)","stdlib","boolean")
        then symbol("∨(bits, bits)","bits","bits") 
        else op
     // assert false report  "CHK"+    print.z //  
      let code2= (code.term2 >> 1 )+z
      let paratypes=paratypes.op
     assert length.paratypes > 1 &and  paratypes_1 = resulttype
      report "Type first parameter must be the same as the result type in apply"
      let i=backparse(  code2 ,length.code2-1,1)
     // assert false report "XXXX"+toword.i+@(+,print,"",code.term2) //
      let newway=  code.term1+Define."@seq"+ subseq(code2,1,i) 
      +newsymbol("@acc",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,resulttype)
      +subseq(code2,i+1,length.code2)
       +[Fref.pseqidxsym.parameter.seqtype  ,newsymbol("apply3",abstracttype("builtin"_1,resulttype )
           ,[ seqtype,resulttype,resulttype ,typeint],resulttype )] 
    //  assert false report "place holdx"+@(+,print,"",newway)  //  
 bindinfo(orgdict,     newway , [resulttype.op],"")
 


function backparse(s:seq.symbol,i:int,noterms:int) int
 if noterms=0 then i
 else 
 let sym=s_i
 let  nopara=nopara.sym
 if nopara=0 then backparse(s,i-1,noterms-1)
 else 
    let a=backparse(s,i-1,nopara)
     backparse(s,a,noterms-1)
 
  a b +
  
  "a b +",2,1 
      0,1,0
 
   a c d + +  , 4,1
                3 2

function declareapplyvars( term1:bindinfo, input:seq.token.bindinfo, place:int)bindinfo
let seqtype=(types.term1)_1
 let newdict = dict.term1 + newsymbol("@e",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,parameter.seqtype)
+ newsymbol("@i",abstracttype("builtin"_1,parameter.seqtype),empty:seq.mytype,typeint)
bindinfo(newdict, code.term1 , types.term1, tokentext.term1)


function apply(term1:bindinfo, term2:bindinfo, term3:bindinfo, term4:bindinfo, input:seq.token.bindinfo, place:int)bindinfo
 let dict = dict.term1
  assert abstracttype.(types.term4)_1 = "seq"_1 report errormessage("last term of apply must be seq", input, place)
  let sym2types = types.term2 + [ parameter.(types.term4)_1]
  let sym2 = lookupbysig(dict, text.term2, sym2types, input, place)
  let sym1types = types.term1 + types.term3 + [ resulttype.sym2]
  let sym1 = lookupbysig(dict, text.term1, sym1types, input, place)
   assert(types.term3)_1 = resulttype.sym1 report errormessage("term3 not same as init" + print.(types.term3)_1 + print.resulttype.sym1, input, place)
   let pseqtype = typepseq+parameter.(types.term4)_1   
   let idx = pseqidxsym.parameter.(types.term4)_1
   let x = lookupbysig(dict, name.idx, paratypes.idx, input, place)
   let seqtype=(types.term4)_1
     let elementtype=parameter.seqtype
     let looptypes= types.term1+resulttype.sym1+types.term2  +seqtype
     let loopsym=Loopblock(@(seperator.",",typerep,"",looptypes)+",int)")
     let newway= code.term1 +  code.term2+ code.term3 + code.term4
       +[Lit(place * 100 ),loopsym] 
       + @(+, Local, empty:seq.symbol,arithseq(length.types.term1, 1, place * 100))
       +   newsymbol("applyaccumalator",abstracttype("builtin"_1,resulttype.sym1),empty:seq.mytype,resulttype.sym1)
       + @(+, Local, empty:seq.symbol,arithseq(length.types.term2, 1, place * 100+length.types.term1))
       + [  newsymbol("applyelement",abstracttype("builtin"_1,elementtype),empty:seq.mytype,elementtype)
         , sym2,sym1,Exit,Block( resulttype.sym1,2),Fref.idx
         ,newsymbol("apply2",abstracttype("builtin"_1,resulttype.sym1)
           ,[resulttype.sym1,typeint],resulttype.sym1)] 
   bindinfo(dict,     newway , types.term3,"")
   
  
function addparameter(orgsize:int, input:seq.token.bindinfo, place:int, dict:set.symbol, m:mytype)set.symbol
 assert isempty.lookup(dict, [ abstracttype.m], empty:seq.mytype) ∨ abstracttype.m = ":"_1 report errormessage("duplciate symbol:" + abstracttype.m, input, place)
 let parano = cardinality.dict - orgsize + 1
  dict + Parameter(abstracttype.m, parameter.m, parano)

function lookupbysig(dict:set.symbol, name:seq.word, paratypes:seq.mytype, input:seq.token.bindinfo, place:int)symbol
 let f = lookup(dict, name, paratypes)
  assert not.isempty.f report errormessage("cannot find 1" + name + "(" + @(seperator(","), print,"", paratypes)
  + ")", input, place)
   // + @(+, print,"", toseq.dict)//
   assert cardinality.f = 1 report errormessage("found more that one" + @(+, print,"", toseq.f), input, place)
    f_1

/function backoffcomment(s:seq.token.bindinfo, match:word, i:int)seq.token.bindinfo if(text(s_i))_1 = match then subseq(s, 1, i-1)else backoffcomment(s, match, i-1)

function createfunc(R:reduction.bindinfo, input:seq.token.bindinfo, funcname:seq.word, paralist:seq.mytype, functypebind:bindinfo, exp:bindinfo)bindinfo
 let functype = gettype.functypebind
  assert functype = (types.exp)_1 ∨ (types.exp)_1 in [ mytype."internal1"]report errormessage("function type of" + print.functype + "does not match expression type" + print.(types.exp)_1, input, place.R)
   bindinfo(dict.R, code.exp, [ mytype."unused", functype] + paralist, funcname)
   


function isdefined(R:reduction.bindinfo, input:seq.token.bindinfo, type:mytype)bindinfo
 let dict = dict.R
  if cardinality.dict < 25 ∨ type in [mytype."T",typeint,mytype."real"]
  ∨  isabstract.type then
  bindinfo(dict, empty:seq.symbol, [type],"")
  else
   let a = lookup(dict,"type:" + print.type,  [type])
    assert cardinality.a = 1  report errormessage("parameter type" + print.type + "is undefined in", // + @(+, print,"", toseq.dict), // input, place.R)
     bindinfo(dict, empty:seq.symbol, [ type],"")


function gettype(b:bindinfo)mytype (types.b)_1


function dict(r:reduction.bindinfo)set.symbol dict.last.r

Function action(ruleno:int, input:seq.token.bindinfo, R:reduction.bindinfo)bindinfo
if ruleno = // G F # // 1 then R_1 else 
if ruleno = // F W NM(FP)T E // 2 then createfunc(R, input, tokentext.R_2, types.R_4, R_6, R_7)else 
if ruleno = // F W N(FP)T E // 3 then createfunc(R, input, tokentext.R_2, types.R_4, R_6, R_7)else 
if ruleno = // F W NM T E // 4 then createfunc(R, input, tokentext.R_2, empty:seq.mytype, R_3, R_4)else 
if ruleno = // F W NM is W P // 5 then assert(tokentext.R_4)_1 in"record sequence"report errormessage("Expected record or sequence after is in type definition got:"+ tokentext.R_4, input, place.R)bindinfo(dict.R, empty:seq.symbol, types.R_5, tokentext.R_4 + tokentext.R_2)else 
if ruleno = // F T // 6 then R_1 else 
if ruleno = // FP P // 7 then bindinfo(@(addparameter(cardinality.dict.R, input, place.R), identity, dict.R, types.R_1), empty:seq.symbol, types.R_1,"")else 
if ruleno = // P T // 8 then bindinfo(dict.R, empty:seq.symbol, [ abstracttype(":"_1, gettype.R_1)],"")else 
if ruleno = // P P, T // 9 then bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ abstracttype(":"_1, gettype.R_3)],"")else 
if ruleno = // P W:T // 10 then bindinfo(dict.R, empty:seq.symbol, [ abstracttype((tokentext.R_1)_1, gettype.R_3)],"")else 
if ruleno = // P P, W:T // 11 then bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ abstracttype((tokentext.R_3)_1, gettype.R_5)],"")else 
if ruleno = // P comment W:T // 12 then bindinfo(dict.R, empty:seq.symbol, [ abstracttype((tokentext.R_2)_1, gettype.R_4)],"")else 
if ruleno = // P P, comment W:T // 13 then bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ abstracttype((tokentext.R_4)_1, gettype.R_6)],"")else 
if ruleno = // E NM // 14 then 
 let id = tokentext.R_1
let f = lookupbysig(dict.R, id, empty:seq.mytype, input, place.R)bindinfo(dict.R, [ f], [ resulttype.f],"")else 
if ruleno = // E NM(L)// 15 then unaryop(R, input, tokentext.R_1, R_3)else 
if ruleno = // E(E)// 16 then R_2 else 
if ruleno = // E { E } // 17 then R_2 else 
if ruleno = // E if E then E else E // 18 then 
let thenpart = R_4 assert(types.R_2)_1 = mytype."boolean"report errormessage("cond of if must be boolean", input, place.R)assert types.R_4 = types.R_6 report errormessage("then and else types are different", input, place.R) 
let newcode = code.R_2 + [ Lit.2, Lit.3, Br]+ code.R_4 + Exit + code.R_6 + [ Exit, Block((types.R_4)_1, 3)]bindinfo(dict.R, newcode, types.thenpart,"")else 
if ruleno = // E unused // 19 then  R_1 else 
if ruleno = // E E_E // 20 then opaction(R, input)else 
if ruleno = // E-E // 21 then unaryop(R, input, tokentext.R_1, R_2)else 
if ruleno = // E W.E // 22 then unaryop(R, input, tokentext.R_1, R_3)else 
if ruleno = // E E * E // 23 then opaction(R, input)else 
if ruleno = // E E-E // 24 then opaction(R, input)else 
if ruleno = // E E = E // 25 then opaction(R, input)else 
if ruleno = // E E > E // 26 then opaction(R, input)else 
if ruleno = // E E ∧ E // 27 then opaction(R, input)else 
if ruleno = // E E ∨ E // 28 then opaction(R, input)else 
if ruleno = // L E // 29 then R_1 else 
if ruleno = // L L, E // 30 then bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3,"")else 
if ruleno = // E [ L]// 31 then 
let types = types.R_2 assert @(∧, =.types_1, true, types)report errormessage("types do not match in build", input, place.R)bindinfo(dict.R, [ Lit.0, Lit.length.types]+ code.R_2 + newsymbol("kindrecord", mytype."T builtin", [ typeint, typeint]+ types, typeptr), [ typeseq + types_1],"")else 
if ruleno = // A let W = E // 32 then 
 let e = R_4
let name = tokentext.R_2 assert isempty.lookup(dict.R, name, empty:seq.mytype)report errormessage("duplicate symbol:"+ name, input, place.R) 
let newdict = dict.R + Local(name,(types.e)_1)bindinfo(newdict, code.e + Define.name, types.e, tokentext.R_2)else 
if ruleno = // E A E // 33 then 
 let name = tokentext.R_1
let f = lookup(dict.R, name, empty:seq.mytype)assert not.isempty.f report"internal error/could not find local symbol to delete from dict with name"+ name bindinfo(dict.R_1-f_1, code.R_1 + code.R_2, // +"SET"+ name, // types.R_2,"")else 
if ruleno = // E assert E report E E // 34 then assert(types.R_2)_1 = mytype."boolean"report errormessage("condition in assert must be boolean in:", input, place.R)assert(types.R_4)_1 = mytype."word seq"report errormessage("report in assert must be seq of word in:", input, place.R) 
let newcode = code.R_2 + [ Lit.2, Lit.3, Br]+ code.R_5 + Exit + code.R_4 + symbol("assert(word seq)", typerep.(types.R_5)_1 +"builtin", typerep.(types.R_5)_1)+ Exit + Block((types.R_5)_1, 3)bindinfo(dict.R, newcode, types.R_5,"")else 
if ruleno = // E I // 35 then bindinfo(dict.R, [ Lit.toint.(tokentext.R_1)_1], [ typeint],"")else 
if ruleno = // E I.I // 36 then bindinfo(dict.R, [ Words(tokentext.R_1 +"."+ tokentext.R_3), symbol("makereal(word seq)","UTF8","real")], [ mytype."real"],"")else 
if ruleno = // T W // 37 then isdefined(R, input, mytype.tokentext.R_1)else 
if ruleno = // T W.T // 38 then isdefined(R, input, abstracttype((tokentext.R_1)_1,(types.R_3)_1))else 
if ruleno = // E $wordlist // 39 then 
let s = tokentext.R_1 bindinfo(dict.R, [ Words.subseq(s, 2, length.s-1)], [ mytype."word seq"],"")else 
if ruleno = // E comment E // 40 then R_2 else 
if ruleno = // N_// 41 then R_1 else 
if ruleno = // N-// 42 then R_1 else 
if ruleno = // N = // 43 then R_1 else 
if ruleno = // N > // 44 then R_1 else 
if ruleno = // N * // 45 then R_1 else 
if ruleno = // N ∧ // 46 then R_1 else 
if ruleno = // N ∨ // 47 then R_1 else 
if ruleno = // K W.E // 48 then bindinfo(dict.R, code.R_3, types.R_3, tokentext.R_1)else 
if ruleno = // K N.E // 49 then bindinfo(dict.R, code.R_3, types.R_3, tokentext.R_1)else 
if ruleno = // K N // 50 then  R_1 else 
if ruleno = // K NM(L)// 51 then bindinfo(dict.R, code.R_3, types.R_3, tokentext.R_1)else 
if ruleno = // K NM // 52 then R_1 else 
if ruleno = // NM W // 53 then R_1 else 
if ruleno = // NM W:T // 54 then bindinfo(dict.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1 +":"+ print.(types.R_3)_1)else 
if ruleno = // E @(K, K, E, E)// 55 then apply(R_3, R_5, R_7, R_9, input, place.R)else 
if ruleno = // D E @@ // 56 then declareapplyvars(R_1, input, place.R)else 
if ruleno = // E D NM(E, L)// 57 then placehold(R_1, R_2, R_4, R_6, input, place.R)else 
assert ruleno = // E D N(E, L)// 58 report"invalid rule number"+ toword.ruleno 
placehold(R_1, R_2, R_4, R_6, input, place.R)

