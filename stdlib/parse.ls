Module parse

run newimp test1

use deepcopy.seq.lexaction

use libscope

use llvm

use seq.int

use seq.lexaction

use seq.mytype

use seq.stepresult

use seq.stkele

use seq.symbol

use set.symbol

use set.word

use stack.stkele

use stdlib

use symbol

use UTF8

use format

Function headdict set.symbol 
 let modulename = mytype."internal1"
  asset([ symbol("builtin"_1, modulename, [ mytype."internal1"], mytype."internal",""), 
  symbol("builtin"_1, modulename, [ mytype."word seq"], mytype."internal",""), 
  symbol("builtin"_1, modulename, empty:seq.mytype, mytype."internal",""), 
  symbol("STATE"_1, modulename, [ mytype."internal1"], mytype."internal1",""), 
  symbol(merge."sizeoftype:T", mytype."$typesize local", empty:seq.mytype, mytype."int","")]
  + @(+, builtinsym.modulename, empty:seq.symbol,"export unbound stub usemangle  FROMSEQ"))

function builtinsym(modname:mytype, name:word)symbol 
 symbol(name, modname, empty:seq.mytype, mytype."internal1","")
 
Function getheader(s:seq.word)seq.word 
 if length.s < 3 
  then s 
  else let endofname=
    if s_3 =":"_1 then consumetype(s, 5) else 3
    let startoftype = 
     if s_endofname ="("_1 
   then findindex(")"_1, s, endofname+1)+ 1 
   else endofname 
  let afterreturntype = consumetype(s, startoftype + 1)
  let aftercomments = consumecomment(s, afterreturntype)
  if aftercomments ≤ length.s ∧ s_aftercomments in"unbound export"
  then s 
  else if aftercomments ≤ length.s ∧ s_aftercomments ="builtin"_1 ∧ last.s ="usemangle"_1 
  then subseq(s, 1, aftercomments - 1)+"usemangle"
  else subseq(s, 1, aftercomments - 1)+"stub"

function consumetype(s:seq.word, i:int)int 
 if i > length.s 
  then i 
  else if s_i ="."_1 then consumetype(s, i + 2)else i

function consumecomment(s:seq.word, i:int)int 
 if i > length.s 
  then i 
  else if s_i ="//"_1 then consumecomment(s, findindex("//"_1, s, i + 1)+ 1)else i


type stepresult is record stk:stack.stkele, place:int, input:seq.word, tokenstate:int, string:seq.word

type bindinfo is record dict:set.symbol, code:seq.word, types:seq.mytype

function dict(bindinfo)set.symbol export

function code(bindinfo)seq.word export

function types(bindinfo)seq.mytype export

Function funcparametertypes(t:bindinfo)seq.mytype 
 // subseq(types.t, 3, length.types.t)// 
  @(+, parameter, empty:seq.mytype, subseq(types.t, 3, length.types.t))

Function parsedresult(t:bindinfo)seq.word 
 let argnames = @(+, abstracttype,"", subseq(types.t, 3, length.types.t))
  let y = [ funcname.t, toword.length.argnames]+ @(+, print,"", funcparametertypes.t)+ print.funcreturntype.t + argnames 
  {"parsedfunc"+ toword.length.y + y + code.t }

Function funcname(t:bindinfo)word towords(types(t)_1)_1

Function funcreturntype(t:bindinfo)mytype types(t)_2

function bindinfo(dict:set.symbol, code:seq.word, types:seq.mytype)bindinfo export

type stkele is record stateno:int, result:bindinfo

type lexaction is record w:word, tokenno:int, label:word

function expect(stateno:int)seq.word 
 let l = @(+, kk.stateno,"", arithseq(length.tokenlist, 1, 1))
  toseq(asset.l - asset."-=_^∧ ∨ *")

function kk(stateno:int, token:int)seq.word 
 if 0 ≠ actiontable_(length.tokenlist * stateno + token)then [ tokenlist_token]else empty:seq.word

use seq.char

function consumeinput(b:stepresult, next:word)stepresult 
 if tokenstate.b ≠ 0 
  then if tokenstate.b = stringtoken 
   then if next ="&quot"_1 
    then BB(stringtoken, bindinfo(dict.result.top.stk.b, string.b, [ mytype."int seq"]), stk.b, place.b, input.b)
    else // add to string // 
    stepresult(stk.b, place.b + 1, input.b, tokenstate.b, string.b + if next = merge.["&"_1,"quot"_1]then"&quot"_1 else next)
   else if next ="//"_1 
   then BB(commenttoken, bindinfo(dict.result.top.stk.b, string.b, [ mytype."int seq"]), stk.b, place.b, input.b)
   else // add to string // stepresult(stk.b, place.b + 1, input.b, tokenstate.b, string.b + next)
  else let act = let x = tointseq.decodeword.next 
   lextable_(1 +(if length.x > 2 
    then 23 *(x_1 + 2 * x_2)+ 4 * x_3 
    else if length.x = 1 then 23 * x_1 else 23 *(x_1 + 2 * x_2))mod 209)
  if w.act ≠ next 
  then if hasdigit.next 
   then BB(Itoken, bindinfo(dict.result.top.stk.b, ["LIT"_1, next], [ mytype."int"]), stk.b, place.b, input.b)
   else BB(Wtoken, bindinfo(dict.result.top.stk.b, [ next], [ mytype."int"]), stk.b, place.b, input.b)
  else if tokenno.act = Itoken 
  then BB(tokenno.act, bindinfo(dict.result.top.stk.b, ["LIT"_1, label.act], [ mytype."int"]), stk.b, place.b, input.b)
  else if tokenno.act = 0 
  then if next ="&quot"_1 
   then // start word list // stepresult(stk.b, place.b + 1, input.b, stringtoken,"")
   else // start comment // stepresult(stk.b, place.b + 1, input.b, commenttoken,"")
  else BB(tokenno.act, bindinfo(dict.result.top.stk.b, [ label.act], [ mytype."int"]), stk.b, place.b, input.b)

function errormessage(message:seq.word, input:seq.word, place:int)seq.word 
 message + prettynoparse(subseq(input, 1, place))

function BB(token:int, tr:bindinfo, stk:stack.stkele, place:int, input:seq.word)stepresult 
 let stateno = stateno.top.stk 
  let actioncode = actiontable_(token + length.tokenlist * stateno)
  if actioncode > 0 
  then stepresult(push(stk, stkele(actioncode, tr)), place + 1, input, 0,"")
  else assert actioncode < 0 report"parse error expect:"+ expect.stateno +"got:"+(if place > length.input then"end of paragraph"else [ input_place])+ // printstate.stateno + // prettynoparse(subseq(input, 1, place))
  let x = reduce(stk,-actioncode, place, input)
  BB(token, bindinfo(dict.result.top.x, code.tr, types.tr), x, place, input)

Function parse(dict:set.symbol, input:seq.word)bindinfo 
 parse(bindinfo(dict,"", empty:seq.mytype), input)

Function parse(b:bindinfo, input:seq.word)bindinfo 
 let a = @(consumeinput, identity, stepresult(push(empty:stack.stkele, stkele(startstate, b)), 1, input, 0,""), input +"#")
  result(toseq(stk.a)_2)

function opaction(subtrees:seq.stkele, input:seq.word, place:int)bindinfo 
 let op = code(result(subtrees_2))_1 
  let dict = dict.result(subtrees_1)
  let types = types.result(subtrees_1)+ types.result(subtrees_3)
  let f = lookupbysig(dict, op, types,input,place)
   bindinfo(dict, code.result(subtrees_1)+ code.result(subtrees_3)+ mangledname(f), [ resulttype(f)])

Function deepcopymangle(type:mytype)word 
 mangle("deepcopy"_1, mytype(towords.type +"deepcopy"), [ mytype."T"])


function unaryop(dict:set.symbol,op:seq.word, exp:bindinfo, input:seq.word, place:int)bindinfo 
  if op _1 ="process"_1 
  then let nopara = manglednopara.last.code.exp 
   let rt = types(exp)_1 
   let prt = mytype(towords.rt +"process")
   let newcode = subseq(code.exp, 1, length.code.exp - 1)+"FREF"+ deepcopymangle.rt +"FREF"+ deepcopymangle.mytype."word seq"+"FREF"+ last.code.exp +"LIT"+ toword.nopara +"PRECORD"+ toword(nopara + 4)
   bindinfo(dict, newcode, [ mytype(towords.rt +"process")])
  else let f = lookupbysig(dict,  op_1, types.exp,input,place)
    bindinfo(dict, code.exp + mangledname(f), [ resulttype(f)])

function apply(term1:bindinfo, term2:bindinfo, term3:bindinfo, term4:bindinfo, input:seq.word, place:int)bindinfo 
 let dict = dict.term1 
  assert abstracttype(types(term4)_1)="seq"_1 report
  errormessage("last term of apply must be seq",input,place)
  let sym2types = types.term2 + [ parameter(types(term4)_1)]
  let sym2 = lookupbysig(dict, code(term2)_1, sym2types,input,place)
  let sym1types = types.term1 + types.term3 + [ resulttype(sym2)]
  let sym1 = lookupbysig(dict, code(term1)_1, sym1types,input,place)
    assert types(term3)_1 = resulttype(sym1)report 
  errormessage("term3 not same as init"+print.types(term3)_1+print.resulttype(sym1),input,place)
  let pseqtype = mytype(towords.parameter(types(term4)_1)+"pseq"_1)
  let idx = mangle("_"_1, mytype(towords.parameter(types(term4)_1)+"seq"_1), [ mytype."T pseq", mytype."int"])
  let x = lookupbysig(dict,"_"_1, [ pseqtype, mytype."int"],input,place)
  bindinfo(dict, subseq(code.term1, 2, length.code.term1)+ subseq(code.term2, 2, length.code.term2)
  + code.term3 + code.term4 +"FREF"+ mangledname(sym2)+"FREF"+ mangledname(sym1)+"FREF"+ 
  idx +"APPLY"+ toword(length.types.term1 + length.types.term2 + 5), types.term3)

function countdigits(s:seq.char, i:int, result:int)word 
 // does not count no-break spaces // 
  if i > length.s 
  then toword.result 
  else countdigits(s, i + 1, result + if s_i = nbspchar then 0 else 1)

function cvttotext(m:mytype)seq.word [ toword.length.towords.m]+ towords.m

function addparameter(orgsize:int,input:seq.word,place:int, dict:set.symbol, m:mytype)set.symbol 
  assert isempty.lookup(dict,abstracttype.m,empty:seq.mytype) &or abstracttype.m=":"_1 report
  errormessage("duplciate symbol:"+abstracttype.m,input,place) 
 let parano = toword(cardinality.dict - orgsize + 1)
  dict + symbol(abstracttype.m, mytype.[ parano,"para"_1], empty:seq.mytype, parameter.m,"")
  
function lookupbysig(dict:set.symbol,name:word,paratypes:seq.mytype,input:seq.word,place:int) symbol
  let f = lookup(dict, name, paratypes)
  assert not.isempty.f report errormessage("cannot find "+ name +"("+ @(seperator.",", print,"", paratypes)+")", input, place)
  assert cardinality.f = 1 report 
  errormessage("found more that one"+ @(+, print2,"", toseq.f),input,place)
  f_1
 
 function createfunc(dict:set.symbol, funcname:seq.word,paralist:seq.mytype,functype:mytype,exp:bindinfo,input:seq.word,place:int)
   bindinfo
    assert  functype = (types.exp)_1 ∨ (types.exp)_1 in[ mytype."internal",mytype."internal1"]
    report errormessage("function type of"+ print.functype +"does not match expression type"+ print.(types.exp)_1 
    , input 
    , place)
     bindinfo(dict, code.exp, [ mytype.funcname,  functype]+ paralist)
     
function isdefined(dict:set.symbol,typ:seq.word,input:seq.word,place:int) seq.word typ

  if cardinality.dict < 15 &or typ in ["T","int"] then typ else
 let a=lookup(dict,merge("type:"+ print.mytype(typ)), empty:seq.mytype)
  assert cardinality.a=1  &or print.mytype(typ) in ["libsym" ,"liblib","mytype","libmod","seq.symbol"
   ] report 
   errormessage(
  "parameter type"+print.mytype(typ) +"is undefined in"  ,// +@(+,print,"",toseq.dict) // input,place)
  typ

function Wtoken int // generated by genlex module in tools // 34

function Itoken int // generated by genlex module in tools // 38

function commenttoken int // generated by genlex module in tools // 11

function stringtoken int // generated by genlex module in tools // 28

function lextable seq.lexaction 
 FORCEINLINE.// generated by genlex module in tools // 
  [ lexaction("`"_1, 0,"`"_1), 
  lexaction("if"_1, 18,"if"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("["_1, 13,"["_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("I"_1, 34,"I"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("@"_1, 29,"@"_1), 
  lexaction("seq"_1, 34,"seq"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("."_1, 1,"."_1), 
  lexaction("∋"_1, 8,"∋"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("function"_1, 34,"function"_1), 
  lexaction("else"_1, 21,"else"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(merge("&"+"contains"), 8,"∋"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(". "_1, 41,". "_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("use"_1, 34,"use"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("∧"_1, 25,"∧"_1), 
  lexaction("A"_1, 34,"A"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("/"_1, 27,"/"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("assert"_1, 23,"assert"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(merge("&"+"cup"), 27,"∪"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("]"_1, 7,"]"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("T"_1, 34,"T"_1), 
  lexaction("empty"_1, 34,"empty"_1), 
  lexaction("K"_1, 34,"K"_1), 
  lexaction("∨"_1, 26,"∨"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("$wordlist"_1, 34,"$wordlist"_1), 
  lexaction("0"_1, 38,"0"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("FP"_1, 34,"FP"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(merge("&"+"ne"), 6,"≠"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("let"_1, 22,"let"_1), 
  lexaction("mod"_1, 27,"mod"_1), 
  lexaction("^"_1, 14,"^"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("L"_1, 34,"L"_1), 
  lexaction("∩"_1, 27,"∩"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(":"_1, 5,":"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(merge("&"+"in"), 8,"∈"_1), 
  lexaction("("_1, 3,"("_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("comment"_1, 34,"comment"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("≠"_1, 6,"≠"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("_"_1, 14,"_"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(">>"_1, 6,">>"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("∪"_1, 27,"∪"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("2"_1, 38,"2"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(")"_1, 4,")"_1), 
  lexaction("//"_1, 0,"//"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("{"_1, 9,"{"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("i"_1, 34,"i"_1), 
  lexaction("Function"_1, 34,"Function"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("W"_1, 34,"W"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("N"_1, 34,"N"_1), 
  lexaction("then"_1, 20,"then"_1), 
  lexaction("E"_1, 34,"E"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("<"_1, 6,"<"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("*"_1, 27,"*"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(merge("&"+"and"), 25,"∧"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("a"_1, 34,"a"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("F"_1, 34,"F"_1), 
  lexaction("word"_1, 34,"word"_1), 
  lexaction("="_1, 2,"="_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("+"_1, 8,"+"_1), 
  lexaction("∈"_1, 8,"∈"_1), 
  lexaction("&quot"_1, 0,"&quot"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("}"_1, 10,"}"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("in"_1, 8,"in"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(merge("&"+"ge"), 6,"≥"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(merge("&"+"or"), 26,"∨"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("P"_1, 34,"P"_1), 
  lexaction("<<"_1, 6,"<<"_1), 
  lexaction("G"_1, 34,"G"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(">"_1, 6,">"_1), 
  lexaction(merge("&"+"cap"), 27,"∩"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(","_1, 12,","_1), 
  lexaction("mytype"_1, 34,"mytype"_1), 
  lexaction("#"_1, 19,"#"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("≤"_1, 6,"≤"_1), 
  lexaction("is"_1, 16,"is"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction(merge("&"+"le"), 6,"≤"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("report"_1, 24,"report"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("?"_1, 6,"?"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("-"_1, 8,"-"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("inst"_1, 34,"inst"_1), 
  lexaction("≥"_1, 6,"≥"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("int"_1, 34,"int"_1), 
  lexaction("`"_1, 0,"`"_1), 
  lexaction("`"_1, 0,"`"_1)]


noactions 2284 
nosymbols:40 alphabet:.=():>]-{ } comment, [_^is T if # then else let assert report ∧ ∨ * $wordlist @ A E G F W P N L I K FP 
norules 58 
nostate 151 

function tokenlist seq.word".=():>]-{ } comment, [_^is T if # then else let assert report ∧ ∨ * $wordlist @ A E G F W P N L I K FP" 

function startstate int 1 

function actiontable seq.int [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 12, 0, 10, 0, 0, 0, 0, 0, 6, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 9, 11, 7, 0, 0, 0, 0, 0, 0, 8, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -45, 0, -45, 0, 0, 0, 0, 0, 0, 0, 0, -45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -49, 0, -49, 0, 0, 0, 0, 0, 0, 0, 0, -49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, -40, 16, -40, 19, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 18, 21, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, 0, 17, 0, -40, 0, -40, 0, 0, -50, 0, -50, 0, 0, 0, 0, 0, 0, 0, 0, -50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -46, 0, -46, 0, 0, 0, 0, 0, 0, 0, 0, -46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -51, 0, -51, 0, 0, 0, 0, 0, 0, 0, 0, -51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -48, 0, -48, 0, 0, 0, 0, 0, 0, 0, 0, -48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -47, 0, -47, 0, 0, 0, 0, 0, 0, 0, 0, -47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 22, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 22, 0, 0, 0, 0, 26, 20, -40, -40, -40, 0, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, 0, -40, 0, -40, 0, -40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 40, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, -40, -40, -40, 47, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, 0, -40, 0, -40, 0, -40, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 49, 0, 0, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, -41, -41, -41, 0, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, 0, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, 0, 0, -41, 0, -41, 0, -41, 0, 0, 53, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 54, 0, 0, 34, 0, 30, 0, 32, 0, 0, 55, -38, -38, -38, 0, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, 0, 0, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, 0, 0, -38, 0, -38, 0, -38, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59, -14, 57, -14, 58, -14, -14, -14, -14, -14, -14, -14, -14, -14, -14, 0, 0, -14, -14, -14, -14, -14, -14, -14, -14, -14, -14, -14, -14, -14, -14, 0, 0, -14, 0, -14, 0, -14, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 60, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, -43, -43, -43, 0, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, 0, 0, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, 0, 0, -43, 0, -43, 0, -43, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 61, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 62, 0, 0, 34, 0, 30, 0, 32, 0, 0, -46, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, -46, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 63, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 71, 0, 0, 0, 69, 0, 67, 0, 0, 0, 0, 0, 64, 70, 0, 0, 0, -4, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 72, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 73, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 75, 0, 0, 34, 0, 30, 74, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 22, 0, 0, 0, 0, 82, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 83, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 75, 0, 0, 34, 0, 30, 84, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 85, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 71, 0, 86, 0, 69, 0, 67, 0, 0, 0, 0, 0, 64, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 87, 0, 0, 0, 13, 0, 0, 0, 12, 0, 10, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 11, 7, 0, 0, 0, 0, 0, 0, 89, 0, 88, 0, 0, 90, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 75, 0, 0, 34, 0, 30, 91, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 92, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 93, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 71, -36, -36, 0, 69, -36, 67, -36, -36, -36, -36, -36, 64, 70, 0, 0, -36, -36, -36, -36, -36, -36, -36, 66, 68, 65, -36, -36, -36, -36, 0, 0, -36, 0, -36, 0, -36, 0, 0, 0, 71, 0, 0, 0, 69, 0, 67, 0, 0, 0, 0, 0, 64, 70, 0, 0, 0, 0, 0, 0, 0, 0, 94, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 0, 0, 0, 69, 0, 67, 0, 95, 0, 0, 0, 64, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -23, -23, -23, 0, -23, -23, -23, -23, -23, -23, -23, -23, 64, 70, 0, 0, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, 0, 0, -23, 0, -23, 0, -23, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 96, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 97, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 98, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 99, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 100, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 101, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 102, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 103, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, -44, -44, -44, 0, -44, -44, -44, -44, -44, -44, -44, -44, 64, 70, 0, 0, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, 0, 0, -44, 0, -44, 0, -44, 0, 0, 0, 71, 0, 0, 0, 69, 0, 67, 0, 0, 0, 0, 0, 64, 70, 0, 0, 0, 0, 104, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 0, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 0, -32, 0, 69, -32, 67, 0, 0, 0, -32, 0, 64, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 107, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, -40, -40, -40, 108, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, 0, -40, 0, -40, 0, -40, 0, 0, 0, 0, 0, -11, 0, 0, 0, 0, 0, 0, 0, -11, 0, 0, 0, 0, 0, 0, -11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 109, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 110, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 0, 0, 111, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 0, 0, 0, 69, 0, 67, 0, 0, 0, 0, 0, 64, 70, 0, 0, 0, -5, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 112, 0, 0, 0, 0, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -25, -25, -25, 0, -25, -25, -25, -25, -25, -25, -25, -25, 64, 70, 0, 0, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, 0, 0, -25, 0, -25, 0, -25, 0, 0, 0, -18, -18, -18, 0, -18, -18, -18, -18, -18, -18, -18, -18, -18, -18, 0, 0, -18, -18, -18, -18, -18, -18, -18, -18, -18, -18, -18, -18, -18, -18, 0, 0, -18, 0, -18, 0, -18, 0, 0, 0, -39, -39, -39, 0, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, 0, 0, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, 0, 0, -39, 0, -39, 0, -39, 0, 0, 114, 0, 113, 0, 0, 0, 0, 0, 0, 0, 0, -56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 116, 0, 115, 0, 0, 0, 0, 0, 0, 0, 0, -57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 117, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 118, 0, 0, 0, 0, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -42, 119, -42, 0, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, 0, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, 0, -42, 0, -42, 0, -42, 0, 0, 0, -24, -24, -24, 0, -24, -24, -24, -24, -24, -24, -24, -24, 64, 70, 0, 0, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, 0, 0, -24, 0, -24, 0, -24, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 120, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, -19, -19, -19, 0, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, 0, 0, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, 0, 0, -19, 0, -19, 0, -19, 0, 0, 0, -22, -22, -22, 0, -22, -22, -22, -22, -22, -22, -22, -22, -22, 70, 0, 0, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, 0, 0, -22, 0, -22, 0, -22, 0, 0, 0, -26, -26, -26, 0, -26, -26, -26, -26, -26, -26, -26, -26, 64, 70, 0, 0, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, 0, 0, -26, 0, -26, 0, -26, 0, 0, 0, 71, -30, -30, 0, 69, -30, 67, -30, -30, -30, -30, -30, 64, 70, 0, 0, -30, -30, -30, -30, -30, -30, -30, -30, -30, 65, -30, -30, -30, -30, 0, 0, -30, 0, -30, 0, -30, 0, 0, 0, -27, -27, -27, 0, -27, -27, -27, -27, -27, -27, -27, -27, 64, 70, 0, 0, -27, -27, -27, -27, -27, -27, -27, -27, -27, 65, -27, -27, -27, -27, 0, 0, -27, 0, -27, 0, -27, 0, 0, 0, 71, -31, -31, 0, 69, -31, 67, -31, -31, -31, -31, -31, 64, 70, 0, 0, -31, -31, -31, -31, -31, -31, -31, 66, -31, 65, -31, -31, -31, -31, 0, 0, -31, 0, -31, 0, -31, 0, 0, 0, -29, -29, -29, 0, -29, -29, 67, -29, -29, -29, -29, -29, 64, 70, 0, 0, -29, -29, -29, -29, -29, -29, -29, -29, -29, 65, -29, -29, -29, -29, 0, 0, -29, 0, -29, 0, -29, 0, 0, 0, 71, -21, -21, 0, 69, -21, 67, -21, -21, -21, -21, -21, 64, 70, 0, 0, -21, -21, -21, -21, -21, -21, -21, 66, 68, 65, -21, -21, -21, -21, 0, 0, -21, 0, -21, 0, -21, 0, 0, 0, -28, -28, -28, 0, -28, -28, 67, -28, -28, -28, -28, -28, 64, 70, 0, 0, -28, -28, -28, -28, -28, -28, -28, -28, -28, 65, -28, -28, -28, -28, 0, 0, -28, 0, -28, 0, -28, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 121, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, -34, -34, -34, 0, -34, -34, -34, -34, -34, -34, -34, -34, -34, -34, 0, 0, -34, -34, -34, -34, -34, -34, -34, -34, -34, -34, -34, -34, -34, -34, 0, 0, -34, 0, -34, 0, -34, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 122, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 123, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 71, 0, 0, 0, 69, 0, 67, 0, 0, 0, 0, 0, 64, 70, 0, 0, 0, -3, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 0, 0, 0, 69, 0, 67, 0, 0, 0, 0, 0, 64, 70, 0, 0, 0, -2, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, -15, -15, -15, 0, -15, -15, -15, -15, -15, -15, -15, -15, -15, -15, 0, 0, -15, -15, -15, -15, -15, -15, -15, -15, -15, -15, -15, -15, -15, -15, 0, 0, -15, 0, -15, 0, -15, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 75, 0, 0, 34, 0, 30, 126, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 127, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 75, 0, 0, 34, 0, 30, 128, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 129, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 0, 0, 0, 12, 0, 10, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 11, 7, 0, 0, 0, 0, 0, 0, 89, 0, 88, 0, 0, 130, 0, 0, -16, -16, -16, 0, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, 0, 0, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, 0, 0, -16, 0, -16, 0, -16, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 75, 0, 0, 34, 0, 30, 131, 32, 0, 0, 0, 139, 31, 0, 0, 138, 0, 135, 38, 0, 41, 0, 43, 132, 70, 0, 0, 42, 0, 0, 0, 44, 37, 0, 134, 136, 133, 36, 33, 35, 137, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 71, 0, 0, 0, 69, 0, 67, 0, 0, 0, 0, 0, 64, 70, 0, 0, 0, 0, 0, 140, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 0, -33, 0, 69, -33, 67, 0, 0, 0, -33, 0, 64, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, -35, 0, 0, 69, 0, 67, -35, 0, -35, 0, -35, 64, 70, 0, 0, -35, 0, 0, 0, -35, -35, 0, 66, 68, 65, -35, -35, -35, -35, 0, 0, -35, 0, -35, 0, -35, 0, 0, 0, 0, 0, -13, 0, 0, 0, 0, 0, 0, 0, -13, 0, 0, 0, 0, 0, 0, -13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 141, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 0, 0, 142, 0, 0, 0, 0, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 0, 0, 0, 69, 0, 67, 0, 0, 0, -53, 0, 64, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 143, 0, 0, 0, 0, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 71, 0, 0, 0, 69, 0, 67, 0, 0, 0, -52, 0, 64, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -45, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, -45, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 96, 0, 0, 34, 0, 30, 0, 32, 0, 0, -49, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, -49, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 97, 0, 0, 34, 0, 30, 0, 32, 0, 0, -50, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, -50, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 98, 0, 0, 34, 0, 30, 0, 32, 0, 0, -46, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, -46, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 146, 0, 0, 34, 0, 30, 0, 32, 0, 0, -51, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, -51, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 100, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 71, -37, -37, 0, 69, -37, 67, -37, -37, -37, -37, -37, 64, 70, 0, 0, -37, -37, -37, -37, -37, -37, -37, 66, 68, 65, -37, -37, -37, -37, 0, 0, -37, 0, -37, 0, -37, 0, 0, -48, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, -48, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 101, 0, 0, 34, 0, 30, 0, 32, 0, 0, -47, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, -47, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 103, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 147, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 71, 0, 0, 0, 69, 0, 67, 0, 0, 0, 0, 0, 64, 70, 0, 0, 0, -6, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 148, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, -17, -17, -17, 0, -17, -17, -17, -17, -17, -17, -17, -17, -17, -17, 0, 0, -17, -17, -17, -17, -17, -17, -17, -17, -17, -17, -17, -17, -17, -17, 0, 0, -17, 0, -17, 0, -17, 0, 0, 0, -27, -27, -27, 0, -27, -27, -27, -27, -27, -27, -27, -27, 64, 70, 0, 0, -27, -27, -27, -27, -27, -27, -27, -27, -27, -23, -27, -27, -27, -27, 0, 0, -27, 0, -27, 0, -27, 0, 0, 0, 71, -20, -20, 0, 69, -20, 67, -20, -20, -20, -20, -20, 64, 70, 0, 0, -20, -20, -20, -20, -20, -20, -20, 66, 68, 65, -20, -20, -20, -20, 0, 0, -20, 0, -20, 0, -20, 0, 0, 0, 71, 0, 0, 0, 69, 0, 67, 0, 0, 0, 149, 0, 64, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 31, 0, 0, 12, 0, 39, 38, 0, 41, 0, 43, 6, 0, 0, 0, 42, 0, 0, 0, 44, 37, 0, 9, 11, 7, 36, 33, 35, 150, 0, 0, 34, 0, 30, 0, 32, 0, 0, 0, 71, 0, 151, 0, 69, 0, 67, 0, 0, 0, 0, 0, 64, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 68, 65, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -58, -58, -58, 0, -58, -58, -58, -58, -58, -58, -58, -58, -58, -58, 0, 0, -58, -58, -58, -58, -58, -58, -58, -58, -58, -58, -58, -58, -58, -58, 0, 0, -58, 0, -58, 0, -58] 

function reduce(stk:stack.stkele, ruleno:int, place:int, input:seq.word)stack.stkele // generated function // 
let rulelen = [ 2, 7, 7, 4, 6, 9, 5, 2, 1, 1, 3, 3, 5, 1, 4, 4, 6, 3, 3, 6, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 4, 2, 5, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 1, 10]_ruleno 
let newstk = pop(stk, rulelen) 
let subtrees = top(stk, rulelen) 
let dict = dict.result.top.stk 
let newtree = 
if ruleno = // G F # // 1 then result.subtrees_1 else 
if ruleno = // F W W(FP)T E // 2 then createfunc(dict, code.result.subtrees_2, types.result.subtrees_4, mytype.code.result.subtrees_6, result.subtrees_7, input, place)else 
if ruleno = // F W N(FP)T E // 3 then createfunc(dict, code.result.subtrees_2, types.result.subtrees_4, mytype.code.result.subtrees_6, result.subtrees_7, input, place)else 
if ruleno = // F W W T E // 4 then createfunc(dict, code.result.subtrees_2, empty:seq.mytype, mytype.code.result.subtrees_3, result.subtrees_4, input, place)else 
if ruleno = // F W W:T T E // 5 then let name = [ merge(code.result.subtrees_2 +":"+ print.mytype.code.result.subtrees_4)]createfunc(dict, name, empty:seq.mytype, mytype.code.result.subtrees_5, result.subtrees_6, input, place)else 
if ruleno = // F W W:T(FP)T E // 6 then let name = [ merge(code.result.subtrees_2 +":"+ print.mytype.code.result.subtrees_4)]createfunc(dict, name, types.result.subtrees_6, mytype.code.result.subtrees_8, result.subtrees_9, input, place)else 
if ruleno = // F W W is W P // 7 then bindinfo(dict, code.result.subtrees_4 + code.result.subtrees_2 + @(+, cvttotext,"", types.result.subtrees_5), types.result.subtrees_5)else 
if ruleno = // F W T // 8 then result.subtrees_2 else 
if ruleno = // FP P // 9 then bindinfo(@(addparameter(cardinality.dict, input, place), identity, dict, types.result.subtrees_1),"", types.result.subtrees_1)else 
if ruleno = // P T // 10 then bindinfo(dict,"", [ mytype(code.result.subtrees_1 +":")])else 
if ruleno = // P P, T // 11 then bindinfo(dict,"", types.result.subtrees_1 + [ mytype(code.result.subtrees_3 +":")])else 
if ruleno = // P W:T // 12 then bindinfo(dict,"", [ mytype(code.result.subtrees_3 + code.result.subtrees_1)])else 
if ruleno = // P P, W:T // 13 then bindinfo(dict,"", types.result.subtrees_1 + [ mytype(code.result.subtrees_5 + code.result.subtrees_3)])else 
if ruleno = // E W // 14 then let id = code.result.subtrees_1 let f = lookupbysig(dict, id_1, empty:seq.mytype, input, place)bindinfo(dict, [ mangledname.f], [ resulttype.f])else 
if ruleno = // E N(L)// 15 then unaryop(dict, code.result.subtrees_1, result.subtrees_3, input, place)else 
if ruleno = // E W(L)// 16 then unaryop(dict, code.result.subtrees_1, result.subtrees_3, input, place)else 
if ruleno = // E W:T(L)// 17 then let name = [ merge(code.result.subtrees_1 +":"+ print.mytype.code.result.subtrees_3)]unaryop(dict, name, result.subtrees_5, input, place)else 
if ruleno = // E(E)// 18 then result.subtrees_2 else 
if ruleno = // E { E } // 19 then result.subtrees_2 else 
if ruleno = // E if E then E else E // 20 then let thenpart = result.subtrees_4 assert(types.result.subtrees_2)_1 = mytype."boolean"report errormessage("cond of if must be boolean", input, place)assert(types.result.subtrees_4)=(types.result.subtrees_6)report errormessage("then and else types are different", input, place)let newcode = code.result.subtrees_2 + code.result.subtrees_4 + code.result.subtrees_6 bindinfo(dict, newcode +"if", types.thenpart)else 
if ruleno = // E E^E // 21 then opaction(subtrees, input, place)else 
if ruleno = // E E_E // 22 then opaction(subtrees, input, place)else 
if ruleno = // E-E // 23 then unaryop(dict,code.result.subtrees_1, result.subtrees_2, input, place)else 
if ruleno = // E W.E // 24 then unaryop(dict,code.result.subtrees_1, result.subtrees_3, input, place)else 
if ruleno = // E N.E // 25 then unaryop(dict,code.result.subtrees_1, result.subtrees_3, input, place)else 
if ruleno = // E E * E // 26 then opaction(subtrees, input, place)else 
if ruleno = // E E-E // 27 then opaction(subtrees, input, place)else 
if ruleno = // E E = E // 28 then opaction(subtrees, input, place)else 
if ruleno = // E E > E // 29 then opaction(subtrees, input, place)else 
if ruleno = // E E ∧ E // 30 then opaction(subtrees, input, place)else 
if ruleno = // E E ∨ E // 31 then opaction(subtrees, input, place)else 
if ruleno = // L E // 32 then result.subtrees_1 else 
if ruleno = // L L, E // 33 then bindinfo(dict, code.result.subtrees_1 + code.result.subtrees_3, types.result.subtrees_1 + types.result.subtrees_3)else 
if ruleno = // E [ L]// 34 then let types = types(result.subtrees_2)assert @(∧, =(types_1), true, types)report errormessage("types do not match in build", input, place)bindinfo(dict,"LIT 0 LIT"+ toword.(length.types)+ code.result.subtrees_2 +"RECORD"+ toword.(length.types + 2), [ mytype(towords(types_1)+"seq")])else 
if ruleno = // A let W = E // 35 then let e = result.subtrees_4 let name =(code.result.subtrees_2)_1 assert isempty.lookup(dict, name, empty:seq.mytype)report errormessage("duplicate symbol:"+ name, input, place)let newdict = dict + symbol(name, mytype("local"), empty:seq.mytype,(types.e)_1,"")bindinfo(newdict, code.e +"define"+ name, types.e)else 
if ruleno = // E A E // 36 then let t = code.result.subtrees_1 let f = lookup(dict, last.code.result.subtrees_1, empty:seq.mytype)assert not(isempty.f)report"internal error/could not find local symbol to delete from dict with name"+ last(code.result(subtrees_1))bindinfo(dict.result.subtrees_1-f_1, subseq(t, 1, length.t-2)+ code.result.subtrees_2 +"SET"+ last.code.result.subtrees_1, types.result.subtrees_2)else 
if ruleno = // E assert E report E E // 37 then assert types(result.subtrees_2)_1 = mytype."boolean"report errormessage("condition in assert must be boolean in:", input, place)assert types(result.subtrees_4)_1 = mytype."word seq"report errormessage("report in assert must be seq of word in:", input, place)let newcode = code.result.subtrees_2 + code.result.subtrees_5 + code.result.subtrees_4 +"assertZbuiltinZwordzseq if"bindinfo(dict, newcode, types.result.subtrees_5)else 
if ruleno = // E I // 38 then result.subtrees_1 else 
if ruleno = // E I.I // 39 then let d = decodeword.(code.result.subtrees_3)_2 bindinfo(dict,"LIT"+ [ encodeword(decodeword.(code.result.subtrees_1)_2 + d)]+"LIT"+ countdigits(d, 1, 0)+"makerealZrealZintZint", [ mytype."real"])else 
if ruleno = // T W // 40 then 
 let discard= isdefined(dict, code.result.subtrees_1,input,place)
result.subtrees_1 
else 
if ruleno = // T W.T // 41 then bindinfo(dict, 
isdefined(dict,code.result.subtrees_3 + code.result.subtrees_1,input,place), 
types.result.subtrees_1)else 
if ruleno = // E W:T // 42 then let f = lookup(dict, merge(code.result.subtrees_1 +":"+ print.mytype.code.result.subtrees_3), empty:seq.mytype)assert not.isempty.f report errormessage("cannot find"+ code.result.subtrees_1 +":"+ print.mytype.code.result.subtrees_3, input, place)bindinfo(dict, [ mangledname.f_1], [ resulttype.f_1])else 
if ruleno = // E $wordlist // 43 then let s = code.result.subtrees_1 bindinfo(dict,"WORDS"+ toword.length.s + s, [ mytype."word seq"])else 
if ruleno = // E comment E // 44 then let s = code.result.subtrees_1 bindinfo(dict, code.result.subtrees_2 +"COMMENT"+ toword.length.s + s, types.result.subtrees_2)else 
if ruleno = // N_// 45 then result.subtrees_1 else 
if ruleno = // N-// 46 then result.subtrees_1 else 
if ruleno = // N = // 47 then result.subtrees_1 else 
if ruleno = // N > // 48 then result.subtrees_1 else 
if ruleno = // N * // 49 then result.subtrees_1 else 
if ruleno = // N ∧ // 50 then result.subtrees_1 else 
if ruleno = // N ∨ // 51 then result.subtrees_1 else 
if ruleno = // K W.E // 52 then bindinfo(dict, code.result.subtrees_1 + code.result.subtrees_3, types.result.subtrees_3)else 
if ruleno = // K N.E // 53 then bindinfo(dict, code.result.subtrees_1 + code.result.subtrees_3, types.result.subtrees_3)else 
if ruleno = // K N(L)// 54 then bindinfo(dict, code.result.subtrees_1 + code.result.subtrees_3, types.result.subtrees_3)else 
if ruleno = // K W(L)// 55 then bindinfo(dict, code.result.subtrees_1 + code.result.subtrees_3, types.result.subtrees_3)else 
if ruleno = // K N // 56 then bindinfo(dict, code.result.subtrees_1, empty:seq.mytype)else 
if ruleno = // K W // 57 then bindinfo(dict, code.result.subtrees_1, empty:seq.mytype)else 
assert ruleno = // E @(K, K, E, E)// 58 report"invalid rule number"+ toword.ruleno 
apply(result.subtrees_3, result.subtrees_5, result.subtrees_7, result.subtrees_9, input, place) 
let leftsidetoken = [ 32, 33, 33, 33, 33, 33, 33, 33, 40, 35, 35, 35, 35, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 37, 37, 31, 30, 31, 31, 31, 31, 17, 17, 31, 31, 31, 36, 36, 36, 36, 36, 36, 36, 39, 39, 39, 39, 39, 39, 31]_ruleno 
let actioncode = actiontable_(leftsidetoken + length.tokenlist * stateno.top.newstk) 
assert actioncode > 0 report"????" 
push(newstk, stkele(actioncode, newtree)) 

