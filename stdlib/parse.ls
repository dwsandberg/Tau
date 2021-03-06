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

Function headdict set.symbol 
 let modulename = mytype."test"
  asset([ symbol("builtin"_1, modulename, [ mytype."internal1"], mytype."internal",""), 
  symbol("builtin"_1, modulename, [ mytype."word seq"], mytype."internal",""), 
  symbol("builtin"_1, modulename, empty:seq.mytype, mytype."internal",""), 
  symbol("STATE"_1, modulename, [ mytype."internal1"], mytype."internal1",""), 
  symbol(merge."sizeoftype:T", mytype."$typesize local", empty:seq.mytype, mytype."int","")]+ @(+, builtinsym.modulename, empty:seq.symbol,"export unbound stub usemangle IDXUC NOOP FROMSEQ"))

function builtinsym(modname:mytype, name:word)symbol 
 symbol(name, modname, empty:seq.mytype, mytype."internal1","")

Function getheader(s:seq.word)seq.word 
 if length.s < 3 
  then s 
  else let startoftype = if s_3 ="("_1 
   then findindex(")"_1, s, 4)+ 1 
   else if s_3 =":"_1 then 4 else 3 
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

Function prettynoparse(s:seq.word, i:int, lastbreak:int, result:seq.word)seq.word 
 if i > length.s 
  then result 
  else let x = s_i 
  if x ="&quot"_1 
  then let t = findindex("&quot"_1, s, i + 1)
   prettynoparse(s, t + 1, lastbreak + t - i, result +"&{ literal"+ subseq(s, i, t)+"&}")
  else if x ="//"_1 
  then let t = findindex("//"_1, s, i + 1)
   prettynoparse(s, t + 1, t - i, result +"&br &{ comment"+ subseq(s, i, t)+"&}")
  else if x in"if then else let assert function Function type"
  then prettynoparse(s, i + 1, 0, result +"&br &keyword"+ x)
  else if x in"report"
  then prettynoparse(s, i + 1, lastbreak + 1, result +"&keyword"+ x)
  else if lastbreak > 20 ∧ x in")]"∨ lastbreak > 40 ∧ x in","
  then prettynoparse(s, i + 1, 0, result + x +"&br")
  else if lastbreak > 20 ∧ x in"["
  then prettynoparse(s, i + 1, 0, result +"&br"+ x)
  else prettynoparse(s, i + 1, lastbreak + 1, result + x)

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
  else let act = let x = decode.next 
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
 message + prettynoparse(subseq(input, 1, place), 1, 0,"")

function BB(token:int, tr:bindinfo, stk:stack.stkele, place:int, input:seq.word)stepresult 
 let stateno = stateno.top.stk 
  let actioncode = actiontable_(token + length.tokenlist * stateno)
  if actioncode > 0 
  then stepresult(push(stk, stkele(actioncode, tr)), place + 1, input, 0,"")
  else assert actioncode < 0 report"parse error expect:"+ expect.stateno +"got:"+(if place > length.input then"end of paragraph"else [ input_place])+ // printstate.stateno + // prettynoparse(subseq(input, 1, place), 1, 0,"")
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
  let f = lookup(dict, op, types)
  assert not.isempty.f report errormessage("cannot find"+ op +"("+ @(seperator.",", print,"", types)+")", input, place)
  bindinfo(dict, code.result(subtrees_1)+ code.result(subtrees_3)+ mangledname(f_1), [ resulttype(f_1)])

Function deepcopymangle(type:mytype)word 
 mangle("deepcopy"_1, mytype(towords.type +"deepcopy"), [ mytype."T"])

function unaryop(op:bindinfo, exp:bindinfo, input:seq.word, place:int)bindinfo 
 let dict = dict.op 
  if code(op)_1 ="process"_1 
  then let nopara = manglednopara.last.code.exp 
   let rt = types(exp)_1 
   let prt = mytype(towords.rt +"process")
   let newcode = subseq(code.exp, 1, length.code.exp - 1)+"FREF"+ deepcopymangle.rt +"FREF"+ deepcopymangle.mytype."word seq"+"FREF"+ last.code.exp +"LIT"+ toword.nopara +"PRECORD"+ toword(nopara + 4)
   bindinfo(dict, newcode, [ mytype(towords.rt +"process")])
  else let f = lookup(dict, code(op)_1, types.exp)
  assert not.isempty.f report errormessage("cannot find unaryop"+ code.op +"("+ @(seperator.",", print,"", types.exp)+")", input, place)
  assert cardinality.f = 1 ∨ code(op)_1 in"length"report"found more that one"+ @(+, print2,"", toseq.f)
  // assert code(op)_1 &ne"arithseq"_1 report"XX"+ print.f_1 // 
  bindinfo(dict, code.exp + mangledname(f_1), [ resulttype(f_1)])

function apply(term1:bindinfo, term2:bindinfo, term3:bindinfo, term4:bindinfo, input:seq.word, place:int)bindinfo 
 let dict = dict.term1 
  assert abstracttype(types(term4)_1)="seq"_1 report"last term of apply must be seq"
  let sym2types = types.term2 + [ parameter(types(term4)_1)]
  let sym2 = lookup(dict, code(term2)_1, sym2types)
  assert not.isempty.sym2 report errormessage("cannot find term2"+ code(term2)_1 +"("+ @(seperator.",", print,"", sym2types)+")", input, place)
  let sym1types = types.term1 + types.term3 + [ resulttype(sym2_1)]
  let sym1 = lookup(dict, code(term1)_1, sym1types)
  assert not.isempty.sym1 report"cannot find term1"+ code(term1)_1 +"("+ @(seperator.",", print,"", sym1types)+")"+"sym2"+ print(sym2_1)
  assert types(term3)_1 = resulttype(sym1_1)report"term3 not same as init"
  let pseqtype = mytype(towords.parameter(types(term4)_1)+"pseq"_1)
  let idx = mangle("_"_1, mytype(towords.parameter(types(term4)_1)+"seq"_1), [ mytype."T pseq", mytype."int"])
  let x = lookup(dict,"_"_1, [ pseqtype, mytype."int"])
  assert not.isempty.x report"cannot find index function for"+ print.pseqtype 
  // assert mangledname.x_1 = idx report"ERR15"+ mangledname.x_1 + idx // 
  bindinfo(dict, subseq(code.term1, 2, length.code.term1)+ subseq(code.term2, 2, length.code.term2)+ code.term3 + code.term4 +"FREF"+ mangledname(sym2_1)+"FREF"+ mangledname(sym1_1)+"FREF"+ idx +"APPLY"+ toword(length.types.term1 + length.types.term2 + 5), types.term3)

function countdigits(s:seq.int, i:int, result:int)word 
 // does not count no-break spaces // 
  if i > length.s 
  then toword.result 
  else countdigits(s, i + 1, result + if s_i = nbspchar then 0 else 1)

function cvttotext(m:mytype)seq.word [ toword.length.towords.m]+ towords.m

function addparameter(orgsize:int, dict:set.symbol, m:mytype)set.symbol 
 let parano = toword(cardinality.dict - orgsize + 1)
  dict + symbol(abstracttype.m, mytype.[ parano,"para"_1], empty:seq.mytype, parameter.m,"")

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

noactions 2186 nosymbols:40 alphabet:.=():>]-{ } comment, [_^is T if # then else let assert report ∧ ∨ * $wordlist @ A E G F W P N L I K FP norules 56 nostate 142 follow.> =.>(.> >.>-.> {.> comment.> [.>_.> T.> if.> let.> assert.> ∧.> ∨.> *.> $wordlist.> @.> A.> E.> W.> N.> I = >.= > = = >(= > > = >-= > { = > comment = >, = > [ = >_= > if = > let = > assert = > ∧ = > ∨ = > * = > $wordlist = > @ = > A = > E = > W = > N = > I(> =(>((> >(>-(> {(> comment(> [(>_(> T(> if(> let(> assert(> ∧(> ∨(> *(> $wordlist(> @(> A(> E(> W(> P(> N(> L(> I(> K(> FP)> =)>()>))> >)>])>-)> {)> })> comment)>,)> [)>_)>^)> T)> if)> #)> then)> else)> let)> assert)> report)> ∧)> ∨)> *)> $wordlist)> @)> A)> E)> W)> N)> I:> T:> W > >.> > = > >(> > > > >-> > { > > comment > >, > > [ > >_> > if > > let > > assert > > ∧ > > ∨ > > * > > $wordlist > > @ > > A > > E > > W > > N > > I]> =]>(]>)]> >]>]]>-]> {]> }]> comment]>,]> []>_]>^]> if]> #]> then]> else]> let]> assert]> report]> ∧]> ∨]> *]> $wordlist]> @]> A]> E]> W]> N]> I->.-> =->(-> >->--> {-> comment->,-> [->_-> if-> let-> assert-> ∧-> ∨-> *-> $wordlist-> @-> A-> E-> W-> N-> I { > = { >({ > > { >-{ > { { > comment { > [ { >_{ > if { > let { > assert { > ∧ { > ∨ { > * { > $wordlist { > @ { > A { > E { > W { > N { > I } > = } >(} >)} > > } >]} >-} > { } > } } > comment } >, } > [ } >_} >^} > if } > # } > then } > else } > let } > assert } > report } > ∧ } > ∨ } > * } > $wordlist } > @ } > A } > E } > W } > N } > I comment > = comment >(comment > > comment >-comment > { comment > comment comment > [ comment >_comment > if comment > let comment > assert comment > ∧ comment > ∨ comment > * comment > $wordlist comment > @ comment > A comment > E comment > W comment > N comment > I, > =, >(, > >, >-, > {, > comment, > [, >_, > T, > if, > let, > assert, > ∧, > ∨, > *, > $wordlist, > @, > A, > E, > W, > N, > I, > K [ > = [ >([ > > [ >-[ > { [ > comment [ > [ [ >_[ > if [ > let [ > assert [ > ∧ [ > ∨ [ > * [ > $wordlist [ > @ [ > A [ > E [ > W [ > N [ > L [ > I_>._> =_>(_> >_>-_> {_> comment_>,_> [_>__> if_> let_> assert_> ∧_> ∨_> *_> $wordlist_> @_> A_> E_> W_> N_> I^> =^>(^> >^>-^> {^> comment^> [^>_^> if^> let^> assert^> ∧^> ∨^> *^> $wordlist^> @^> A^> E^> W^> N^> I is > W T > = T >(T >)T > > T >]T >-T > { T > } T > comment T >, T > [ T >_T >^T > if T > # T > then T > else T > let T > assert T > report T > ∧ T > ∨ T > * T > $wordlist T > @ T > A T > E T > W T > N T > I if > = if >(if > > if >-if > { if > comment if > [ if >_if > if if > let if > assert if > ∧ if > ∨ if > * if > $wordlist if > @ if > A if > E if > W if > N if > I then > = then >(then > > then >-then > { then > comment then > [ then >_then > if then > let then > assert then > ∧ then > ∨ then > * then > $wordlist then > @ then > A then > E then > W then > N then > I else > = else >(else > > else >-else > { else > comment else > [ else >_else > if else > let else > assert else > ∧ else > ∨ else > * else > $wordlist else > @ else > A else > E else > W else > N else > I let > W assert > = assert >(assert > > assert >-assert > { assert > comment assert > [ assert >_assert > if assert > let assert > assert assert > ∧ assert > ∨ assert > * assert > $wordlist assert > @ assert > A assert > E assert > W assert > N assert > I report > = report >(report > > report >-report > { report > comment report > [ report >_report > if report > let report > assert report > ∧ report > ∨ report > * report > $wordlist report > @ report > A report > E report > W report > N report > I ∧ >.∧ > = ∧ >(∧ > > ∧ >-∧ > { ∧ > comment ∧ >, ∧ > [ ∧ >_∧ > if ∧ > let ∧ > assert ∧ > ∧ ∧ > ∨ ∧ > * ∧ > $wordlist ∧ > @ ∧ > A ∧ > E ∧ > W ∧ > N ∧ > I ∨ >.∨ > = ∨ >(∨ > > ∨ >-∨ > { ∨ > comment ∨ >, ∨ > [ ∨ >_∨ > if ∨ > let ∨ > assert ∨ > ∧ ∨ > ∨ ∨ > * ∨ > $wordlist ∨ > @ ∨ > A ∨ > E ∨ > W ∨ > N ∨ > I * >.* > = * >(* > > * >-* > { * > comment * >, * > [ * >_* > if * > let * > assert * > ∧ * > ∨ * > * * > $wordlist * > @ * > A * > E * > W * > N * > I $wordlist > = $wordlist >($wordlist >)$wordlist > > $wordlist >]$wordlist >-$wordlist > { $wordlist > } $wordlist > comment $wordlist >, $wordlist > [ $wordlist >_$wordlist >^$wordlist > if $wordlist > # $wordlist > then $wordlist > else $wordlist > let $wordlist > assert $wordlist > report $wordlist > ∧ $wordlist > ∨ $wordlist > * $wordlist > $wordlist $wordlist > @ $wordlist > A $wordlist > E $wordlist > W $wordlist > N $wordlist > I @ >(A > = A >(A > > A >-A > { A > comment A > [ A >_A > if A > let A > assert A > ∧ A > ∨ A > * A > $wordlist A > @ A > A A > E A > W A > N A > I E > = E >(E >)E > > E >]E >-E > { E > } E > comment E >, E > [ E >_E >^E > if E > # E > then E > else E > let E > assert E > report E > ∧ E > ∨ E > * E > $wordlist E > @ E > A E > E E > W E > N E > I F > # W >.W > = W >(W >)W >:W > > W >]W >-W > { W > } W > comment W >, W > [ W >_W >^W > is W > T W > if W > # W > then W > else W > let W > assert W > report W > ∧ W > ∨ W > * W > $wordlist W > @ W > A W > E W > W W > P W > N W > I P >)P >, P > # N >.N >(N >, L >)L >]L >, I >.I > = I >(I >)I > > I >]I >-I > { I > } I > comment I >, I > [ I >_I >^I > if I > # I > then I > else I > let I > assert I > report I > ∧ I > ∨ I > * I > $wordlist I > @ I > A I > E I > W I > N I > I K >, FP >)

function tokenlist seq.word 
 {".=():>]-{ } comment, [_^is T if # then else let assert report ∧ ∨ * $wordlist @ A E G F W P N L I K FP"}

function startstate int 1

function actiontable seq.int 
 [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 5, 0, 0, 0, 6, 0, 7, 0, 0, 
 0, 0, 0, 8, 0, 0, 9, 0, 0, 0, 
 0, 0, 0, 0, 10, 11, 12, 0, 0, 0, 
 0, 0, 0, 13, 0, 14, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 -45, 0,-45, 0, 0, 0, 0, 0, 0, 0, 
 0,-45, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 -46, 0,-46, 0, 0, 0, 0, 0, 0, 0, 
 0,-46, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 -44, 0,-44, 0, 0, 0, 0, 0, 0, 0, 
 0,-44, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 -43, 0,-43, 0, 0, 0, 0, 0, 0, 0, 
 0,-43, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0,-7, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 -48, 0,-48, 0, 0, 0, 0, 0, 0, 0, 
 0,-48, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 -49, 0,-49, 0, 0, 0, 0, 0, 0, 0, 
 0,-49, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 -47, 0,-47, 0, 0, 0, 0, 0, 0, 0, 
 0,-47, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 15,-38, 16,-38, 17,-38,-38,-38,-38,-38, 
 -38,-38,-38,-38,-38, 18, 19,-38,-38,-38, 
 -38,-38,-38,-38,-38,-38,-38,-38,-38,-38, 
 -38, 0, 0, 20, 0,-38, 0,-38, 0, 0, 
 0, 0, 21, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 22, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 24, 25, 0, 0, 0, 0, 26, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 40, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 15,-38,-38,-38, 0,-38,-38,-38,-38,-38, 
 -38,-38,-38,-38,-38, 0, 0,-38,-38,-38, 
 -38,-38,-38,-38,-38,-38,-38,-38,-38,-38, 
 -38, 0, 0,-38, 0,-38, 0,-38, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 24, 25, 0, 0, 0, 0, 44, 
 0,-39,-39,-39, 0,-39,-39,-39,-39,-39, 
 -39,-39,-39,-39,-39, 0, 0,-39,-39,-39, 
 -39,-39,-39,-39,-39,-39,-39,-39,-39,-39, 
 -39, 0, 0,-39, 0,-39, 0,-39, 0, 0, 
 0, 0, 0,-9, 0, 0, 0, 0, 0, 0, 
 0,-9, 0, 0, 0, 0, 0, 0,-9, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 15,-38,-38,-38, 45,-38,-38,-38,-38,-38, 
 -38,-38,-38,-38,-38, 0, 0,-38,-38,-38, 
 -38,-38,-38,-38,-38,-38,-38,-38,-38,-38, 
 -38, 0, 0,-38, 0,-38, 0,-38, 0, 0, 
 0, 0, 0,-8, 0, 0, 0, 0, 0, 0, 
 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 48, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 24, 49, 0, 0, 0, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 50, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 -44, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32,-44, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 51, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 52, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 53, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 54, 0, 0, 41, 0, 42, 55, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 56, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 57, 0, 0, 0, 0, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 58, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0,-41,-41,-41, 0,-41,-41,-41,-41,-41, 
 -41,-41,-41,-41,-41, 0, 0,-41,-41,-41, 
 -41,-41,-41,-41,-41,-41,-41,-41,-41,-41, 
 -41, 0, 0,-41, 0,-41, 0,-41, 0, 0, 
 0, 0, 59, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 60, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 61, 0, 0, 0, 62, 0, 63, 0, 0, 
 0, 0, 0, 64, 65, 0, 0, 0,-4, 0, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 69,-13, 70,-13, 71,-13,-13,-13,-13,-13, 
 -13,-13,-13,-13,-13, 0, 0,-13,-13,-13, 
 -13,-13,-13,-13,-13,-13,-13,-13,-13,-13, 
 -13, 0, 0,-13, 0,-13, 0,-13, 0, 0, 
 72, 0, 73, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 74,-36,-36,-36, 0,-36,-36,-36,-36,-36, 
 -36,-36,-36,-36,-36, 0, 0,-36,-36,-36, 
 -36,-36,-36,-36,-36,-36,-36,-36,-36,-36, 
 -36, 0, 0,-36, 0,-36, 0,-36, 0, 0, 
 0, 0, 0, 75, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 77, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 78, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 79, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 
 0, 61, 0, 0, 0, 62, 0, 63, 0, 0, 
 0, 0, 0, 64, 65, 0, 0, 0,-5, 0, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 46, 0, 0, 0, 0, 0, 0,-6, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 61, 0, 80, 0, 62, 0, 63, 0, 0, 
 0, 0, 0, 64, 65, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0,-21,-21,-21, 0,-21,-21,-21,-21,-21, 
 -21,-21,-21, 64, 65, 0, 0,-21,-21,-21, 
 -21,-21,-21,-21,-21,-21,-21,-21,-21,-21, 
 -21, 0, 0,-21, 0,-21, 0,-21, 0, 0, 
 0, 61, 0, 0, 0, 62, 0, 63, 0, 81, 
 0, 0, 0, 64, 65, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0,-42,-42,-42, 0,-42,-42,-42,-42,-42, 
 -42,-42,-42, 64, 65, 0, 0,-42,-42,-42, 
 -42,-42,-42,-42,-42,-42,-42,-42,-42,-42, 
 -42, 0, 0,-42, 0,-42, 0,-42, 0, 0, 
 0, 61, 0,-30, 0, 62,-30, 63, 0, 0, 
 0,-30, 0, 64, 65, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 82, 0, 0, 0, 
 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 61, 0, 0, 0, 62, 0, 63, 0, 0, 
 0, 0, 0, 64, 65, 0, 0, 0, 0, 84, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 85, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 61, 0, 0, 0, 62, 0, 63, 0, 0, 
 0, 0, 0, 64, 65, 0, 0, 0, 0, 0, 
 0, 0, 0, 86, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 5, 0, 0, 0, 6, 0, 7, 0, 0, 
 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 10, 11, 12, 0, 0, 0, 
 0, 0, 0, 87, 0, 88, 0, 0, 89, 0, 
 0, 61,-34,-34, 0, 62,-34, 63,-34,-34, 
 -34,-34,-34, 64, 65, 0, 0,-34,-34,-34, 
 -34,-34,-34,-34, 66, 67, 68,-34,-34,-34, 
 -34, 0, 0,-34, 0,-34, 0,-34, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 90, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 91, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 92, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 93, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 94, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 95, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 96, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 97, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 98, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 54, 0, 0, 41, 0, 42, 99, 43, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 100, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 101, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 54, 0, 0, 41, 0, 42, 102, 43, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 103, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 104, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 
 0, 0, 0,-11, 0, 0, 0, 0, 0, 0, 
 0,-11, 0, 0, 0, 0, 0, 0,-11, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0,-10, 0, 0, 0, 0, 0, 0, 
 0,-10, 0, 0, 0, 0, 0, 0,-10, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 15,-38,-38,-38, 105,-38,-38,-38,-38,-38, 
 -38,-38,-38,-38,-38, 0, 0,-38,-38,-38, 
 -38,-38,-38,-38,-38,-38,-38,-38,-38,-38, 
 -38, 0, 0,-38, 0,-38, 0,-38, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 106, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0,-16,-16,-16, 0,-16,-16,-16,-16,-16, 
 -16,-16,-16,-16,-16, 0, 0,-16,-16,-16, 
 -16,-16,-16,-16,-16,-16,-16,-16,-16,-16, 
 -16, 0, 0,-16, 0,-16, 0,-16, 0, 0, 
 0,-17,-17,-17, 0,-17,-17,-17,-17,-17, 
 -17,-17,-17,-17,-17, 0, 0,-17,-17,-17, 
 -17,-17,-17,-17,-17,-17,-17,-17,-17,-17, 
 -17, 0, 0,-17, 0,-17, 0,-17, 0, 0, 
 0,-32,-32,-32, 0,-32,-32,-32,-32,-32, 
 -32,-32,-32,-32,-32, 0, 0,-32,-32,-32, 
 -32,-32,-32,-32,-32,-32,-32,-32,-32,-32, 
 -32, 0, 0,-32, 0,-32, 0,-32, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 107, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 108, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 109, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 110, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 111, 0, 112, 0, 0, 0, 0, 0, 0, 0, 
 0,-55, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 113, 0, 114, 0, 0, 0, 0, 0, 0, 0, 
 0,-54, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 115, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0,-26,-26,-26, 0,-26,-26, 63,-26,-26, 
 -26,-26,-26, 64, 65, 0, 0,-26,-26,-26, 
 -26,-26,-26,-26,-26,-26, 68,-26,-26,-26, 
 -26, 0, 0,-26, 0,-26, 0,-26, 0, 0, 
 0,-27,-27,-27, 0,-27,-27, 63,-27,-27, 
 -27,-27,-27, 64, 65, 0, 0,-27,-27,-27, 
 -27,-27,-27,-27,-27,-27, 68,-27,-27,-27, 
 -27, 0, 0,-27, 0,-27, 0,-27, 0, 0, 
 0,-25,-25,-25, 0,-25,-25,-25,-25,-25, 
 -25,-25,-25, 64, 65, 0, 0,-25,-25,-25, 
 -25,-25,-25,-25,-25,-25, 68,-25,-25,-25, 
 -25, 0, 0,-25, 0,-25, 0,-25, 0, 0, 
 0,-20,-20,-20, 0,-20,-20,-20,-20,-20, 
 -20,-20,-20,-20, 65, 0, 0,-20,-20,-20, 
 -20,-20,-20,-20,-20,-20,-20,-20,-20,-20, 
 -20, 0, 0,-20, 0,-20, 0,-20, 0, 0, 
 0, 61,-19,-19, 0, 62,-19, 63,-19,-19, 
 -19,-19,-19, 64, 65, 0, 0,-19,-19,-19, 
 -19,-19,-19,-19, 66, 67, 68,-19,-19,-19, 
 -19, 0, 0,-19, 0,-19, 0,-19, 0, 0, 
 0, 61,-28,-28, 0, 62,-28, 63,-28,-28, 
 -28,-28,-28, 64, 65, 0, 0,-28,-28,-28, 
 -28,-28,-28,-28,-28,-28, 68,-28,-28,-28, 
 -28, 0, 0,-28, 0,-28, 0,-28, 0, 0, 
 0, 61,-29,-29, 0, 62,-29, 63,-29,-29, 
 -29,-29,-29, 64, 65, 0, 0,-29,-29,-29, 
 -29,-29,-29,-29, 66,-29, 68,-29,-29,-29, 
 -29, 0, 0,-29, 0,-29, 0,-29, 0, 0, 
 0,-24,-24,-24, 0,-24,-24,-24,-24,-24, 
 -24,-24,-24, 64, 65, 0, 0,-24,-24,-24, 
 -24,-24,-24,-24,-24,-24,-24,-24,-24,-24, 
 -24, 0, 0,-24, 0,-24, 0,-24, 0, 0, 
 0,-22,-22,-22, 0,-22,-22,-22,-22,-22, 
 -22,-22,-22, 64, 65, 0, 0,-22,-22,-22, 
 -22,-22,-22,-22,-22,-22,-22,-22,-22,-22, 
 -22, 0, 0,-22, 0,-22, 0,-22, 0, 0, 
 0, 0, 0, 116, 0, 0, 0, 0, 0, 0, 
 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0,-40,-40,-40, 0,-40,-40,-40,-40,-40, 
 -40,-40,-40,-40,-40, 0, 0,-40,-40,-40, 
 -40,-40,-40,-40,-40,-40,-40,-40,-40,-40, 
 -40, 0, 0,-40, 0,-40, 0,-40, 0, 0, 
 0,-23,-23,-23, 0,-23,-23,-23,-23,-23, 
 -23,-23,-23, 64, 65, 0, 0,-23,-23,-23, 
 -23,-23,-23,-23,-23,-23,-23,-23,-23,-23, 
 -23, 0, 0,-23, 0,-23, 0,-23, 0, 0, 
 0, 0, 0, 117, 0, 0, 0, 0, 0, 0, 
 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0,-37,-37,-37, 0,-37,-37,-37,-37,-37, 
 -37,-37,-37,-37,-37, 0, 0,-37,-37,-37, 
 -37,-37,-37,-37,-37,-37,-37,-37,-37,-37, 
 -37, 0, 0,-37, 0,-37, 0,-37, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 118, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 119, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 
 0, 61, 0, 0, 0, 62, 0, 63, 0, 0, 
 0, 0, 0, 64, 65, 0, 0, 0,-2, 0, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 61, 0,-31, 0, 62,-31, 63, 0, 0, 
 0,-31, 0, 64, 65, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 61, 0, 0, 0, 62, 0, 63, 0, 0, 
 0, 0, 0, 64, 65, 0, 0, 0, 0, 0, 
 120, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 61,-33, 0, 0, 62, 0, 63,-33, 0, 
 -33, 0,-33, 64, 65, 0, 0,-33, 0, 0, 
 0,-33,-33, 0, 66, 67, 68,-33,-33,-33, 
 -33, 0, 0,-33, 0,-33, 0,-33, 0, 0, 
 0, 121, 29, 0, 0, 122, 0, 123, 31, 0, 
 32, 0, 33, 124, 65, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 125, 126, 127, 37, 38, 39, 
 128, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 129, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 54, 0, 0, 41, 0, 42, 130, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 131, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 54, 0, 0, 41, 0, 42, 132, 43, 0, 0, 
 0, 5, 0, 0, 0, 6, 0, 7, 0, 0, 
 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 10, 11, 12, 0, 0, 0, 
 0, 0, 0, 87, 0, 88, 0, 0, 133, 0, 
 0,-15,-15,-15, 0,-15,-15,-15,-15,-15, 
 -15,-15,-15,-15,-15, 0, 0,-15,-15,-15, 
 -15,-15,-15,-15,-15,-15,-15,-15,-15,-15, 
 -15, 0, 0,-15, 0,-15, 0,-15, 0, 0, 
 0,-14,-14,-14, 0,-14,-14,-14,-14,-14, 
 -14,-14,-14,-14,-14, 0, 0,-14,-14,-14, 
 -14,-14,-14,-14,-14,-14,-14,-14,-14,-14, 
 -14, 0, 0,-14, 0,-14, 0,-14, 0, 0, 
 0, 61, 0, 0, 0, 62, 0, 63, 0, 0, 
 0, 0, 0, 64, 65, 0, 0, 0,-3, 0, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0,-12, 0, 0, 0, 0, 0, 0, 
 0,-12, 0, 0, 0, 0, 0, 0,-12, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 134, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 -45, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32,-45, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 90, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 -46, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32,-46, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 91, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 -44, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32,-44, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 135, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 -43, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32,-43, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 93, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 -48, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32,-48, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 95, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 -49, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32,-49, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 96, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 -47, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32,-47, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 97, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 61,-35,-35, 0, 62,-35, 63,-35,-35, 
 -35,-35,-35, 64, 65, 0, 0,-35,-35,-35, 
 -35,-35,-35,-35, 66, 67, 68,-35,-35,-35, 
 -35, 0, 0,-35, 0,-35, 0,-35, 0, 0, 
 0, 61, 0, 0, 0, 62, 0, 63, 0, 0, 
 0,-50, 0, 64, 65, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 136, 0, 0, 0, 0, 0, 0, 
 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 61, 0, 0, 0, 62, 0, 63, 0, 0, 
 0,-51, 0, 64, 65, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 137, 0, 0, 0, 0, 0, 0, 
 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 138, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 61,-18,-18, 0, 62,-18, 63,-18,-18, 
 -18,-18,-18, 64, 65, 0, 0,-18,-18,-18, 
 -18,-18,-18,-18, 66, 67, 68,-18,-18,-18, 
 -18, 0, 0,-18, 0,-18, 0,-18, 0, 0, 
 0,-25,-25,-25, 0,-25,-25,-25,-25,-25, 
 -25,-25,-25, 64, 65, 0, 0,-25,-25,-25, 
 -25,-25,-25,-25,-25,-25,-21,-25,-25,-25, 
 -25, 0, 0,-25, 0,-25, 0,-25, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0,-53, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0,-52, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 139, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 61, 0, 0, 0, 62, 0, 63, 0, 0, 
 0, 140, 0, 64, 65, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0, 5, 29, 0, 0, 6, 0, 30, 31, 0, 
 32, 0, 33, 8, 0, 0, 0, 34, 0, 0, 
 0, 35, 36, 0, 10, 11, 12, 37, 38, 39, 
 141, 0, 0, 41, 0, 42, 0, 43, 0, 0, 
 0, 61, 0, 142, 0, 62, 0, 63, 0, 0, 
 0, 0, 0, 64, 65, 0, 0, 0, 0, 0, 
 0, 0, 0, 0, 66, 67, 68, 0, 0, 0, 
 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
 0,-56,-56,-56, 0,-56,-56,-56,-56,-56, 
 -56,-56,-56,-56,-56, 0, 0,-56,-56,-56, 
 -56,-56,-56,-56,-56,-56,-56,-56,-56,-56, 
 -56, 0, 0,-56, 0,-56, 0,-56]

function reduce(stk:stack.stkele, ruleno:int, place:int, input:seq.word)stack.stkele 
 // generated function // 
  let rulelen = [ 2, 7, 7, 4, 5, 5, 2, 1, 1, 3, 
  3, 5, 1, 4, 4, 3, 3, 6, 3, 3, 
  2, 3, 3, 3, 3, 3, 3, 3, 3, 1, 
  3, 3, 4, 2, 5, 1, 3, 1, 3, 3, 
  1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 
  3, 4, 4, 1, 1, 10]_ruleno 
  let newstk = pop(stk, rulelen)
  let subtrees = top(stk, rulelen)
  let dict = dict.result.top.stk 
  let newtree = if ruleno = // G F # // 1 
   then result(subtrees_1)
   else if ruleno = // F W W(FP)T E // 2 
   then let functype = code.result(subtrees_6)
    let exptype = types.result(subtrees_7)
    assert mytype.functype = exptype_1 ∨ exptype_1 = mytype."internal"report errormessage("function type of"+ print.mytype.functype +"does not match expression type"+ print(exptype_1), input, place)
    bindinfo(dict, code.result(subtrees_7), [ mytype.code.result(subtrees_2), mytype.functype]+ types.result(subtrees_4))
   else if ruleno = // F W N(FP)T E // 3 
   then let functype = code.result(subtrees_6)
    let exptype = types.result(subtrees_7)
    assert mytype.functype = exptype_1 ∨ exptype_1 = mytype."internal"report errormessage("function type of"+ print.mytype.functype +"does not match expression type"+ print(exptype_1), input, place)
    bindinfo(dict, code.result(subtrees_7), [ mytype.code.result(subtrees_2), mytype.functype]+ types.result(subtrees_4))
   else if ruleno = // F W W T E // 4 
   then let functype = code.result(subtrees_3)
    let exptype = types.result(subtrees_4)
    assert mytype.functype = exptype_1 ∨ exptype_1 = mytype."internal"report errormessage("function type of"+ print.mytype.functype +"does not match expression type"+ print(exptype_1), input, place)
    bindinfo(dict, code.result(subtrees_4), [ mytype.code.result(subtrees_2), mytype.functype])
   else if ruleno = // F W W:T E // 5 
   then let functype = code.result(subtrees_4)
    let exptype = types.result(subtrees_5)
    assert mytype.functype = exptype_1 ∨ exptype_1 = mytype."internal"report errormessage("function type of"+ print.mytype.functype +"does not match expression type"+ print(exptype_1), input, place)
    bindinfo(dict, code.result(subtrees_5), [ mytype.[ merge(code.result(subtrees_2)+":"+ print.mytype.functype)], mytype.functype])
   else if ruleno = // F W W is W P // 6 
   then bindinfo(dict, code.result(subtrees_4)+ code.result(subtrees_2)+ @(+, cvttotext,"", types.result(subtrees_5)), types.result(subtrees_5))
   else if ruleno = // F W T // 7 
   then result(subtrees_2)
   else if ruleno = // FP P // 8 
   then bindinfo(@(addparameter.cardinality.dict, identity, dict, types.result(subtrees_1)),"", types.result(subtrees_1))
   else if ruleno = // P T // 9 
   then bindinfo(dict,"", [ mytype(code.result(subtrees_1)+":")])
   else if ruleno = // P P, T // 10 
   then bindinfo(dict,"", types.result(subtrees_1)+ [ mytype(code.result(subtrees_3)+":")])
   else if ruleno = // P W:T // 11 
   then bindinfo(dict,"", [ mytype(code.result(subtrees_3)+ code.result(subtrees_1))])
   else if ruleno = // P P, W:T // 12 
   then bindinfo(dict,"", types.result(subtrees_1)+ [ mytype(code.result(subtrees_5)+ code.result(subtrees_3))])
   else if ruleno = // E W // 13 
   then let id = code.result(subtrees_1)
    let f = lookup(dict, id_1, empty:seq.mytype)
    assert not.isempty.f report errormessage("cannot find id"+ id, input, place)
    bindinfo(dict, [ mangledname(f_1)], [ resulttype(f_1)])
   else if ruleno = // E N(L)// 14 
   then unaryop(result(subtrees_1), result(subtrees_3), input, place)
   else if ruleno = // E W(L)// 15 
   then unaryop(result(subtrees_1), result(subtrees_3), input, place)
   else if ruleno = // E(E)// 16 
   then result(subtrees_2)
   else if ruleno = // E { E } // 17 
   then result(subtrees_2)
   else if ruleno = // E if E then E else E // 18 
   then let thenpart = result(subtrees_4)
    assert types(result(subtrees_2))_1 = mytype."boolean"report errormessage("cond of if must be boolean", input, place)
    assert types.result(subtrees_4)= types.result(subtrees_6)report errormessage("then and else types are different", input, place)
    let newcode = code.result(subtrees_2)+ code.result(subtrees_4)+ code.result(subtrees_6)
    bindinfo(dict, newcode +"if", types.thenpart)
   else if ruleno = // E E^E // 19 
   then opaction(subtrees, input, place)
   else if ruleno = // E E_E // 20 
   then opaction(subtrees, input, place)
   else if ruleno = // E-E // 21 
   then unaryop(result(subtrees_1), result(subtrees_2), input, place)
   else if ruleno = // E W.E // 22 
   then unaryop(result(subtrees_1), result(subtrees_3), input, place)
   else if ruleno = // E N.E // 23 
   then unaryop(result(subtrees_1), result(subtrees_3), input, place)
   else if ruleno = // E E * E // 24 
   then opaction(subtrees, input, place)
   else if ruleno = // E E-E // 25 
   then opaction(subtrees, input, place)
   else if ruleno = // E E = E // 26 
   then opaction(subtrees, input, place)
   else if ruleno = // E E > E // 27 
   then opaction(subtrees, input, place)
   else if ruleno = // E E ∧ E // 28 
   then opaction(subtrees, input, place)
   else if ruleno = // E E ∨ E // 29 
   then opaction(subtrees, input, place)
   else if ruleno = // L E // 30 
   then result(subtrees_1)
   else if ruleno = // L L, E // 31 
   then bindinfo(dict, code.result(subtrees_1)+ code.result(subtrees_3), types.result(subtrees_1)+ types.result(subtrees_3))
   else if ruleno = // E [ L]// 32 
   then let types = types.result(subtrees_2)
    assert @(∧, =(types_1), true, types)report errormessage("types do not match in build", input, place)
    bindinfo(dict,"LIT 0 LIT"+ toword.length.types + code.result(subtrees_2)+"RECORD"+ toword(length.types + 2), [ mytype(towords(types_1)+"seq")])
   else if ruleno = // A let W = E // 33 
   then let e = result(subtrees_4)
    let name = code(result(subtrees_2))_1 
    let newdict = dict + symbol(name, mytype."local", empty:seq.mytype, types(e)_1,"")
    bindinfo(newdict, code.e +"define"+ name, types.e)
   else if ruleno = // E A E // 34 
   then let t = code.result(subtrees_1)
    let f = lookup(dict, last.code.result(subtrees_1), empty:seq.mytype)
    assert not.isempty.f report"error"
    bindinfo(dict.result(subtrees_1) - f_1, subseq(t, 1, length.t - 2)+ code.result(subtrees_2)+"SET"+ last.code.result(subtrees_1), types.result(subtrees_2))
   else if ruleno = // E assert E report E E // 35 
   then assert types(result(subtrees_2))_1 = mytype."boolean"report errormessage("condition in assert must be boolean in:", input, place)
    assert types(result(subtrees_4))_1 = mytype."word seq"report errormessage("report in assert must be seq of word in:", input, place)
    let newcode = code.result(subtrees_2)+ code.result(subtrees_5)+ code.result(subtrees_4)+"assertZbuiltinZwordzseq if"
    bindinfo(dict, newcode, types.result(subtrees_5))
   else if ruleno = // E I // 36 
   then result(subtrees_1)
   else if ruleno = // E I.I // 37 
   then let d = decode(code(result(subtrees_3))_2)
    bindinfo(dict,"LIT"+ [ encodeword(decode(code(result(subtrees_1))_2)+ d)]+"LIT"+ countdigits(d, 1, 0)+"makerealZrealZintZint", [ mytype."real"])
   else if ruleno = // T W // 38 
   then result(subtrees_1)
   else if ruleno = // T W.T // 39 
   then bindinfo(dict, code.result(subtrees_3)+ code.result(subtrees_1), types.result(subtrees_1))
   else if ruleno = // E W:T // 40 
   then let f = lookup(dict, merge(code.result(subtrees_1)+":"+ print.mytype.code.result(subtrees_3)), empty:seq.mytype)
    assert not.isempty.f report errormessage("cannot find"+ code.result(subtrees_1)+":"+ print.mytype.code.result(subtrees_3), input, place)
    bindinfo(dict, [ mangledname(f_1)], [ resulttype(f_1)])
   else if ruleno = // E $wordlist // 41 
   then let s = code.result(subtrees_1)
    bindinfo(dict,"WORDS"+ toword.length.s + s, [ mytype."word seq"])
   else if ruleno = // E comment E // 42 
   then let s = code.result(subtrees_1)
    bindinfo(dict, code.result(subtrees_2)+"COMMENT"+ toword.length.s + s, types.result(subtrees_2))
   else if ruleno = // N_// 43 
   then result(subtrees_1)
   else if ruleno = // N-// 44 
   then result(subtrees_1)
   else if ruleno = // N = // 45 
   then result(subtrees_1)
   else if ruleno = // N > // 46 
   then result(subtrees_1)
   else if ruleno = // N * // 47 
   then result(subtrees_1)
   else if ruleno = // N ∧ // 48 
   then result(subtrees_1)
   else if ruleno = // N ∨ // 49 
   then result(subtrees_1)
   else if ruleno = // K W.E // 50 
   then bindinfo(dict, code.result(subtrees_1)+ code.result(subtrees_3), types.result(subtrees_3))
   else if ruleno = // K N.E // 51 
   then bindinfo(dict, code.result(subtrees_1)+ code.result(subtrees_3), types.result(subtrees_3))
   else if ruleno = // K N(L)// 52 
   then bindinfo(dict, code.result(subtrees_1)+ code.result(subtrees_3), types.result(subtrees_3))
   else if ruleno = // K W(L)// 53 
   then bindinfo(dict, code.result(subtrees_1)+ code.result(subtrees_3), types.result(subtrees_3))
   else if ruleno = // K N // 54 
   then bindinfo(dict, code.result(subtrees_1), empty:seq.mytype)
   else if ruleno = // K W // 55 
   then bindinfo(dict, code.result(subtrees_1), empty:seq.mytype)
   else assert ruleno = // E @(K, K, E, E)// 56 report"invalid rule number"+ toword.ruleno 
   apply(result(subtrees_3), result(subtrees_5), result(subtrees_7), result(subtrees_9), input, place)
  let leftsidetoken = [ 32, 33, 33, 33, 33, 33, 33, 40, 35, 35, 
  35, 35, 31, 31, 31, 31, 31, 31, 31, 31, 
  31, 31, 31, 31, 31, 31, 31, 31, 31, 37, 
  37, 31, 30, 31, 31, 31, 31, 17, 17, 31, 
  31, 31, 36, 36, 36, 36, 36, 36, 36, 39, 
  39, 39, 39, 39, 39, 31]_ruleno 
  let actioncode = actiontable_(leftsidetoken + length.tokenlist * stateno.top.newstk)
  assert actioncode > 0 report"??"
  push(newstk, stkele(actioncode, newtree))

