#!/usr/local/bin/tau

Module parse

run mylib test


use deepcopy.seq.lexaction

use format

use mangle



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



Function getheader(s:seq.word)seq.word 
 if length.s < 3 
  then s 
  else 
   let endofname = if s_3 =":"_1 then consumetype(s, 5)else 3 
   let startoftype = if s_endofname ="("_1 then findindex(")"_1, s, endofname + 1)+ 1 else endofname 
   let afterreturntype = consumetype(s, startoftype + 1)
   let aftercomments = consumecomment(s, afterreturntype)
    if aftercomments ≤ length.s ∧ s_aftercomments in"unbound export"
     then s 
     else if aftercomments ≤ length.s ∧ s_aftercomments ="builtin"_1 ∧ last.s ="usemangle"_1 
     then subseq(s, 1, aftercomments - 1)+"usemangle"
     else subseq(s, 1, aftercomments - 1)+"stub"

function consumetype(s:seq.word, i:int)int 
 if i > length.s then i else if s_i ="."_1 then consumetype(s, i + 2)else i

function consumecomment(s:seq.word, i:int)int 
 if i > length.s then i else if s_i ="//"_1 then consumecomment(s, findindex("//"_1, s, i + 1)+ 1)else i

type stepresult is record stk:stack.stkele, place:int, input:seq.word, tokenstate:int, string:seq.word

Function type:stepresult internaltype export

Function type:bindinfo internaltype export

type bindinfo is record dict:set.symbol, code:seq.word, types:seq.mytype

function dict(bindinfo)set.symbol export

function code(bindinfo)seq.word export

function types(bindinfo)seq.mytype export

Function funcparametertypes(t:bindinfo)seq.mytype 
  @(+, parameter, empty:seq.mytype, subseq(types.t, 3, length.types.t))


Function funcname(t:bindinfo)word(towords.(types.t)_1)_1

Function funcreturntype(t:bindinfo)mytype(types.t)_2

function bindinfo(dict:set.symbol, code:seq.word, types:seq.mytype)bindinfo export

type stkele is record stateno:int, result:bindinfo

type lexaction is record w:word, tokenno:int, label:word

function expect(stateno:int)seq.word 
 let l = @(+, kk(stateno),"", arithseq(length.tokenlist, 1, 1))
   toseq(asset.l - asset."-=_^∧ ∨ *")

function kk(stateno:int, token:int)seq.word 
 if 0 ≠ actiontable_(length.tokenlist * stateno + token)then [ tokenlist_token]else empty:seq.word


  

function consumeinput(lextab:seq.lexaction,b:stepresult, next:word)stepresult 
 // assert (input.b)_1="use"_1 &or next in "function segment(  " report "MMM"+[next]+input.b //
 if tokenstate.b ≠ 0 
  then 
   if tokenstate.b = stringtoken 
   then 
    if next ="&quot"_1 
    then BB(stringtoken, bindinfo(dict.result.top.stk.b, string.b, [ mytype."int seq"]), stk.b, place.b, input.b)
    else 
    // add to string // 
    stepresult(stk.b 
    , place.b + 1 
    , input.b 
    , tokenstate.b 
    , string.b + if next = merge.["&"_1,"quot"_1]then"&quot"_1 else next)
   else if tokenstate.b=-1 then
     if next ="'"_1 then
     BB(stringtoken, bindinfo(dict.result.top.stk.b, string.b, [ mytype."int seq"]), stk.b, place.b, input.b)
   else // add to string // stepresult(stk.b, place.b + 1, input.b, tokenstate.b, string.b + next)
   else 
   assert tokenstate.b=commenttoken report "Lex check"
   if next ="//"_1 
   then BB(commenttoken, bindinfo(dict.result.top.stk.b, string.b, [ mytype."int seq"]), stk.b, place.b, input.b)
   else // add to string // stepresult(stk.b, place.b + 1, input.b, tokenstate.b, string.b + next)
  else 
        let lexindex= binarysearch(lextab,lexaction(next,0,next))
    if lexindex < 0 
     then // next is not in lex table //
      let kind=checkinteger(next)
      if kind="WORD"_1 then
      BB(Wtoken, bindinfo(dict.result.top.stk.b, [ next], [ mytype."int"]), stk.b, place.b, input.b)
      else assert kind="INTEGER"_1 report errormessage("Illegal character in Integer",input.b,place.b)
       BB(Itoken 
      , bindinfo(dict.result.top.stk.b, ["LIT"_1, next], [ mytype."int"])
      , stk.b 
      , place.b 
      , input.b)
      else 
     let act=lextab_lexindex
      if tokenno.act = Itoken 
     then BB(tokenno.act 
     , bindinfo(dict.result.top.stk.b, ["LIT"_1, label.act], [ mytype."int"])
     , stk.b 
     , place.b 
     , input.b)
     else 
      if tokenno.act = 0 
     then 
      if next ="&quot"_1 
      then // start word list // stepresult(stk.b, place.b + 1, input.b, stringtoken,"")
      else if next="'"_1 then stepresult(stk.b, place.b + 1, input.b, -1,"")
      else // start comment // stepresult(stk.b, place.b + 1, input.b, commenttoken,"")
     else BB(tokenno.act, bindinfo(dict.result.top.stk.b, [ label.act], [ mytype."int"]), stk.b, place.b, input.b)

function errormessage(message:seq.word, input:seq.word, place:int)seq.word 
 message + prettynoparse.subseq(input, 1, place)

function BB(token:int, tr:bindinfo, stk:stack.stkele, place:int, input:seq.word)stepresult 
 let stateno = stateno.top.stk 
  let actioncode = actiontable_(token + length.tokenlist * stateno)
   if actioncode > 0 
    then stepresult(push(stk, stkele(actioncode, tr)), place + 1, input, 0,"")
    else 
     assert actioncode < 0 
     report"parse error expect:"+ expect.stateno +"got:"+(
      if place > length.input 
      then"end of paragraph"
      else [ input_place]+ // printstate.stateno + // prettynoparse.subseq(input, 1, place))
      let x = reduce(stk,-actioncode, place, input)
        BB(token, bindinfo(dict.result.top.x, code.tr, types.tr), x, place, input)

Function parse(dict:set.symbol, input:seq.word)bindinfo 
 parse(bindinfo(dict,"", empty:seq.mytype), input)

Function parse(b:bindinfo, input:seq.word)bindinfo 
let sortedlex=if length.orderadded.cachelex=0 then    
  let discard=encode(cachelex,sort.lextable)
   (orderadded.cachelex)_1
   else (orderadded.cachelex)_1
 let a = @(consumeinput.sortedlex
  , identity 
  , stepresult(push(empty:stack.stkele, stkele(startstate, b)), 1, input, 0,"")
  , input +"#")
  assert tokenstate.a=0 report
    errormessage("missing ending"+if tokenstate.a=commenttoken then "//" else 
                                  if tokenstate.a=stringtoken then "&quot" else "????",input.a,place.a)
    result.(toseq.stk.a)_2
     

function  ?(a:lexaction,b:lexaction) ordering  w.a ? w.b 

function  =(a:lexaction,b:lexaction) boolean  w.a = w.b 

function hash(l:seq.lexaction) int length.l


use otherseq.lexaction

use blockseq.lexaction

use seq.seq.lexaction

type cachelex is encoding seq.lexaction


   

function opaction(R:reduction)bindinfo 
 let op =(code.R_2)_1 
  let dict = dict.R_1 
  let types = types.R_1 + types.R_3 
  let f = lookupbysig(dict, op, types, input.R, place.R)
   bindinfo(dict, code.R_1 + code.R_3 + mangledname.f, [ resulttype.f])

Function deepcopymangle(type:mytype)word 
 mangle("deepcopy"_1, mytype(towords.type +"deepcopy"), [ mytype."T"])

function unaryop(R:reduction, op:seq.word, exp:bindinfo)bindinfo 
 if op_1 ="process"_1 
  then 
   let nopara = manglednopara.last.code.exp 
   let rt =(types.exp)_1 
   let prt = mytype(towords.rt +"process")
   let newcode = subseq(code.exp, 1, length.code.exp - 1)+"FREF"+ deepcopymangle.rt +"FREF"+ deepcopymangle.mytype."word seq"
   +"FREF"
   + last.code.exp 
   +"LIT"
   + toword.nopara 
   +"PRECORD"
   + toword(nopara + 4)
    bindinfo(dict.R, newcode, [ mytype(towords.rt +"process")])
  else 
   let f = lookupbysig(dict.R, op_1, types.exp, input.R, place.R)
    bindinfo(dict.R, code.exp + mangledname.f, [ resulttype.f])

function apply(term1:bindinfo, term2:bindinfo, term3:bindinfo, term4:bindinfo, input:seq.word, place:int)bindinfo 
 let dict = dict.term1 
  assert abstracttype.(types.term4)_1 ="seq"_1 
  report errormessage("last term of apply must be seq", input, place)
   let sym2types = types.term2 + [ parameter.(types.term4)_1]
    let sym2 = lookupbysig(dict,(code.term2)_1, sym2types, input, place)
    let sym1types = types.term1 + types.term3 + [ resulttype.sym2]
    let sym1 = lookupbysig(dict,(code.term1)_1, sym1types, input, place)
    assert(types.term3)_1 = resulttype.sym1 
    report errormessage("term3 not same as init"+ print.(types.term3)_1 + print.resulttype.sym1, input, place)
     let pseqtype = mytype(towords.parameter.(types.term4)_1 +"pseq"_1)
      let idx = mangle("_"_1 
      , mytype(towords.parameter.(types.term4)_1 +"seq"_1)
      , [ mytype."T pseq", mytype."int"])
      let x = lookupbysig(dict,"_"_1, [ pseqtype, mytype."int"], input, place)
       bindinfo(dict 
       , subseq(code.term1, 2, length.code.term1)+ subseq(code.term2, 2, length.code.term2)+ code.term3 + code.term4 +"FREF"
       + mangledname.sym2 
       +"FREF"
       + mangledname.sym1 
       +"FREF"
       + idx 
       +"APPLY"
       + toword(length.types.term1 + length.types.term2 + 5)
       , types.term3)



function addparameter(orgsize:int, input:seq.word, place:int, dict:set.symbol, m:mytype)set.symbol 
 assert isempty.lookup(dict, abstracttype.m, empty:seq.mytype)∨ abstracttype.m =":"_1 
  report errormessage("duplciate symbol:"+ abstracttype.m, input, place)
   let parano = toword(cardinality.dict - orgsize + 1)
     dict + symbol(abstracttype.m, mytype.[ parano,"para"_1], empty:seq.mytype, parameter.m,"")

function lookupbysig(dict:set.symbol, name:word, paratypes:seq.mytype, input:seq.word, place:int)symbol 
 let f = lookup(dict, name, paratypes)
  assert not.isempty.f 
  report errormessage("cannot find"+ name +"("+ @(seperator(","), print,"", paratypes)+")"
  , input 
  , place)
   assert cardinality.f = 1 report errormessage("found more that one"+ @(+, print2,"", toseq.f), input, place)
     f_1

function backoffcomment(s:seq.word,match:word,i:int) seq.word
  if s_i=match then subseq(s,1,i- 1) else backoffcomment(s,match,i- 1)

function createfunc(R:reduction, funcname:seq.word, paralist:seq.mytype, functypebind:bindinfo, exp:bindinfo
 )bindinfo 
  let dict=dict.R
  let functype=mytype.gettype.functypebind
  assert functype =(types.exp)_1 ∨(types.exp)_1 in [ mytype."internal", mytype."internal1"]
  report errormessage("function type of"+ print.functype +"does not match expression type"+ print.(types.exp)_1 
  , input.R 
  , place.R)
    let i=toint((code.functypebind)_1)
    let header= if (input.R)_i in "// &quot"  then backoffcomment((input.R),(input.R)_i,i- 1) else 
     subseq((input.R),1,i- 1)
    let newcode="parsedfunc"+ toword.length.header + header+ code.exp
    bindinfo(dict, newcode, [ mytype.funcname, functype]+ paralist)
    
     

function isdefined(R:reduction, typ:seq.word)bindinfo 
 let dict=dict.R
 if cardinality.dict < 25 ∨ typ in ["T","int"]  &or subseq(typ,1,1)="T"
  then bindinfo(dict, [toword.place.R], [ mytype.typ])
  else 
   let a = lookup(dict, merge("type:"+ print.mytype.typ), empty:seq.mytype)
   assert cardinality.a = 1 ∨ print.mytype.typ in ["?"]
   report errormessage("parameter type"+ print.mytype.typ +"is undefined in"
   , // + @(+, print,"", toseq.dict), // input.R 
   , place.R)
    bindinfo(dict, [toword.place.R], [ mytype.typ])

function gettype(b:bindinfo)seq.word towords.(types.b)_1

function Wtoken int // generated by genlex module in tools // 34 

function Itoken int // generated by genlex module in tools // 38 

function commenttoken int // generated by genlex module in tools // 11 

function stringtoken int // generated by genlex module in tools // 28 

function lextable seq.lexaction // generated by genlex module in tools // [ lexaction("N"_1, 34,"N"_1) 
, lexaction("("_1, 3,"("_1) 
, lexaction("}"_1, 10,"}"_1) 
, lexaction("function"_1, 34,"function"_1) 
, lexaction("//"_1, 0,"//"_1) 
, lexaction("]"_1, 7,"]"_1) 
, lexaction("I"_1, 34,"I"_1) 
, lexaction("F"_1, 34,"F"_1) 
, lexaction("use"_1, 34,"use"_1) 
, lexaction("#"_1, 19,"#"_1) 
, lexaction("≠"_1, 6,"≠"_1) 
, lexaction("+"_1, 8,"+"_1) 
, lexaction("_"_1, 14,"_"_1) 
, lexaction("&quot"_1, 0,"&quot"_1) 
,lexaction(" ' "_1, 0,"& ' "_1) 
, lexaction(merge("&"+"ne"), 6,"≠"_1) 
, lexaction("@"_1, 29,"@"_1) 
, lexaction("P"_1, 34,"P"_1) 
, lexaction("else"_1, 21,"else"_1) 
, lexaction("i"_1, 34,"i"_1) 
, lexaction("∩"_1, 27,"∩"_1) 
, lexaction(")"_1, 4,")"_1) 
, lexaction("*"_1, 27,"*"_1) 
, lexaction("FP"_1, 34,"FP"_1) 
, lexaction("Function"_1, 34,"Function"_1) 
, lexaction(","_1, 12,","_1) 
, lexaction(merge("&"+"cap"), 27,"∩"_1) 
, lexaction("inst"_1, 34,"inst"_1) 
, lexaction("W"_1, 34,"W"_1) 
, lexaction("A"_1, 34,"A"_1) 
, lexaction("$wordlist"_1, 34,"$wordlist"_1) 
, lexaction("is"_1, 16,"is"_1) 
, lexaction("assert"_1, 23,"assert"_1) 
, lexaction(merge("&"+"and"), 25,"∧"_1) 
, lexaction("K"_1, 34,"K"_1) 
, lexaction(merge("&"+"ge"), 6,"≥"_1) 
, lexaction("report"_1, 24,"report"_1) 
, lexaction("∧"_1, 25,"∧"_1) 
, lexaction(":"_1, 5,":"_1) 
, lexaction("{"_1, 9,"{"_1) 
, lexaction("mod"_1, 27,"mod"_1) 
, lexaction(merge("&"+"or"), 26,"∨"_1) 
, lexaction(merge("&"+"contains"), 8,"∋"_1) 
, lexaction("then"_1, 20,"then"_1) 
, lexaction("≤"_1, 6,"≤"_1) 
, lexaction("∪"_1, 27,"∪"_1) 
, lexaction("/"_1, 27,"/"_1) 
, lexaction(">>"_1, 6,">>"_1) 
, lexaction("-"_1, 8,"-"_1) 
, lexaction("L"_1, 34,"L"_1) 
, lexaction("∨"_1, 26,"∨"_1) 
, lexaction(merge("&"+"in"), 8,"∈"_1) 
, lexaction("a"_1, 34,"a"_1) 
, lexaction("<"_1, 6,"<"_1) 
, lexaction("E"_1, 34,"E"_1) 
, lexaction(">"_1, 6,">"_1) 
, lexaction("word"_1, 34,"word"_1) 
, lexaction("seq"_1, 34,"seq"_1) 
, lexaction(merge("&"+"le"), 6,"≤"_1) 
, lexaction("^"_1, 14,"^"_1) 
, lexaction("in"_1, 8,"in"_1) 
, lexaction("∈"_1, 8,"∈"_1) 
, lexaction("comment"_1, 34,"comment"_1) 
, lexaction("="_1, 2,"="_1) 
, lexaction("if"_1, 18,"if"_1) 
, lexaction("["_1, 13,"["_1) 
, lexaction(merge("&"+"cup"), 27,"∪"_1) 
, lexaction("."_1, 1,"."_1) 
, lexaction("G"_1, 34,"G"_1) 
, lexaction("let"_1, 22,"let"_1) 
, lexaction("0"_1, 38,"0"_1) 
, lexaction("?"_1, 6,"?"_1) 
, lexaction("∋"_1, 8,"∋"_1) 
, lexaction("T"_1, 34,"T"_1) 
, lexaction("<<"_1, 6,"<<"_1) 
, lexaction("≥"_1, 6,"≥"_1) 
, lexaction("int"_1, 34,"int"_1) 
, lexaction("mytype"_1, 34,"mytype"_1) 
, lexaction(". "_1, 41,". "_1) 
, lexaction("2"_1, 38,"2"_1) 
, lexaction("empty"_1, 34,"empty"_1)]

noactions 2303 
nosymbols:40 alphabet:.=():>]-{ } comment, [_^is T if # then else let assert report ∧ ∨ * $wordlist @ A E G F W P N L I K FP 
norules 60 
nostate 159 
follow N >(N >, N >.(> N(>((> I(>_(> @(> P(> *(> FP(> W(> A(> $wordlist(> assert(> K(> ∧(> {(>-(> L(> ∨(> E(> >(> comment(> =(> if(> [(> let(> T } > N } >(} > } } >]} > I } > # } >_} > @ } > else } >)} > * } >, } > W } > A } > $wordlist } > assert } > report } > ∧ } > { } > then } >-} > ∨ } > E } > > } >^} > comment } > = } > if } > [ } > let]> N]>(]> }]>]]> I]> #]>_]> @]> else]>)]> *]>,]> W]> A]> $wordlist]> assert]> report]> ∧]> {]> then]>-]> ∨]> E]> >]>^]> comment]> =]> if]> []> let I > N I >(I > } I >]I > I I > # I >_I > @ I > else I >)I > * I >, I > W I > A I > $wordlist I > assert I > report I > ∧ I > { I > then I >-I > ∨ I > E I > > I >^I > comment I > = I > if I > [ I >.I > let F > #_> N_>(_> I_>__> @_> *_>,_> W_> A_> $wordlist_> assert_> ∧_> {_>-_> ∨_> E_> >_> comment_> =_> if_> [_>._> let @ >(P > # P >)P >, else > N else >(else > I else >_else > @ else > * else > W else > A else > $wordlist else > assert else > ∧ else > { else >-else > ∨ else > E else > > else > comment else > = else > if else > [ else > let)> N)>()> })>])> I)> #)>_)> @)> else)>))> *)>,)> W)> A)> $wordlist)> assert)> report)> ∧)> {)> then)>-)> ∨)> E)> >)>^)> comment)> =)> if)> [)> let)> T * > N * >(* > I * >_* > @ * > * * >, * > W * > A * > $wordlist * > assert * > ∧ * > { * >-* > ∨ * > E * > > * > comment * > = * > if * > [ * >.* > let FP >), > N, >(, > I, >_, > @, > *, > W, > A, > $wordlist, > assert, > K, > ∧, > {, >-, > ∨, > E, > >, > comment, > =, > if, > [, > let, > T W > N W >(W > } W >]W > I W > # W >_W > @ W > P W > else W >)W > * W >, W > W W > A W > $wordlist W > is W > assert W > report W > ∧ W >:W > { W > then W >-W > ∨ W > E W > > W >^W > comment W > = W > if W > [ W >.W > let W > T A > N A >(A > I A >_A > @ A > * A > W A > A A > $wordlist A > assert A > ∧ A > { A >-A > ∨ A > E A > > A > comment A > = A > if A > [ A > let $wordlist > N $wordlist >($wordlist > } $wordlist >]$wordlist > I $wordlist > # $wordlist >_$wordlist > @ $wordlist > else $wordlist >)$wordlist > * $wordlist >, $wordlist > W $wordlist > A $wordlist > $wordlist $wordlist > assert $wordlist > report $wordlist > ∧ $wordlist > { $wordlist > then $wordlist >-$wordlist > ∨ $wordlist > E $wordlist > > $wordlist >^$wordlist > comment $wordlist > = $wordlist > if $wordlist > [ $wordlist > let is > W assert > N assert >(assert > I assert >_assert > @ assert > * assert > W assert > A assert > $wordlist assert > assert assert > ∧ assert > { assert >-assert > ∨ assert > E assert > > assert > comment assert > = assert > if assert > [ assert > let K >, report > N report >(report > I report >_report > @ report > * report > W report > A report > $wordlist report > assert report > ∧ report > { report >-report > ∨ report > E report > > report > comment report > = report > if report > [ report > let ∧ > N ∧ >(∧ > I ∧ >_∧ > @ ∧ > * ∧ >, ∧ > W ∧ > A ∧ > $wordlist ∧ > assert ∧ > ∧ ∧ > { ∧ >-∧ > ∨ ∧ > E ∧ > > ∧ > comment ∧ > = ∧ > if ∧ > [ ∧ >.∧ > let:> W:> T { > N { >({ > I { >_{ > @ { > * { > W { > A { > $wordlist { > assert { > ∧ { > { { >-{ > ∨ { > E { > > { > comment { > = { > if { > [ { > let then > N then >(then > I then >_then > @ then > * then > W then > A then > $wordlist then > assert then > ∧ then > { then >-then > ∨ then > E then > > then > comment then > = then > if then > [ then > let-> N->(-> I->_-> @-> *->,-> W-> A-> $wordlist-> assert-> ∧-> {->--> ∨-> E-> >-> comment-> =-> if-> [->.-> let L >]L >)L >, ∨ > N ∨ >(∨ > I ∨ >_∨ > @ ∨ > * ∨ >, ∨ > W ∨ > A ∨ > $wordlist ∨ > assert ∨ > ∧ ∨ > { ∨ >-∨ > ∨ ∨ > E ∨ > > ∨ > comment ∨ > = ∨ > if ∨ > [ ∨ >.∨ > let E > N E >(E > } E >]E > I E > # E >_E > @ E > else E >)E > * E >, E > W E > A E > $wordlist E > assert E > report E > ∧ E > { E > then E >-E > ∨ E > E E > > E >^E > comment E > = E > if E > [ E > let > > N > >(> > I > >_> > @ > > * > >, > > W > > A > > $wordlist > > assert > > ∧ > > { > >-> > ∨ > > E > > > > > comment > > = > > if > > [ > >.> > let^> N^>(^> I^>_^> @^> *^> W^> A^> $wordlist^> assert^> ∧^> {^>-^> ∨^> E^> >^> comment^> =^> if^> [^> let comment > N comment >(comment > I comment >_comment > @ comment > * comment > W comment > A comment > $wordlist comment > assert comment > ∧ comment > { comment >-comment > ∨ comment > E comment > > comment > comment comment > = comment > if comment > [ comment > let = > N = >(= > I = >_= > @ = > * = >, = > W = > A = > $wordlist = > assert = > ∧ = > { = >-= > ∨ = > E = > > = > comment = > = = > if = > [ = >.= > let if > N if >(if > I if >_if > @ if > * if > W if > A if > $wordlist if > assert if > ∧ if > { if >-if > ∨ if > E if > > if > comment if > = if > if if > [ if > let [ > N [ >([ > I [ >_[ > @ [ > * [ > W [ > A [ > $wordlist [ > assert [ > ∧ [ > { [ >-[ > L [ > ∨ [ > E [ > > [ > comment [ > = [ > if [ > [ [ > let.> N.>(.> I.>_.> @.> *.> W.> A.> $wordlist.> assert.> ∧.> {.>-.> ∨.> E.> >.> comment.> =.> if.> [.> let.> T let > W T > N T >(T > } T >]T > I T > # T >_T > @ T > else T >)T > * T >, T > W T > A T > $wordlist T > assert T > report T > ∧ T > { T > then T >-T > ∨ T > E T > > T >^T > comment T > = T > if T > [ T > let T > T 

function tokenlist seq.word".=():>]-{ } comment, [_^is T if # then else let assert report ∧ ∨ * $wordlist @ A E G F W P N L I K FP" 

function startstate int 1 

function actiontable seq.int [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 12, 0, 10, 0, 0, 0, 0, 0, 6, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 9, 11, 7, 0, 0, 0, 0, 0, 0, 8, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -47, 0, -47, 0, 0, 0, 0, 0, 0, 0, 0, -47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -51, 0, -51, 0, 0, 0, 0, 0, 0, 0, 0, -51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, -42, 16, -42, 19, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 18, 21, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, 0, 17, 0, -42, 0, -42, 0, 0, -52, 0, -52, 0, 0, 0, 0, 0, 0, 0, 0, -52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -48, 0, -48, 0, 0, 0, 0, 0, 0, 0, 0, -48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -53, 0, -53, 0, 0, 0, 0, 0, 0, 0, 0, -53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -50, 0, -50, 0, 0, 0, 0, 0, 0, 0, 0, -50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -49, 0, -49, 0, 0, 0, 0, 0, 0, 0, 0, -49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 22, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 22, 0, 0, 0, 0, 27, 20, -42, -42, -42, 0, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, 0, -42, 0, -42, 0, -42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 41, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, -42, -42, -42, 48, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, 0, -42, 0, -42, 0, -42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 51, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, -43, -43, -43, 0, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, 0, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, 0, 0, -43, 0, -43, 0, -43, 0, 0, 55, 0, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 56, 0, 0, 35, 0, 31, 0, 33, 0, 0, 57, -40, -40, -40, 0, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, 0, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, 0, -40, 0, -40, 0, -40, 0, 0, 0, 0, 58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61, -16, 59, -16, 60, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, 0, 0, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, 0, 0, -16, 0, -16, 0, -16, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 62, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, -45, -45, -45, 0, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, 0, 0, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, 0, 0, -45, 0, -45, 0, -45, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 63, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 64, 0, 0, 35, 0, 31, 0, 33, 0, 0, -48, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, -48, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 65, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 73, 0, 0, 0, 71, 0, 69, 0, 0, 0, 0, 0, 66, 72, 0, 0, 0, -4, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 74, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 75, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 77, 0, 0, 35, 0, 31, 76, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 22, 0, 0, 0, 0, 86, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 87, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 77, 0, 0, 35, 0, 31, 88, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 89, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 73, 0, 90, 0, 71, 0, 69, 0, 0, 0, 0, 0, 66, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 91, 0, 0, 0, 13, 0, 0, 0, 12, 0, 10, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 11, 7, 0, 0, 0, 0, 0, 0, 93, 0, 92, 0, 0, 94, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 77, 0, 0, 35, 0, 31, 95, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 97, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 73, -38, -38, 0, 71, -38, 69, -38, -38, -38, -38, -38, 66, 72, 0, 0, -38, -38, -38, -38, -38, -38, -38, 68, 70, 67, -38, -38, -38, -38, 0, 0, -38, 0, -38, 0, -38, 0, 0, 0, 73, 0, 0, 0, 71, 0, 69, 0, 0, 0, 0, 0, 66, 72, 0, 0, 0, 0, 0, 0, 0, 0, 98, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 71, 0, 69, 0, 99, 0, 0, 0, 66, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -25, -25, -25, 0, -25, -25, -25, -25, -25, -25, -25, -25, 66, 72, 0, 0, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, -25, 0, 0, -25, 0, -25, 0, -25, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 100, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 101, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 102, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 103, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 104, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 105, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 106, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 107, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, -46, -46, -46, 0, -46, -46, -46, -46, -46, -46, -46, -46, 66, 72, 0, 0, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, 0, 0, -46, 0, -46, 0, -46, 0, 0, 0, 73, 0, 0, 0, 71, 0, 69, 0, 0, 0, 0, 0, 66, 72, 0, 0, 0, 0, 108, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 109, 0, 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, -34, 0, 71, -34, 69, 0, 0, 0, -34, 0, 66, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 111, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, -42, -42, -42, 112, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, 0, -42, 0, -42, 0, -42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 113, 0, 0, 0, 0, 0, 0, 0, 0, 0, -11, 0, 0, 0, 0, 0, 0, 0, -11, 0, 0, 0, 0, 0, 0, -11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 114, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 115, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 116, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 0, 0, 117, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 71, 0, 69, 0, 0, 0, 0, 0, 66, 72, 0, 0, 0, -5, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 118, 0, 0, 0, 0, 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -27, -27, -27, 0, -27, -27, -27, -27, -27, -27, -27, -27, 66, 72, 0, 0, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, -27, 0, 0, -27, 0, -27, 0, -27, 0, 0, 0, -20, -20, -20, 0, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, 0, 0, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, 0, 0, -20, 0, -20, 0, -20, 0, 0, 0, -41, -41, -41, 0, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, 0, 0, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, 0, 0, -41, 0, -41, 0, -41, 0, 0, 120, 0, 119, 0, 0, 0, 0, 0, 0, 0, 0, -58, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 122, 0, 121, 0, 0, 0, 0, 0, 0, 0, 0, -59, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 123, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -44, 125, -44, 0, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, 0, 0, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, 0, 0, -44, 0, -44, 0, -44, 0, 0, 0, -26, -26, -26, 0, -26, -26, -26, -26, -26, -26, -26, -26, 66, 72, 0, 0, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, -26, 0, 0, -26, 0, -26, 0, -26, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 126, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, -21, -21, -21, 0, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, 0, 0, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, 0, 0, -21, 0, -21, 0, -21, 0, 0, 0, -24, -24, -24, 0, -24, -24, -24, -24, -24, -24, -24, -24, -24, 72, 0, 0, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, -24, 0, 0, -24, 0, -24, 0, -24, 0, 0, 0, -28, -28, -28, 0, -28, -28, -28, -28, -28, -28, -28, -28, 66, 72, 0, 0, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28, -28, 0, 0, -28, 0, -28, 0, -28, 0, 0, 0, 73, -32, -32, 0, 71, -32, 69, -32, -32, -32, -32, -32, 66, 72, 0, 0, -32, -32, -32, -32, -32, -32, -32, -32, -32, 67, -32, -32, -32, -32, 0, 0, -32, 0, -32, 0, -32, 0, 0, 0, -29, -29, -29, 0, -29, -29, -29, -29, -29, -29, -29, -29, 66, 72, 0, 0, -29, -29, -29, -29, -29, -29, -29, -29, -29, 67, -29, -29, -29, -29, 0, 0, -29, 0, -29, 0, -29, 0, 0, 0, 73, -33, -33, 0, 71, -33, 69, -33, -33, -33, -33, -33, 66, 72, 0, 0, -33, -33, -33, -33, -33, -33, -33, 68, -33, 67, -33, -33, -33, -33, 0, 0, -33, 0, -33, 0, -33, 0, 0, 0, -31, -31, -31, 0, -31, -31, 69, -31, -31, -31, -31, -31, 66, 72, 0, 0, -31, -31, -31, -31, -31, -31, -31, -31, -31, 67, -31, -31, -31, -31, 0, 0, -31, 0, -31, 0, -31, 0, 0, 0, 73, -23, -23, 0, 71, -23, 69, -23, -23, -23, -23, -23, 66, 72, 0, 0, -23, -23, -23, -23, -23, -23, -23, 68, 70, 67, -23, -23, -23, -23, 0, 0, -23, 0, -23, 0, -23, 0, 0, 0, -30, -30, -30, 0, -30, -30, 69, -30, -30, -30, -30, -30, 66, 72, 0, 0, -30, -30, -30, -30, -30, -30, -30, -30, -30, 67, -30, -30, -30, -30, 0, 0, -30, 0, -30, 0, -30, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 127, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, -36, -36, -36, 0, -36, -36, -36, -36, -36, -36, -36, -36, -36, -36, 0, 0, -36, -36, -36, -36, -36, -36, -36, -36, -36, -36, -36, -36, -36, -36, 0, 0, -36, 0, -36, 0, -36, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 128, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 129, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 130, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 131, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 71, 0, 69, 0, 0, 0, 0, 0, 66, 72, 0, 0, 0, -3, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -14, 0, 0, 0, 0, 0, 0, 0, -14, 0, 0, 0, 0, 0, 0, -14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 71, 0, 69, 0, 0, 0, 0, 0, 66, 72, 0, 0, 0, -2, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 132, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, -17, -17, -17, 0, -17, -17, -17, -17, -17, -17, -17, -17, -17, -17, 0, 0, -17, -17, -17, -17, -17, -17, -17, -17, -17, -17, -17, -17, -17, -17, 0, 0, -17, 0, -17, 0, -17, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 77, 0, 0, 35, 0, 31, 133, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 134, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 77, 0, 0, 35, 0, 31, 135, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 136, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 0, 0, 0, 12, 0, 10, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 11, 7, 0, 0, 0, 0, 0, 0, 93, 0, 92, 0, 0, 137, 0, 0, -18, -18, -18, 0, -18, -18, -18, -18, -18, -18, -18, -18, -18, -18, 0, 0, -18, -18, -18, -18, -18, -18, -18, -18, -18, -18, -18, -18, -18, -18, 0, 0, -18, 0, -18, 0, -18, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 77, 0, 0, 35, 0, 31, 138, 33, 0, 0, 0, 146, 32, 0, 0, 145, 0, 142, 39, 0, 42, 0, 44, 139, 72, 0, 0, 43, 0, 0, 0, 45, 38, 0, 141, 143, 140, 37, 34, 36, 144, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 73, 0, 0, 0, 71, 0, 69, 0, 0, 0, 0, 0, 66, 72, 0, 0, 0, 0, 0, 147, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, -35, 0, 71, -35, 69, 0, 0, 0, -35, 0, 66, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, -37, 0, 0, 71, 0, 69, -37, 0, -37, 0, -37, 66, 72, 0, 0, -37, 0, 0, 0, -37, -37, 0, 68, 70, 67, -37, -37, -37, -37, 0, 0, -37, 0, -37, 0, -37, 0, 0, 0, 0, 0, -13, 0, 0, 0, 0, 0, 0, 0, -13, 0, 0, 0, 0, 0, 0, -13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 148, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 149, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 0, 0, 150, 0, 0, 0, 0, 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 71, 0, 69, 0, 0, 0, -55, 0, 66, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 151, 0, 0, 0, 0, 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 71, 0, 69, 0, 0, 0, -54, 0, 66, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 153, 0, 0, 0, 0, 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -47, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, -47, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 100, 0, 0, 35, 0, 31, 0, 33, 0, 0, -51, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, -51, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 101, 0, 0, 35, 0, 31, 0, 33, 0, 0, -52, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, -52, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 102, 0, 0, 35, 0, 31, 0, 33, 0, 0, -48, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, -48, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 154, 0, 0, 35, 0, 31, 0, 33, 0, 0, -53, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, -53, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 104, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 73, -39, -39, 0, 71, -39, 69, -39, -39, -39, -39, -39, 66, 72, 0, 0, -39, -39, -39, -39, -39, -39, -39, 68, 70, 67, -39, -39, -39, -39, 0, 0, -39, 0, -39, 0, -39, 0, 0, -50, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, -50, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 105, 0, 0, 35, 0, 31, 0, 33, 0, 0, -49, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, -49, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 107, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 155, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 0, 0, -15, 0, 0, 0, 0, 0, 0, 0, -15, 0, 0, 0, 0, 0, 0, -15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 71, 0, 69, 0, 0, 0, 0, 0, 66, 72, 0, 0, 0, -6, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 156, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, -19, -19, -19, 0, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, 0, 0, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, 0, 0, -19, 0, -19, 0, -19, 0, 0, 0, -29, -29, -29, 0, -29, -29, -29, -29, -29, -29, -29, -29, 66, 72, 0, 0, -29, -29, -29, -29, -29, -29, -29, -29, -29, -25, -29, -29, -29, -29, 0, 0, -29, 0, -29, 0, -29, 0, 0, 0, 73, -22, -22, 0, 71, -22, 69, -22, -22, -22, -22, -22, 66, 72, 0, 0, -22, -22, -22, -22, -22, -22, -22, 68, 70, 67, -22, -22, -22, -22, 0, 0, -22, 0, -22, 0, -22, 0, 0, 0, 73, 0, 0, 0, 71, 0, 69, 0, 0, 0, 157, 0, 66, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 32, 0, 0, 12, 0, 40, 39, 0, 42, 0, 44, 6, 0, 0, 0, 43, 0, 0, 0, 45, 38, 0, 9, 11, 7, 37, 34, 36, 158, 0, 0, 35, 0, 31, 0, 33, 0, 0, 0, 73, 0, 159, 0, 71, 0, 69, 0, 0, 0, 0, 0, 66, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 70, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -60, -60, -60, 0, -60, -60, -60, -60, -60, -60, -60, -60, -60, -60, 0, 0, -60, -60, -60, -60, -60, -60, -60, -60, -60, -60, -60, -60, -60, -60, 0, 0, -60, 0, -60, 0, -60] 

function   _(r:reduction,n:int) bindinfo result.(toseq.r)_n


type reduction is record toseq:seq.stkele,input:seq.word,place:int

function   dict(r:reduction)  set.symbol dict.result.last.toseq.r



function reduce(stk:stack.stkele, ruleno:int, place:int, input:seq.word)stack.stkele // generated function // 
let rulelen = [ 2, 7, 7, 4, 6, 9, 5, 2, 1, 1, 3, 3, 5, 4, 6, 1, 4, 4, 6, 3, 3, 6, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 4, 2, 5, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 1, 10]_ruleno 
let newstk = pop(stk, rulelen) 
let R = reduction(top(stk, rulelen),input,place) 
let newtree = 
if ruleno = // G F # // 1 then R_1 else 
if ruleno = // F W W(FP)T E // 2 then createfunc(R,code.R_2, types.R_4, R_6, R_7)else 
if ruleno = // F W N(FP)T E // 3 then createfunc(R, code.R_2, types.R_4,R_6, R_7)else 
if ruleno = // F W W T E // 4 then  createfunc(R, code.R_2, empty:seq.mytype, R_3, R_4)else 
if ruleno = // F W W:T T E // 5 then 
let name = [ merge(code.R_2 +":"+ print.mytype.gettype.R_4)]createfunc(R, name, empty:seq.mytype,R_5, R_6)else 
if ruleno = // F W W:T(FP)T E // 6 then 
let name = [ merge(code.R_2 +":"+ print.mytype.gettype.R_4)]createfunc(R, name, types.R_6, R_8, R_9)else 
if ruleno = // F W W is W P // 7 then assert(code.R_4)_1 in"record encoding sequence"report errormessage("Expected record encoding or sequence after is in type definition got:"+ code.R_4, input, place)bindinfo(dict.R, code.R_4 + code.R_2 + code.R_5, types.R_5)else 
if ruleno = // F W T // 8 then // use clause // bindinfo(dict.R, gettype.R_2, empty:seq.mytype)else 
if ruleno = // FP P // 9 then bindinfo(@(addparameter(cardinality.dict.R, input, place), identity, dict.R, types.R_1),"", types.R_1)else 
if ruleno = // P T // 10 then bindinfo(dict.R,"", [ mytype(gettype.R_1 +":")])else 
if ruleno = // P P, T // 11 then bindinfo(dict.R,"", types.R_1 + [ mytype(gettype.R_3 +":")])else 
if ruleno = // P W:T // 12 then bindinfo(dict.R, code.R_1 + code.R_3, [ mytype(gettype.R_3 + code.R_1)])else 
if ruleno = // P P, W:T // 13 then bindinfo(dict.R, code.R_1 + code.R_3 + code.R_5, types.R_1 + [ mytype(gettype.R_5 + code.R_3)])else 
if ruleno = // P comment W:T // 14 then bindinfo(dict.R,"//"+ code.R_1 +"//"+ code.R_2 + code.R_4, [ mytype(gettype.R_4 + code.R_2)])else 
if ruleno = // P P, comment W:T // 15 then bindinfo(dict.R,"//"+ code.R_3 +"//"+ code.R_1 + code.R_4 + code.R_6, types.R_1 + [ mytype(gettype.R_6 + code.R_4)])else 
if ruleno = // E W // 16 then 
let id = code.R_1 
let f = lookupbysig(dict.R, id_1, empty:seq.mytype, input, place)bindinfo(dict.R, [ mangledname.f], [ resulttype.f])else 
if ruleno = // E N(L)// 17 then unaryop(R,code.R_1, R_3 )else 
if ruleno = // E W(L)// 18 then unaryop(R,code.R_1, R_3 )else 
if ruleno = // E W:T(L)// 19 then 
let name = [ merge(code.R_1 +":"+ print.(types.R_3)_1)] unaryop(R, name, R_5 )else 
if ruleno = // E(E)// 20 then R_2 else 
if ruleno = // E { E } // 21 then R_2 else 
if ruleno = // E if E then E else E // 22 then 
let thenpart = R_4 assert(types.R_2)_1 = mytype."boolean"report errormessage("cond of if must be boolean", input, place)assert(types.R_4)=(types.R_6)report errormessage("then and else types are different", input, place)
let newcode = code.R_2 + code.R_4 + code.R_6 bindinfo(dict.R, newcode +"if", types.thenpart)else 
if ruleno = // E E^E // 23 then opaction(R)else 
if ruleno = // E E_E // 24 then opaction(R)else 
if ruleno = // E-E // 25 then unaryop(R, code.R_1, R_2)else 
if ruleno = // E W.E // 26 then unaryop(R, code.R_1, R_3)else 
if ruleno = // E N.E // 27 then unaryop(R, code.R_1, R_3)else 
if ruleno = // E E * E // 28 then opaction(R)else 
if ruleno = // E E-E // 29 then opaction(R)else 
if ruleno = // E E = E // 30 then opaction(R)else 
if ruleno = // E E > E // 31 then opaction(R)else 
if ruleno = // E E ∧ E // 32 then opaction(R)else 
if ruleno = // E E ∨ E // 33 then opaction(R)else 
if ruleno = // L E // 34 then R_1 else 
if ruleno = // L L, E // 35 then bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3)else 
if ruleno = // E [ L]// 36 then 
let types = types(R_2)assert @(&and, =(types_1), true, types)report errormessage("types do not match in build", input, place)bindinfo(dict.R,"LIT 0 LIT"+ toword.(length.types)+ code.R_2 +"RECORD"+ toword.(length.types + 2), [ mytype(towords(types_1)+"seq")])else 
if ruleno = // A let W = E // 37 then 
let e = R_4 
let name =(code.R_2)_1 assert isempty.lookup(dict.R, name, empty:seq.mytype)report errormessage("duplicate symbol:"+ name, input, place)
let newdict = dict.R + symbol(name, mytype("local"), empty:seq.mytype,(types.e)_1,"")bindinfo(newdict, code.e +"define"+ name, types.e)else 
if ruleno = // E A E // 38 then 
let t = code.R_1 
let f = lookup(dict.R, last.code.R_1, empty:seq.mytype)assert not(isempty.f)report"internal error/could not find local symbol to delete from dict with name"+ last(code.R_1)bindinfo(dict.R_1-f_1, subseq(t, 1, length.t- 2)+ code.R_2 +"SET"+ last.code.R_1, types.R_2)else 
if ruleno = // E assert E report E E // 39 then assert types(R_2)_1 = mytype."boolean"report errormessage("condition in assert must be boolean in:", input, place)assert types(R_4)_1 = mytype."word seq"report errormessage("report in assert must be seq of word in:", input, place)
let newcode = code.R_2 + code.R_5 + code.R_4 +"assertZbuiltinZwordzseq if"bindinfo(dict.R, newcode, types.R_5)else 
if ruleno = // E I // 40 then R_1 else 
if ruleno = // E I.I // 41 then 
bindinfo(dict.R,"WORDS 3" +[(code.R_1)_2,"."_1,(code.R_3)_2]+"makerealZUTF8Zwordzseq", [ mytype."real"]) else 
if ruleno = // T W // 42 then isdefined(R, code.R_1 )else 
if ruleno = // T W.T // 43 then isdefined(R, towords.(types.R_3)_1 + code.R_1 )else 
if ruleno = // E W:T // 44 then 
let f = lookup(dict.R, merge(code.R_1 +":"+ print((types.R_3)_1)), empty:seq.mytype)assert not.isempty.f report errormessage("cannot find"+ code.R_1 +":"+ print.mytype.code.R_3, input, place)bindinfo(dict.R, [ mangledname.f_1], [ resulttype.f_1])else 
if ruleno = // E $wordlist // 45 then 
let s = code.R_1 bindinfo(dict.R,"WORDS"+ toword.length.s + s, [ mytype."word seq"])else 
if ruleno = // E comment E // 46 then 
let s = code.R_1 bindinfo(dict.R, code.R_2 +"COMMENT"+ toword.length.s + s, types.R_2)else 
if ruleno = // N_// 47 then R_1 else 
if ruleno = // N-// 48 then R_1 else 
if ruleno = // N = // 49 then R_1 else 
if ruleno = // N > // 50 then R_1 else 
if ruleno = // N * // 51 then R_1 else 
if ruleno = // N &and // 52 then R_1 else 
if ruleno = // N &or // 53 then R_1 else 
if ruleno = // K W.E // 54 then bindinfo(dict.R, code.R_1 + code.R_3, types.R_3)else 
if ruleno = // K N.E // 55 then bindinfo(dict.R, code.R_1 + code.R_3, types.R_3)else 
if ruleno = // K N(L)// 56 then bindinfo(dict.R, code.R_1 + code.R_3, types.R_3)else 
if ruleno = // K W(L)// 57 then bindinfo(dict.R, code.R_1 + code.R_3, types.R_3)else 
if ruleno = // K N // 58 then bindinfo(dict.R, code.R_1, empty:seq.mytype)else 
if ruleno = // K W // 59 then bindinfo(dict.R, code.R_1, empty:seq.mytype)else 
assert ruleno = // E @(K, K, E, E)// 60 report"invalid rule number"+ toword.ruleno 
apply(R_3, R_5, R_7, R_9, input, place) 
let leftsidetoken = [ 32, 33, 33, 33, 33, 33, 33, 33, 40, 35, 35, 35, 35, 35, 35, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 37, 37, 31, 30, 31, 31, 31, 31, 17, 17, 31, 31, 31, 36, 36, 36, 36, 36, 36, 36, 39, 39, 39, 39, 39, 39, 31]_ruleno 
let actioncode = actiontable_(leftsidetoken + length.tokenlist * stateno.top.newstk) 
assert actioncode > 0 report"????" 
push(newstk, stkele(actioncode, newtree))
