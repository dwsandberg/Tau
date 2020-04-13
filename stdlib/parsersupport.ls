#!/usr/local/bin/tau

run newpretty test1

Module parsersupport.T

use stdlib

use otherseq.token.T

use stack.stkele.T

use seq.token.T

use format

use seq.stkele.T

type token is record w:word, tokenno:int,  attribute:T

type stkele is record stateno:int,place:int, attribute:T

 type reduction is record toseq:seq.stkele.T
 
 Function type:reduction.T internaltype export  
 
 Function type:token.T internaltype export  
 
 
Function attribute:T(seq.word) T  unbound

Function action(int, seq.token.T,reduction.T) T unbound

Function text(T) seq.word unbound

Function text(t:token.T) seq.word text.attribute.t

Function ?(a:token.T, b:token.T)ordering w.a ? w.b 

Function =(a:token.T, b:token.T)boolean w.a = w.b

Function_(r:reduction.T, n:int) T  attribute.(toseq.r)_n 

Function last(r:reduction.T) T attribute.(toseq.r)_length.toseq.r 

Function errormessage(message:seq.word,input:seq.token.T,place:int) seq.word
message + "&br" +prettynoparse.@(+,text,"",subseq(input,1,place))


  function tokenstream(lextab:seq.token.T, input:seq.word, i:int,  result:seq.token.T) seq.token.T
     if i > length.input then result
     else  
      let next=input_i
     let lexindex = binarysearch(lextab, token(next, 0, attribute:T("")))
   if lexindex < 0 then 
   // next is not in lex table // 
    let kind = checkinteger.next 
     if kind = "WORD"_1 then  
     tokenstream(lextab,input,i+1,result+token(Wtoken:T, attribute:T([next])) )
     else 
      let newresult=result+token(Itoken:T, attribute:T([next]))
     assert kind = "INTEGER"_1 report  errormessage("Illegal character in Integer" +next,newresult,length.newresult)
          tokenstream(lextab,input,i+1,newresult )
      else 
    let act = lextab_lexindex 
     if tokenno.act = Itoken:T then tokenstream(lextab,input,i+1,result+token(Itoken:T, attribute:T([next])) )
   else if tokenno.act = 0 then 
       if next="/"_1  then
         let j=consumecomment(input,i)
         if j = i then let tmp= token("/"_1, 27, attribute:T("/")) tokenstream(lextab,input,j+1,result+tmp )
         else 
         assert j < length.input report errormessage("No matching //",result+token(0,attribute:T([next])),length.result+1)
          let tmp= token(commenttoken:T,attribute:T(subseq(input,i ,j-1 )))
          tokenstream(lextab,input,j,result+tmp )
       else 
       let j=findindex(next,input,i+1) 
       assert j < length.input report errormessage("No matching "+next,result+token(0,attribute:T([next])),length.result+1)
       let tmp=token(if next=" // "_1 then commenttoken:T else stringtoken:T, 
       attribute:T(subseq(input,i,j)))
       tokenstream(lextab,input,j+1,result+tmp )
    else 
       if next="/"_1  then
         let j=consumecomment(input,i)
         if j = i then let tmp= token("/"_1, 27, attribute:T("/")) tokenstream(lextab,input,j+1,result+tmp )
         else 
         assert j < length.input report errormessage("No matching //",result+token(0,attribute:T([next])),length.result+1)
          let tmp= token(commenttoken:T,attribute:T(subseq(input,i ,j-1 )))
          tokenstream(lextab,input,j,result+tmp )
       else 
       tokenstream(lextab,input,i+1,result+act )
       
       
       function  forward(stk:T,T) T unbound

        function step(input:seq.token.T, stk:stack.stkele.T ,token:token.T) stack.stkele.T 
  let stateno = stateno.top.stk 
  let actioncode = actiontable:T_(tokenno.token + length.tokenlist:T * stateno)
  if actioncode > 0 then 
    if stateno=2 then stk else 
     push(stk, stkele(actioncode,place.top.stk+1, forward(attribute.top.stk,attribute.token)))
  else 
  assert actioncode < 0 report errormessage( if w.token="#"_1 then "parse error:unexpected end of imput" else
  "parse error state"+toword.stateno,input,place.top.stk)+expect:T(stateno)
  let ruleno=-actioncode
  let rulelen = rulelength:T_ruleno 
   let newstk = pop(stk, rulelen)
 let newstateno= actiontable:T_(leftside:T_ruleno + length.tokenlist:T * stateno.top.newstk)
 assert newstateno > 0 report"????"
 let newstkele=stkele(newstateno,place.top.stk, action(ruleno,input,reduction(top(stk, rulelen))))
 step(input,push(newstk, newstkele),token)
 
use set.word

function expect:T(stateno:int)seq.word 
 let l = @(+, kk:T(stateno),"", arithseq(length.tokenlist:T, 1, 1))
   toseq(asset.l - asset."-=_^∧ ∨ *")

function kk:T(stateno:int, token:int)seq.word 
 if 0 ≠ actiontable:T_(length.tokenlist:T * stateno + token)then [ tokenlist:T_token]else empty:seq.word


 Function  place(R:reduction.T) int  place((toseq.R)_length.toseq.R)


 
function token( tokenno:int,attribute:T)  token.T   token("??"_1,tokenno,attribute) 

 Function parse:T(input:seq.word) T
   // if parse is called many times caching lextable improves performance //
   parse:T(attribute:T(""),sort.lextable:T,input)

Function parse:T(initial:T,lextable:seq.token.T,input:seq.word) T
let a=  tokenstream (lextable,input+ "#",1,empty:seq.token.T) 
    let stk=@(step.a,identity,push(empty:stack.stkele.T, stkele(startstate:T,1,initial )),a)
    attribute.top.stk

Function sortedlextable:T seq.token.T sort.lextable:T



function lextable:T seq.token.T // generated by genlex module in tools //  
[  token("'"_1, 0, attribute:T("'")) 
,token("N"_1, 34, attribute:T("N")) 
, token("("_1, 3, attribute:T("(")) 
, token("}"_1, 10, attribute:T("}")) 
, token("function"_1, 34, attribute:T("function")) 
, token(if length."//"=1 then "//"_1 else "thiSSHOULDNEVerMAtCH"_1, 0, attribute:T("//")) 
, token("]"_1, 7, attribute:T("]")) 
, token("I"_1, 34, attribute:T("I")) 
, token("F"_1, 34, attribute:T("F")) 
, token("use"_1, 34, attribute:T("use")) 
, token(merge("&"+"ge"), 6, attribute:T("≥")) 
, token("#"_1, 19, attribute:T("#")) 
, token("≠"_1, 6, attribute:T("≠")) 
, token("+"_1, 8, attribute:T("+")) 
, token("_"_1, 14, attribute:T("_")) 
, token('"'_1, 0, attribute:T('"')) 
, token("@"_1, 29, attribute:T("@")) 
, token("P"_1, 34, attribute:T("P")) 
, token("else"_1, 21, attribute:T("else")) 
, token("i"_1, 34, attribute:T("i")) 
, token(merge("&"+"and"), 25, attribute:T("∧")) 
, token("∩"_1, 27, attribute:T("∩")) 
, token(")"_1, 4, attribute:T(")")) 
, token("*"_1, 27, attribute:T("*")) 
, token("FP"_1, 34, attribute:T("FP")) 
, token("Function"_1, 34, attribute:T("Function")) 
, token(","_1, 12, attribute:T(",")) 
, token("inst"_1, 34, attribute:T("inst")) 
, token("W"_1, 34, attribute:T("W")) 
, token("A"_1, 34, attribute:T("A")) 
, token("$wordlist"_1, 34, attribute:T("$wordlist")) 
, token("is"_1, 16, attribute:T("is")) 
, token("assert"_1, 23, attribute:T("assert")) 
, token("K"_1, 34, attribute:T("K")) 
, token("report"_1, 24, attribute:T("report")) 
, token("∧"_1, 25, attribute:T("∧")) 
, token(":"_1, 5, attribute:T(":")) 
, token("{"_1, 9, attribute:T("{")) 
, token(merge("&"+"or"), 26, attribute:T("∨")) 
, token("mod"_1, 27, attribute:T("mod")) 
, token(merge("&"+"in"), 8, attribute:T("∈")) 
, token("then"_1, 20, attribute:T("then")) 
, token("≤"_1, 6, attribute:T("≤")) 
, token("∪"_1, 27, attribute:T("∪")) 
, token("/"_1, 27, attribute:T("/")) 
, token(">>"_1, 6, attribute:T(">>")) 
, token("-"_1, 8, attribute:T("-")) 
, token("L"_1, 34, attribute:T("L")) 
, token("∨"_1, 26, attribute:T("∨")) 
, token("a"_1, 34, attribute:T("a")) 
, token("<"_1, 6, attribute:T("<")) 
, token("E"_1, 34, attribute:T("E")) 
, token(">"_1, 6, attribute:T(">")) 
, token(merge("&"+"contains"), 8, attribute:T("∋")) 
, token("word"_1, 34, attribute:T("word")) 
, token("seq"_1, 34, attribute:T("seq")) 
, token(merge("&"+"le"), 6, attribute:T("≤")) 
, token("^"_1, 14, attribute:T("^")) 
, token("in"_1, 8, attribute:T("in")) 
, token("∈"_1, 8, attribute:T("∈")) 
, token("comment"_1, 34, attribute:T("comment")) 
, token(merge("&"+"cup"), 27, attribute:T("∪")) 
, token("="_1, 2, attribute:T("=")) 
, token("if"_1, 18, attribute:T("if")) 
, token("["_1, 13, attribute:T("[")) 
, token("."_1, 1, attribute:T(".")) 
, token(merge("&"+"ne"), 6, attribute:T("≠")) 
, token("G"_1, 34, attribute:T("G")) 
, token("let"_1, 22, attribute:T("let")) 
, token("0"_1, 38, attribute:T("0")) 
, token("?"_1, 6, attribute:T("?")) 
, token("∋"_1, 8, attribute:T("∋")) 
, token(merge("&"+"cap"), 27, attribute:T("∩")) 
, token("T"_1, 34, attribute:T("T")) 
, token("<<"_1, 6, attribute:T("<<")) 
, token("≥"_1, 6, attribute:T("≥")) 
, token("int"_1, 34, attribute:T("int")) 
, token("mytype"_1, 34, attribute:T("mytype")) 
, token(". "_1, 41, attribute:T(".")) 
, token("2"_1, 38, attribute:T("2")) 
, token("empty"_1, 34, attribute:T("empty"))]

function Wtoken:T int // generated by genlex module in tools // 34 

function Itoken:T int // generated by genlex module in tools // 38 

function commenttoken:T int // generated by genlex module in tools // 11 

function stringtoken:T int // generated by genlex module in tools // 28 

function rulelength:T seq.int [ 2, 7, 4, 5, 1, 1, 1, 3, 3, 5, 4, 6, 1, 4, 3, 3, 6, 3, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 4, 2, 5, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 10]

function leftside:T seq.int [ 32, 33, 33, 33, 33, 40, 35, 35, 35, 35, 35, 35, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 37, 37, 31, 30, 31, 31, 31, 31, 17, 17, 31, 31, 36, 36, 36, 36, 36, 36, 36, 39, 39, 39, 39, 41, 41, 41, 31]

function tokenlist:T seq.word".=():>]- { } comment, [_^is T if # then else let assert report ∧ ∨ * $wordlist @ A E G F W P N L I K FP NM"

function startstate:T int 1

noactions 2598
nosymbols:41
norules 55
nostate 139

function actiontable:T seq.int [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 15, -37, -37, 0, 14, -37, 12, -37, -37, -37, -37, -37, 7, -37, 0, -37, -37, -37, -37, -37, -37, -37, -37, 11, 13, 9, -37, -37, -37, -37, 0, 0, 10, 0, 6, 0, -37, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -53, -53, -53, 0, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, 0, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, 0, 0, -53, 0, -53, 0, -53, 0, 0, -53, -41, -41, -41, -41, 0, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, 0, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, -41, 0, 0, -41, 0, -41, 0, -41, 0, 0, -41, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, -45, -45, -45, -45, 0, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, 0, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, -45, 0, 0, -45, 0, -45, 0, -45, 0, 0, -45, 0, -52, -52, -52, 21, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, 20, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, 0, 0, -52, 0, -52, 0, -52, 0, 0, -52, -46, -46, -46, -46, 0, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, 0, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, -46, 0, 0, -46, 0, -46, 0, -46, 0, 0, -46, -42, -42, -42, -42, 0, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, -42, 0, 0, -42, 0, -42, 0, -42, 0, 0, -42, -47, -47, -47, -47, 0, -47, -47, -47, -47, -47, -47, -47, -47, -47, -47, 0, -47, -47, -47, -47, -47, -47, -47, -47, -47, -47, -47, -47, -47, -47, -47, 0, 0, -47, 0, -47, 0, -47, 0, 0, -47, -44, -44, -44, -44, 0, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, 0, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, -44, 0, 0, -44, 0, -44, 0, -44, 0, 0, -44, -43, -43, -43, -43, 0, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, 0, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, -43, 0, 0, -43, 0, -43, 0, -43, 0, 0, -43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 23, 0, 0, 0, 0, 24, 0, 16, -37, -37, -37, 0, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, 0, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, 0, 0, -37, 0, -37, 0, -37, 0, 0, -37, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 39, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, -38, -38, -38, 0, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, 0, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, -38, 0, 0, -38, 0, -38, 0, -38, 0, 0, -38, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, -37, -37, -37, 48, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, 0, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, 0, 0, -37, 0, -37, 0, -37, 0, 0, -37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 50, -53, -53, -53, 0, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, 0, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, 0, 0, -53, 0, -53, 0, -53, 0, 0, -53, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 51, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 52, -35, -35, -35, 0, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, 0, 0, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, -35, 0, 0, -35, 0, -35, 0, -35, 0, 0, -35, 0, 0, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -13, 54, -13, 0, -13, -13, -13, -13, -13, -13, -13, -13, -13, -13, 0, 0, -13, -13, -13, -13, -13, -13, -13, -13, -13, -13, -13, -13, -13, -13, 0, 0, -13, 0, -13, 0, -13, 0, 0, -13, 55, -52, -52, -52, 21, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, 0, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, 0, 0, -52, 0, -52, 0, -52, 0, 0, -52, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 56, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, -39, -39, -39, 0, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, 0, 0, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, -39, 0, 0, -39, 0, -39, 0, -39, 0, 0, -39, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 57, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 58, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, -42, 15, 29, -42, 0, 14, -42, 38, 37, -42, 40, -42, 42, 7, -42, 0, -42, 41, -42, -42, -42, 43, 36, -42, 11, 13, 9, 35, 31, 34, 59, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 67, 0, 0, 0, 65, 0, 63, 0, 0, 0, 0, 0, 60, 66, 0, 0, 0, -3, 0, 0, 0, 0, 0, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 68, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 69, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 71, 0, 0, 33, 0, 28, 70, 30, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 73, 0, 0, 0, 0, 0, 0, 0, -54, -54, -54, 0, -54, -54, -54, -54, -54, -54, -54, -54, -54, -54, 0, -54, -54, -54, -54, -54, -54, -54, -54, -54, -54, -54, -54, -54, -54, -54, 0, 0, -54, 0, -54, 0, -54, 0, 0, -54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75, 0, 0, 0, 0, 0, 76, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 74, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 79, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 80, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 67, 0, 81, 0, 65, 0, 63, 0, 0, 0, 0, 0, 60, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82, 0, 0, 0, 0, 15, 0, 0, 0, 14, 0, 12, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 13, 9, 0, 0, 0, 0, 0, 0, 85, 0, 83, 0, 0, 86, 0, 84, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 71, 0, 0, 33, 0, 28, 87, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 88, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 67, -33, -33, 0, 65, -33, 63, -33, -33, -33, -33, -33, 60, 66, 0, 0, -33, -33, -33, -33, -33, -33, -33, 62, 64, 61, -33, -33, -33, -33, 0, 0, -33, 0, -33, 0, -33, 0, 0, -33, 0, 67, 0, 0, 0, 65, 0, 63, 0, 0, 0, 0, 0, 60, 66, 0, 0, 0, 0, 0, 0, 0, 0, 89, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 0, 0, 0, 65, 0, 63, 0, 90, 0, 0, 0, 60, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -20, -20, -20, 0, -20, -20, -20, -20, -20, -20, -20, -20, 60, 66, 0, 0, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, -20, 0, 0, -20, 0, -20, 0, -20, 0, 0, -20, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 91, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 92, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 93, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 94, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 95, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 96, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 97, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 98, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, -40, -40, -40, 0, -40, -40, -40, -40, -40, -40, -40, -40, 60, 66, 0, 0, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, -40, 0, 0, -40, 0, -40, 0, -40, 0, 0, -40, 0, 67, 0, 0, 0, 65, 0, 63, 0, 0, 0, 0, 0, 60, 66, 0, 0, 0, 0, 99, 0, 0, 0, 0, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 0, 0, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 0, -29, 0, 65, -29, 63, 0, 0, 0, -29, 0, 60, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 102, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, -37, -37, -37, 103, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, 0, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, -37, 0, 0, -37, 0, -37, 0, -37, 0, 0, -37, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 104, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 105, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 0, 0, -9, 0, 0, 0, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 0, -9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, -22, -22, -22, 0, -22, -22, -22, -22, -22, -22, -22, -22, 60, 66, 0, 0, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, -22, 0, 0, -22, 0, -22, 0, -22, 0, 0, -22, 0, -15, -15, -15, 0, -15, -15, -15, -15, -15, -15, -15, -15, -15, -15, 0, 0, -15, -15, -15, -15, -15, -15, -15, -15, -15, -15, -15, -15, -15, -15, 0, 0, -15, 0, -15, 0, -15, 0, 0, -15, 0, -36, -36, -36, 0, -36, -36, -36, -36, -36, -36, -36, -36, -36, -36, 0, 0, -36, -36, -36, -36, -36, -36, -36, -36, -36, -36, -36, -36, -36, -36, 0, 0, -36, 0, -36, 0, -36, 0, 0, -36, 107, -53, -53, -53, 0, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, 0, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, -53, 0, 0, -53, 0, -53, 0, -53, 0, 0, -53, 0, 0, 108, 0, 0, 0, 0, 0, 0, 0, 0, -51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 109, -52, -52, -52, 21, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, 0, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, -52, 0, 0, -52, 0, -52, 0, -52, 0, 0, -52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 111, 0, 0, 0, 0, 0, 0, 0, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -21, -21, -21, 0, -21, -21, -21, -21, -21, -21, -21, -21, 60, 66, 0, 0, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, -21, 0, 0, -21, 0, -21, 0, -21, 0, 0, -21, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 112, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, -16, -16, -16, 0, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, 0, 0, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, 0, 0, -16, 0, -16, 0, -16, 0, 0, -16, 0, -19, -19, -19, 0, -19, -19, -19, -19, -19, -19, -19, -19, -19, 66, 0, 0, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, -19, 0, 0, -19, 0, -19, 0, -19, 0, 0, -19, 0, -23, -23, -23, 0, -23, -23, -23, -23, -23, -23, -23, -23, 60, 66, 0, 0, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, -23, 0, 0, -23, 0, -23, 0, -23, 0, 0, -23, 0, 67, -27, -27, 0, 65, -27, 63, -27, -27, -27, -27, -27, 60, 66, 0, 0, -27, -27, -27, -27, -27, -27, -27, -27, -27, 61, -27, -27, -27, -27, 0, 0, -27, 0, -27, 0, -27, 0, 0, -27, 0, -24, -24, -24, 0, -24, -24, -24, -24, -24, -24, -24, -24, 60, 66, 0, 0, -24, -24, -24, -24, -24, -24, -24, -24, -24, 61, -24, -24, -24, -24, 0, 0, -24, 0, -24, 0, -24, 0, 0, -24, 0, 67, -28, -28, 0, 65, -28, 63, -28, -28, -28, -28, -28, 60, 66, 0, 0, -28, -28, -28, -28, -28, -28, -28, 62, -28, 61, -28, -28, -28, -28, 0, 0, -28, 0, -28, 0, -28, 0, 0, -28, 0, -26, -26, -26, 0, -26, -26, 63, -26, -26, -26, -26, -26, 60, 66, 0, 0, -26, -26, -26, -26, -26, -26, -26, -26, -26, 61, -26, -26, -26, -26, 0, 0, -26, 0, -26, 0, -26, 0, 0, -26, 0, 67, -18, -18, 0, 65, -18, 63, -18, -18, -18, -18, -18, 60, 66, 0, 0, -18, -18, -18, -18, -18, -18, -18, 62, 64, 61, -18, -18, -18, -18, 0, 0, -18, 0, -18, 0, -18, 0, 0, -18, 0, -25, -25, -25, 0, -25, -25, 63, -25, -25, -25, -25, -25, 60, 66, 0, 0, -25, -25, -25, -25, -25, -25, -25, -25, -25, 61, -25, -25, -25, -25, 0, 0, -25, 0, -25, 0, -25, 0, 0, -25, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 113, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, -31, -31, -31, 0, -31, -31, -31, -31, -31, -31, -31, -31, -31, -31, 0, 0, -31, -31, -31, -31, -31, -31, -31, -31, -31, -31, -31, -31, -31, -31, 0, 0, -31, 0, -31, 0, -31, 0, 0, -31, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 114, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 115, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 117, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 0, 0, 0, 65, 0, 63, 0, 0, 0, 0, 0, 60, 66, 0, 0, 0, -2, 0, 0, 0, 0, 0, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -11, 0, 0, 0, 0, 0, 0, 0, -11, 0, 0, 0, 0, 0, 0, -11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 118, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 71, 0, 0, 33, 0, 28, 119, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 120, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 0, 0, 0, 14, 0, 12, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 13, 9, 0, 0, 0, 0, 0, 0, 85, 0, 83, 0, 0, 121, 0, 84, 0, -14, -14, -14, 0, -14, -14, -14, -14, -14, -14, -14, -14, -14, -14, 0, 0, -14, -14, -14, -14, -14, -14, -14, -14, -14, -14, -14, -14, -14, -14, 0, 0, -14, 0, -14, 0, -14, 0, 0, -14, 0, 129, 29, 0, 0, 128, 0, 125, 37, 0, 40, 0, 42, 122, 66, 0, 0, 41, 0, 0, 0, 43, 36, 0, 124, 126, 123, 35, 31, 34, 127, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 67, 0, 0, 0, 65, 0, 63, 0, 0, 0, 0, 0, 60, 66, 0, 0, 0, 0, 0, 130, 0, 0, 0, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 0, -30, 0, 65, -30, 63, 0, 0, 0, -30, 0, 60, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, -32, 0, 0, 65, 0, 63, -32, 0, -32, 0, -32, 60, 66, 0, 0, -32, 0, 0, 0, -32, -32, 0, 62, 64, 61, -32, -32, -32, -32, 0, 0, -32, 0, -32, 0, -32, 0, 0, -32, 0, 0, 0, -10, 0, 0, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 131, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 0, 67, 0, 0, 0, 65, 0, 63, 0, 0, 0, -49, 0, 60, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 132, 0, 0, 0, 0, 0, 0, 0, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 67, 0, 0, 0, 65, 0, 63, 0, 0, 0, -48, 0, 60, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 133, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -41, 15, 29, -41, 0, 14, -41, 38, 37, -41, 40, -41, 42, 7, -41, 0, -41, 41, -41, -41, -41, 43, 36, -41, 11, 13, 9, 35, 31, 34, 91, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, -45, 15, 29, -45, 0, 14, -45, 38, 37, -45, 40, -45, 42, 7, -45, 0, -45, 41, -45, -45, -45, 43, 36, -45, 11, 13, 9, 35, 31, 34, 92, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, -46, 15, 29, -46, 0, 14, -46, 38, 37, -46, 40, -46, 42, 7, -46, 0, -46, 41, -46, -46, -46, 43, 36, -46, 11, 13, 9, 35, 31, 34, 93, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, -42, 15, 29, -42, 0, 14, -42, 38, 37, -42, 40, -42, 42, 7, -42, 0, -42, 41, -42, -42, -42, 43, 36, -42, 11, 13, 9, 35, 31, 34, 134, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, -47, 15, 29, -47, 0, 14, -47, 38, 37, -47, 40, -47, 42, 7, -47, 0, -47, 41, -47, -47, -47, 43, 36, -47, 11, 13, 9, 35, 31, 34, 95, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 67, -34, -34, 0, 65, -34, 63, -34, -34, -34, -34, -34, 60, 66, 0, 0, -34, -34, -34, -34, -34, -34, -34, 62, 64, 61, -34, -34, -34, -34, 0, 0, -34, 0, -34, 0, -34, 0, 0, -34, -44, 15, 29, -44, 0, 14, -44, 38, 37, -44, 40, -44, 42, 7, -44, 0, -44, 41, -44, -44, -44, 43, 36, -44, 11, 13, 9, 35, 31, 34, 96, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, -43, 15, 29, -43, 0, 14, -43, 38, 37, -43, 40, -43, 42, 7, -43, 0, -43, 41, -43, -43, -43, 43, 36, -43, 11, 13, 9, 35, 31, 34, 98, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 135, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 136, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, -24, -24, -24, 0, -24, -24, -24, -24, -24, -24, -24, -24, 60, 66, 0, 0, -24, -24, -24, -24, -24, -24, -24, -24, -24, -20, -24, -24, -24, -24, 0, 0, -24, 0, -24, 0, -24, 0, 0, -24, 0, 67, -17, -17, 0, 65, -17, 63, -17, -17, -17, -17, -17, 60, 66, 0, 0, -17, -17, -17, -17, -17, -17, -17, 62, 64, 61, -17, -17, -17, -17, 0, 0, -17, 0, -17, 0, -17, 0, 0, -17, 0, 67, 0, 0, 0, 65, 0, 63, 0, 0, 0, 137, 0, 60, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 29, 0, 0, 14, 0, 38, 37, 0, 40, 0, 42, 7, 0, 0, 0, 41, 0, 0, 0, 43, 36, 0, 11, 13, 9, 35, 31, 34, 138, 0, 0, 33, 0, 28, 0, 30, 0, 0, 32, 0, 67, 0, 139, 0, 65, 0, 63, 0, 0, 0, 0, 0, 60, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62, 64, 61, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -55, -55, -55, 0, -55, -55, -55, -55, -55, -55, -55, -55, -55, -55, 0, 0, -55, -55, -55, -55, -55, -55, -55, -55, -55, -55, -55, -55, -55, -55, 0, 0, -55, 0, -55, 0, -55, 0, 0, -55]
 
