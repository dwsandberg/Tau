#!/usr/local/bin/tau


Module testparser

* Example of LR1 parser. 

run testparser testparser 

use stdlib

use stack.stkele


use seq.stkele

use genLR1

use seq.seq.word


use seq.stepresult

Function testparser seq.word 
//  runs the parser on a sample string. //
 parse("1+2+3")+"OK"

Function gentestgrammar seq.word 
// generates the tables used in this test //
  let testgrammar=[ ["G F #","$_1"], 
 ["F E","$_1"], 
 ["E 1","1"], 
 ["E 2","2"], 
 ["E 3","3"], 
 ["E E + E","$_1 + $_3"]]  
lr1parser(testgrammar, empty:seq.seq.word)


    type  stepresult is record stk:stack.stkele, place:int,track:seq.word ,tokenstate:int,string:seq.word
 
type stkele is record stateno:int,  result:int

function dict (  result:int) int
//  dict is not used in this example.  In more complicated example the result fld of the stkele would be a record // 0

function getactioncode(stateno:int,lookahead:word) int
  actiontable_( findindex(lookahead,tokenlist)+length.tokenlist * stateno)

function       consumeinput(b :stepresult,next:word)  stepresult
            let stk=stk.b
            let track=true
            let stateno=stateno.top.stk
            let commenttoken=1 let stringtoken=2
            let token=next     
             let actioncode=getactioncode(stateno,token)
               if actioncode > 0  then 
                 stepresult(push(stk,stkele( actioncode,0)) ,place.b+1,
               if track then track.b+"&br next"+next+printstate.actioncode else track.b,0,"")
               else assert actioncode < 0 report "parse error"+"place"+toword.place.b+toword.actioncode+track.b
             let x = reduce(stk,-actioncode ,place.b, track.b) 
             consumeinput( stepresult(x,place.b,
              if track then track.b+"&br reduce by"+toword.(-actioncode)+printstate.stateno.top.x else track.b,tokenstate.b,string.b),next)
              
   
Function parse(input:seq.word) seq.word
let a=@(consumeinput,identity,stepresult(push(empty:stack.stkele,stkele(startstate,0)),1,"",0,""),input+"#")
 [toword.(result.(toseq.stk.a)_2)]
 


 

Below is generated from parser generator.


function tokenlist seq.word"1 + 2 3 # E G F" 

function startstate int 1 

function actiontable seq.int [ 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 4, 0, 5, 0, 6, 0, -3, 0, 0, -3, 0, 0, 0, 0, -4, 0, 0, -4, 0, 0, 0, 0, -5, 0, 0, -5, 0, 0, 0, 0, 7, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 2, 0, 3, 4, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, -6] 

function reduce(stk:stack.stkele, ruleno:int, place:int, input:seq.word)stack.stkele // generated function // 
let rulelen = [ 2, 1, 1, 1, 1, 3]_ruleno 
let newstk = pop(stk, rulelen) 
let subtrees = top(stk, rulelen) 
let dict = dict.result.top.stk 
let newtree = 
if ruleno = // G F # // 1 then result.subtrees_1 else 
if ruleno = // F E // 2 then result.subtrees_1 else 
if ruleno = // E 1 // 3 then 1 else 
if ruleno = // E 2 // 4 then 2 else 
if ruleno = // E 3 // 5 then 3 else 
assert ruleno = // E E + E // 6 report"invalid rule number"+ toword.ruleno 
result.subtrees_1 + result.subtrees_3 
let leftsidetoken = [ 7, 8, 6, 6, 6, 6]_ruleno 
let actioncode = actiontable_(leftsidetoken + length.tokenlist * stateno.top.newstk) 
assert actioncode > 0 report"??" 
push(newstk, stkele(actioncode, newtree)) 

function printstate(stateno:int)seq.word 
[ 
"E ' 1 | E ' 2 | E ' 3 | E ' E + E | G ' F # | F ' E 
", 
"E 1 ' 
", 
"E 2 ' 
", 
"E 3 ' 
", 
"E E ' + E | F E ' 
", 
"G F ' # 
", 
"E ' 1 | E ' 2 | E ' 3 | E ' E + E | E E + ' E 
", 
"G F # ' 
", 
"E E ' + E | E E + E ' 
"]_stateno