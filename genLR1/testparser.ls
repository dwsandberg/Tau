#!/usr/local/bin/tau

 #!/usr/local/bin/tau
#!/usr/local/bin/tau



Module testparser

run testparser test5

use stdlib

use stack.stkele2


use seq.stkele2


use seq.stepresult2

    type  stepresult2 is record stk:stack.stkele2, place:int,track:seq.word ,tokenstate:int,string:seq.word

type stkele2 is record stateno:int,  result:int

function getactioncode(stateno:int,lookahead:word) int
  actiontable_( findindex(lookahead,tokenlist)+length.tokenlist * stateno)

function printstate(i:int) seq.word "state="+[toword.i]

function       consumeinput(b :stepresult2,next:word)  stepresult2
            let stk=stk.b
            let track=true
            let stateno=stateno.top.stk
            // assert place.b < 6 report "next"+next+print.state //
            let commenttoken=1 let stringtoken=2
            let token=next     
             let actioncode=getactioncode(stateno,token)
               if actioncode > 0  then 
                 stepresult2(push(stk,stkele2( actioncode,0)) ,place.b+1,
               if track then track.b+"&br next"+next+printstate.actioncode else track.b,0,"")
               else assert actioncode < 0 report "parse error"+"place"+toword.place.b+toword.actioncode+track.b
             let x = reduce(stk,-actioncode ) 
             consumeinput( stepresult2(x,place.b,
              if track then track.b+"&br reduce by"+toword.(-actioncode)+printstate.stateno.top.x else track.b,tokenstate.b,string.b),next)
              
   
Function parse(input:seq.word) seq.word
let a=@(consumeinput,identity,stepresult2(push(empty:stack.stkele2,stkele2(startstate,0)),1,"",0,""),input+"#")
 [toword.(result.(toseq.stk.a)_2)]
 

Function test5 seq.word  parse("1+2+3")+"OK"

Below is generated from parser generator.

function tokenlist seq.word"1 + # 3 2 F E G" 

function startstate int 1 

function actiontable seq.int [ 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 4, 5, 6, 0, 0, -3, -3, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -4, -4, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 8, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 4, 0, 9, 0, 0, 8, -6] 

function reduce(stk:stack.stkele2, ruleno:int)stack.stkele2 // generated function // 
let rulelen = [ 2, 1, 1, 1, 1, 3]_ruleno 
let newstk = pop(stk, rulelen) 
let subtrees = top(stk, rulelen) 
let newtree = 
if ruleno = // G F # // 1 then result.subtrees_1 else 
if ruleno = // F E // 2 then result.subtrees_1 else 
if ruleno = // E 1 // 3 then 1 else 
if ruleno = // E 2 // 4 then 2 else 
if ruleno = // E 3 // 5 then 3 else 
assert ruleno = // E E + E // 6 report"invalid rule number"+ toword.ruleno 
result.subtrees_1 + result.subtrees_3 
let leftside ="G F E E E E"_ruleno 
let actioncode = getactioncode(stateno.top.newstk, leftside) 
assert actioncode > 0 report"??" 
push(newstk, stkele2(actioncode, newtree)) 
