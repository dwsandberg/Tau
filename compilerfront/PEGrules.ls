Module PEGrules

???? handle  "* R a; b; c; d;  any" so final string is only created at end.

  make PEGbyte.ls  handle blanklines at beginning.

???? for statement fails some times because generated locals are not unique. 

???? handle  " S a b c d sp  / a b c e " so first part is not scanned twice.

???? further test of ! operator.  

???? optimize  PEGbyte.ls 

???? add error recovery

use standard

use seq.pegpart

use seq.pegrule

use seq.tableEntry


Function pattern2code(pattern:seq.word) seq.word
for acc = "", last = "", w ∈ pattern+dq  do
   if last /ne "^" then
   next(acc + last,[w])
  else  if checkinteger.w ∈ "INTEGER" then
    next(acc+dq("+R_$([w])+"),"") 
   else
   next(acc + last,[w])  
/do dq.acc




Function PEGgrammar(s:seq.word) seq.pegrule
let beginrule = 1
let inpart = 2
let inaction = 3
let more = 4,
for state = beginrule
 , kind = "d"_1
 , leftside = "?"_1
 , acc = ""
 , part = ""
 , parts = empty:seq.pegpart
 , rules = empty:seq.pegrule
 , w ∈ s + "/br /br"
do
   if state=beginrule then
  let newrules = if isempty.parts then rules else rules + rule(kind, leftside, parts)
  let newkind = if not.isempty.parts then "d"_1 else kind,
  if w ∈ "* !" then
                    next(beginrule,w,leftside,"","",empty:seq.pegpart,newrules)
  else
   next(inpart, newkind, w, "", "", empty:seq.pegpart, newrules)
    else if state=inpart then
  if w ∈ "#" then
      next(inaction,kind,leftside,"",acc,parts,rules)
  else
   next(inpart, kind, leftside, acc + w, part, parts, rules)
   else if state=inaction then 
  if w ∈ "#" then
   next(more, kind, leftside, "", "", parts + pegpart(part, acc), rules)
  else
   next(inaction, kind, leftside, acc + w, part, parts, rules)
 else
  {state = more}
  if w ∈ "/" then
        next(inpart,kind, leftside,"","",parts,rules)
  else
   assert w ∈ "/br" report "format problem  $(leftside) <* none $(s) *> "  ,
            next(beginrule,kind, leftside,"","",parts,rules)
  /do  rules

use otherseq.pegrule
 
function   %(r:pegrule) seq.word
  "/br br"+ %leftside.r 
+ for acc = "", p ∈ parts.r do
     acc+part.p +"#"+replacement.p+"# /" 
    /do acc >> 1  

function match(has!:boolean,e:word, g:seq.pegrule) state
for acc = startstate + goallength, match = Match, r ∈ g
while match = Match
do
 if e = leftside.r ∧ has! = kind.r ∈ "!" then
 next(acc, MatchNT.acc) 
 else
  next(acc + nostates.r, match)
/do match

type pegrule is kind:word
 , leftside:word
 , parts:seq.pegpart
 , nostates:int
 
function %leftside(r:pegrule) seq.word
if kind.r ∈ "* !" then [kind.r, leftside.r] else [leftside.r]
  
Function pretty(rules:seq.pegrule) seq.word
for acc0 = "2", r ∈ rules do
 let startno = toint.first.acc0,
 for acc = "", partno = startno, p ∈ parts.r do
   next(acc + " $(part.p) # $(partno) # /", partno + 1)
 /do
  let newrule = 
   "$(%leftside.r) $(acc >> 1)
    /br
    "
  ,
  %.if startno = partno then partno + 1 else partno /if + acc0 << 1
  + newrule
/do acc0

type pegpart is  part:seq.word, replacement:seq.word

type tableEntry is action:state, match:word, Sstate:state, Fstate:state

Export type:pegrule

Export type:tableEntry

Export Fstate(tableEntry) state

Export Sstate(tableEntry) state

Export match(tableEntry) word

Export action(tableEntry) state



function nostates2(a:pegpart,kind:word) int
for acc = if kind ∈ "*" then 1 else 0, e ∈ part.a do
 if e ∈ "!" then acc else acc + 1
/do acc

function goallength int 1

function rule(kind:word,leftside:word,p:seq.pegpart) pegrule
for acc = 0 ,e ∈ p do
 acc + nostates2(e, kind)
/do pegrule(kind, leftside, p, acc)

use otherseq.seq.word

use otherseq.word

function =(a:pegpart,b:pegpart) boolean 
  let t= part.a=part.b 
assert t report "XX" + part.a + part.b,
t

function =(a:pegrule,b:pegrule) boolean  
let t = kind.a = kind.b ∧ leftside.a = leftside.b ∧ parts.a = parts.b
assert t report "XX" + leftside.a + leftside.b + kind.a + kind.b,
t

 function replacement(kind:seq.word,r:pegpart) seq.word
  if kind="code" then replacement.r   
  else if kind="first" then "R_0"
  else assert kind="words" report "unknown replacement type:" +kind
   pattern2code.replacement.r
  
Function makeAction( kind:seq.word, gin:seq.pegrule) seq.word
let adjust=length."else if partno=0 then {"
     for acc = empty:seq.seq.word, r ∈ gin do
  for acc0 = acc, p ∈ parts.r do
   let part0 = 
    for part0 = "", w0 ∈ part.p do
     if w0 ∈ dq then
      part0 + "dq"
     else if w0 ∈ "{" then
      part0 + "/lb"
     else if w0 ∈ "}" then part0 + "/rb" else part0 + w0
      /do part0
   ,
   acc0
   + "if partno ={;; $(%leftside.r) $(part0) ;;} $(length.acc0 + 2) then  
   $(replacement(kind,p))
     else"
  /do acc0
 /do  
 {assert "paragraphx"_1 /in %.acc report %.acc}
 "{$(pretty.gin)}    $(%.acc >> 1)  
  else {  partno = x ;; X } R_0"
  
 

Function PEGgrammarFromAction(s:seq.word) seq.pegrule
{Extract grammar from action table }
let first;;=0
let inrule=1
let inpart=2
let inaction=3
for rules = empty:seq.pegrule
 , state = first;;
 , part = ""
 , act = ""
 , parts = empty:seq.pegpart
 , lastleft = "?"
 , w ∈ s + ";; ;;"
do
   if state=first;;  then 
  if w ∈ ";;" then
   next(rules, inpart, part, act, parts, lastleft)
  else
   next(rules, first;;, part, act, parts, lastleft)
   else if state=inpart then
  if w ∈ ";;" then
   next(rules, inaction, part, act, parts, lastleft)
   else 
   let w1 = if w ∈ "/lb" then "{}"_1 else if w ∈ "/rb" then "{}"_2 else w,
   next(rules, inpart, part + w1, act, parts, lastleft)
 else if w ∈ ";;" then
  let thisleft = if first.part ∈ "* !" then subseq(part, 1, 2) else [first.part]
  let newpart = pegpart(part << length.thisleft, act << 3 >> 5),
        if lastleft=thisleft then
            next(rules, inpart ,"","",parts+newpart,thisleft)
       else   
   let kind = if first.lastleft ∈ "*" then first.lastleft else "d"_1,
         next(rules+rule(kind,last.lastleft,parts)  , inpart ,"","",[newpart],thisleft)
 else
  next(rules, inaction, part, act + w, parts, lastleft)
/do rules << 1

Function makeTbl(gin:seq.pegrule) seq.tableEntry
let g = [rule("d"_1, "G"_1, [pegpart([leftside.first.gin], "")])] + gin,
for nextstate = startstate
 , table = empty:seq.tableEntry
 , reduce0 = 1
 , s ∈ g
do
 let begin = nextstate
 let ruletableentries = 
  for nextstate2 = nextstate
   , acc = empty:seq.tableEntry
   , reduce = reduce0
   , remainingparts = length.parts.s
   , p ∈ parts.s
  do
   let nextpart = nextstate2 + nostates2(p,kind.s)
   let failmatch = 
    if remainingparts > 1    then
     nextpart
    else if kind.s ∈ "*" then Success* else if kind.s ∈ "!" then New! else Fail
   let parttableentries = 
    for   acc2 = empty:seq.tableEntry
     , thisstate = nextstate2
     , last = "?"_1
     , e ∈ part.p
    do
     if e ∈ "!" then
      next(  acc2, thisstate, e)
     else
      let ee = match(last ∈ "!", e, gin)
      let action = 
       if e ∈ "any" then
        MatchAny
       else
         if last ∈ "!" ∧ ee = Match then !Match else ee
      let C = tableEntry(action, e, thisstate + 1, failmatch),
      next(  acc2 + C, thisstate + 1, e)
    /do
     if kind.s ∈ "*" then
      acc2 + tableEntry(Reduce.reduce, "?"_1,  begin ,   state.0)
       else 
         let final = last.acc2,
      if kind.s ∈ "!" then
             acc2 >> 1 + tableEntry(action.final, match.final,Fail  , New!)
       else 
        acc2 >> 1 + tableEntry(action.final, match.final,Reduce.reduce  , Fstate.final)  
   ,
   next(nextpart, acc + parttableentries, reduce + 1, remainingparts - 1)
  /do acc
 ,
 next(nextstate + length.ruletableentries
  , table + ruletableentries
  , reduce0 + if kind.s /in "!" then 0 else length.parts.s
  )
/do  table 

Function NonTerminals( p:pegpart,gin:seq.pegrule) seq.word
  for Ncount = "\0"
      , last = "?"_1
     , e ∈ part.p
    do
     if e ∈ "!" /or last ∈ "!" /or e /nin "any" /and match(last ∈ "!", e, gin)=Match then
       next(Ncount , e)
     else  
      next(Ncount+  merge("\ $(length.Ncount)"),e)
     /do  Ncount
     
type  machine is   constants:seq.seq.word,actions:seq.seq.int

Export type:machine

use seq.seq.int



function  otherinst seq.word 
"\push  \length    \catleft \t "

Function \push int -1

Function \length int -2

Function \catleft int -3

Function \t int -4

   use stack.seq.word
   

Function  runMachine( actno:int,actions:machine,strings:seq.seq.word,t:seq.word) seq.word
     for acc="",stk=empty:stack.seq.word,inst /in (actions.actions)_actno do
     if inst > 0 then next(acc+(constants.actions)_inst,stk)
      else if  inst < -length.otherinst then  
        next(acc+strings _ ( -length.otherinst -inst ),stk)
        else if inst=\push then
         next("",push( stk,acc))
       else if inst=\t then
         next(acc,push( stk,t))
        else if inst=\catleft then
          if isempty.stk then
           next(acc,stk)
          else next(top.stk+acc,pop.stk)
         else assert   inst=\length  report "???"
           next("~length"+%.length.acc+acc,stk)
       /do acc
      
Function makeInterperter(gin:seq.pegrule) machine
for acc0=machine(empty:seq.seq.word,[empty:seq.int]), r /in gin do 
  if kind.r ∈ "!" then acc0 else
   for acc = acc0, part ∈ parts.r do 
     let subs=otherinst+NonTerminals(part,gin) 
     for str="", consts=constants.acc,actions=empty:seq.int, w /in replacement.part do 
        let i= findindex(subs,w)
       if i > length.subs then
         next(str+w,consts,actions)
       else if isempty.str then
         next(str,consts,actions+[-i] )
       else 
         let j=findindex(consts,str)
         if j > length.consts then
           next("",consts+str,actions+[length.consts+1,-i])
         else 
           next("",consts+str,actions+[j,-i])
   /do  if isempty.str then
         machine(consts,actions.acc+actions)
        else 
             let k=findindex(consts,str)
         if k > length.consts then
           machine(consts+str,actions.acc+[actions+[length.consts+1]])
         else 
           machine(consts,actions.acc+[actions+k])
   /do acc
  /do 
  acc0
  
Function unparse(acc0:machine) seq.seq.word
 let z=otherinst+"\0 \1 \2 \3"
for   a2=empty:seq.seq.word,      a /in actions.acc0 do
      for a1="",  i /in a do
       a1+ if i < -length.z then [merge("\$(-i)")]
       else if i < 0 then [z_-i] else
              (constants.acc0)_i
      /do a2+a1
    /do a2


use otherseq.int
        

Function %table(t:seq.tableEntry)seq.word
for acc = "", rowno = 1, a ∈ t do
 next(
  acc
  + if action.action.a = actionReduce then
   "/row $(rowno) $(action.a) /cell $(%state.Fstate.a) /cell $(%state.Sstate.a) /cell"
  else
   "/row $(rowno) $(action.a) /cell $(match.a) /cell $(%state.Sstate.a) /cell $(%state.Fstate.a)
    "
  , rowno + 1)
/do "<* table $(acc) *>"

Function %state(i:state) seq.word
let action = action.i,
if action = state.0 then
 %.index.i
else
 ["T !Match MatchAny Success* Fail Success*! Match Reduce New!"_(toint.action + 1)]
 + if action = actionReduce then "." + %.index.i else ""

Function %(s:state) seq.word 
let action = action.s,
if action = Fail then
 "Fail"
else if action = actionReduce then
 "Reduce.$(index.s)"
else if action = Success* then
 "Success*"
else if action = Success*! then
 "Success*!"
else if action = MatchAny then
 "MatchAny"
else if action = Match then
 "Match"
else if action = !Match then
 "!Match"
else if action = New! then "New!" else "S.$(index.s)"

type state is toint:int

Export type:state

Export state(int)  state

function shift int 16

Function index(i:state) int toint.i / shift

Function =(a:state, b:state) boolean toint.a = toint.b

function MatchNT(state:state) state state

Function S(i:int) state  state(i * shift) 

Function Reduce(partno:int) state state(partno * shift + toint.actionReduce)

function actionReduce*(partno:int) state state.partno

function +(s:state, i:int) state state(toint.s + i * shift)

use bits

Function action(s:state) state state.toint(bits.toint.s ∧ 0xF)


Function !Match state {T}state.1

Function MatchAny state {T}state.2

Function Match state {T}state.3

Function NoTable(s:state) boolean   toint.s > 3 

Function Fail state {NT}state.4

Function Success*! state {NT}state.5

Function Success* state{NT} state.6

Function actionReduce state {NT}state.7

Function New! state {NT}state.8

/Function actionMatchNT state state.0

Function startstate state state.shift

Function funny(s:state) boolean toint.s = 0 