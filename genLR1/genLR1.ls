#!/usr/local/bin/tau

Library genLR1    genlex   
 uses stdlib  
 exports   genLR1 genlex 

Module genLR1

A paragraph of just a single word function crashes the compiler

/run genLR1 gentestgrammar2

run genLR1 gentau2


run tauparser test2

use graph.word

use ipair.seq.word

use oseq.int

use oseq.seq.word

use oseq.word

use seq.action

use seq.arc.word

use seq.int

use seq.ipair.seq.word

use seq.seq.seq.word

use seq.seq.word

use seq.set.ipair.seq.word

use seq.word

use set.arc.word

use set.ipair.seq.word

use set.word

use stdlib

type estate is encoding set.ipair.seq.word

type action is record stateno:int, lookahead:word, codedaction:int

type grammarinfo is record grammar:seq.seq.word, follow:graph.word, ruleprec:seq.seq.word

function =(a:ipair.seq.word, b:ipair.seq.word)boolean value.a = value.b ∧ index.a = index.b

function ?(a:ipair.seq.word, b:ipair.seq.word)ordering value.a ? value.b ∧ index.a ? index.b

function hash(p:ipair.seq.word)int hash.value.p + index.p

function =(a:action, b:action)boolean lookahead.a = lookahead.b ∧ stateno.a = stateno.b

function hash(s:set.ipair.seq.word)int hash(toseq(s)_1)

function backarc(tail:word, head:word)arc.word arc(head, tail)

function follow1(s:seq.word, i:int)arc.word 
 assert i > 1 ∧ i < length.s report s + toword.i 
  arc(s_i, s_(i + 1))

function follow2(rule:seq.word)seq.arc.word 
 @(+, follow1.rule, empty:seq.arc.word, arithseq(length.rule - 2, 1, 2))

function follow(grammar:seq.seq.word)graph.word 
 follow(newgraph.@(+, follow2, empty:seq.arc.word, grammar), grammar)

function follow3(g:graph.word, rule:seq.word)seq.arc.word 
 let a = @(+, arc.last.rule, empty:seq.arc.word, toseq.successors(g, rule_1))
  @(+, backarc(rule_2), a, toseq.predecessors(g, rule_1))

function follow(g:graph.word, grammar:seq.seq.word)graph.word 
 let g2 = @(+, follow3.g, g, grammar)
  if g = g2 then g else follow(g2, grammar)

function ruleno(grammar:seq.seq.word, rule:seq.word)int 
 let ruleno = if rule =""then 0 else findindex(rule, grammar)
  assert ruleno ≤ length.grammar report"rule not found"+ rule 
  ruleno

function state(stateno:int)set.ipair.seq.word 
 if stateno = 0 then empty:set.ipair.seq.word else mapping(estate)_stateno

function shift(stateno:int, lookahead:word, newstateno:int)action action(stateno, lookahead, newstateno)

function reduce(stateno:int, lookahead:word, ruleno:int)action action(stateno, lookahead,-ruleno)

function getaction(ruleprec:seq.seq.word, grammar:seq.seq.word, state:set.ipair.seq.word, stateno:int, reductions:seq.seq.word, lookahead:word)action 
 let newstate = advance(grammar, state, lookahead)
  let newstateno = if not.isempty.newstate then encoding.encode(newstate, estate)else 0 
  if length.reductions = 0 ∧ newstateno ≠ 0 
  then shift(stateno, lookahead, newstateno)
  else if length.reductions = 1 ∧ newstateno = 0 
  then reduce(stateno, lookahead, ruleno(grammar, reductions_1))
  else let lookplace = findindex([ lookahead], ruleprec)
  let yy = if lookplace > length.ruleprec 
   then empty:seq.seq.word 
   else @(+, tosubstate.reductions, empty:seq.seq.word, subseq(ruleprec, 1, lookplace - 1))
  if length.yy = 1 
  then reduce(stateno, lookahead, ruleno(grammar, yy_1))
  else if length.yy = 0 ∧ newstateno ≠ 0 
  then shift(stateno, lookahead, newstateno)
  else let r = if length.yy = 0 then reductions else yy 
  if length.r = 2 ∧ r_1 ="E-E"∧ r_2 ="E E-E"
  then // assert false report"<>"+ lookahead + toword.length.yy + print.r // 
   reduce(stateno, lookahead, ruleno(grammar, r_2))
  else // ERROR ambiguous // action(stateno, lookahead, 0)

function print(a:seq.seq.word)seq.word @(seperator."&br", identity,"", a)

function printstate(stateno:int)seq.word [ toword.stateno]

function alphabet(grammar:seq.seq.word)seq.word toseq.asset.@(+, identity,"", grammar)

function addaction(alphabet:seq.word, table:seq.int, a:action)seq.int 
 replace(table, findindex(lookahead.a, alphabet)+ length.alphabet * stateno.a, codedaction.a)

function first(a:seq.seq.word)seq.word a_1

function first(a:seq.word)word a_1

function tosubstate(state:seq.seq.word, rule:seq.word)seq.seq.word 
 if rule in state then [ rule]else empty:seq.seq.word

function print(p:ipair.seq.word)seq.word 
 subseq(value.p, 1, index.p - 1)+"'"+ subseq(value.p, index.p, length.value.p)

function print(s:set.ipair.seq.word)seq.word 
 {"&br  &quot "+ @(seperator."|", print,"", toseq.s)+"&br  &quot "}

Function initialstate(grammar:seq.seq.word)set.ipair.seq.word 
 close(grammar, asset.[ ipair(2,"G F #")])

function close(g:seq.seq.word, s:set.ipair.seq.word)set.ipair.seq.word 
 let newset = @(∪, close.g, s, toseq.s)
  if s = newset then s else close(g, newset)

function close(g:seq.seq.word, p:ipair.seq.word)set.ipair.seq.word 
 if index.p > length.value.p 
  then empty:set.ipair.seq.word 
  else asset.@(+, startswith(value(p)_index.p), empty:seq.ipair.seq.word, g)

function startswith(first:word, x:seq.word)seq.ipair.seq.word 
 if x_1 = first then [ ipair(2, x)]else empty:seq.ipair.seq.word

function advance(g:seq.seq.word, state:set.ipair.seq.word, next:word)set.ipair.seq.word 
 close(g, asset.@(+, advance.next, empty:seq.ipair.seq.word, toseq.state))

function advance(next:word, p:ipair.seq.word)seq.ipair.seq.word 
 if index.p ≤ length.value.p ∧ value(p)_index.p = next 
  then [ ipair(index.p + 1, value.p)]
  else empty:seq.ipair.seq.word

function finished(p:ipair.seq.word)seq.seq.word 
 if index.p = length.value.p + 1 then [ value.p]else empty:seq.seq.word

function finished(s:set.ipair.seq.word)seq.seq.word @(+, finished, empty:seq.seq.word, toseq.s)

function shifts(p:ipair.seq.word)seq.word 
 if index.p = length.value.p + 1 then empty:seq.word else [ value(p)_index.p]

function shifts(s:set.ipair.seq.word)seq.word toseq.asset.@(+, shifts, empty:seq.word, toseq.s)

function lr1parser(grammarandact:seq.seq.seq.word, ruleprec:seq.seq.word)seq.word 
 let grammar2 = @(+, first, empty:seq.seq.word, grammarandact)
  let initialstateno = encoding.encode(initialstate.grammar2, estate)
  let alphabet = alphabet.grammar2 
  let graminfo = grammarinfo(grammar2, follow.grammar2, ruleprec)
  let actions = closestate(graminfo, 1, empty:seq.action)
  let amb=@(+, isambiguous,"", actions)
    { if length.amb > 0 then "ambiguous actions:"+amb else "" }
   +"&br noactions"+ toword.length.actions +"&br nosymbols:"+ toword.length.alphabet +"alphabet:"+ alphabet +
   "&br norules"+ toword.length.grammarandact +"&br nostate"+ toword.length.mapping.estate +
   "&br follow"+ @(+, print,"", toseq.arcs.follow.graminfo)+ let a = @(addaction.alphabet, identity, dseq.0, actions)
   {"&br &br function tokenlist seq.word  &quot "+ alphabet +" &quot "+"&br
    &br function startstate int"+ toword.initialstateno +"&br 
    &br function actiontable seq.int ["+ @(seperator.",", toword,"", a)+"]"+
    "&br &br"+ generatereduce(grammarandact, alphabet)+"&br &br function printstate(stateno:int)seq.word 
    &br ["+ @(seperator.",", print,"", mapping.estate)+"]_stateno"} 

function isambiguous(a:action)seq.word 
 if codedaction.a = 0 then"&br"+ toword.stateno.a + lookahead.a else""

function print(a:arc.word)seq.word [ tail.a]+">"+ head.a

function closestate(graminfo:grammarinfo, stateno:int, result:seq.action)seq.action 
 let m = mapping.estate 
  if stateno > length.m 
  then result 
  else let state = m_stateno 
  let reductions = finished.state 
  let follows = @(∪, successors.follow.graminfo, empty:set.word, @(+, first,"", reductions))
  let newresult = @(+, getaction(ruleprec.graminfo, grammar.graminfo, state, stateno, reductions), result, toseq(asset.shifts.state ∪ follows))
  closestate(graminfo, stateno + 1, newresult)

Function generatereduce(grammarandact:seq.seq.seq.word, alphabet:seq.word)seq.word 
 {"function reduce(stk:stack.stkele, ruleno:int,place:int,input:seq.word)stack.stkele // generated function // 
 &br let rulelen = ["+ @(seperator.",", rulelength,"", grammarandact)+"]_ruleno 
 &br let newstk = pop(stk, rulelen)&br let subtrees = top(stk, rulelen)
 &br let dict = dict.result.top.stk
 &br let newtree ="+ @(+, reduceline.grammarandact,"", arithseq(length.grammarandact, 1, 1))+
 "&br let leftsidetoken = ["+ @(seperator.",", leftside.alphabet,"", grammarandact)+"]_ruleno 
 &br let actioncode = actiontable_(leftsidetoken + length.tokenlist * stateno.top.newstk)&br assert actioncode > 0 report  &quot  ??  &quot  
 &br push(newstk, stkele(actioncode, newtree))"}

function rulelength(a:seq.seq.word)word toword(length(a_1) - 1)

function leftside(alphabet:seq.word, a:seq.seq.word)word toword.findindex(a_1_1, alphabet)

function replace$(w:word)seq.word 
 if w ="$"_1 then"result.subtrees"else [ w]

function reduceline(grammerandact:seq.seq.seq.word, i:int)seq.word 
 let s = grammerandact_i 
  if i = length.grammerandact 
  then"&br assert ruleno = //"+ s_1 +"//"+ toword.i +"report  &quot  invalid rule number  &quot  + toword.ruleno &br"+ @(+, replace$,"", s_2)
  else"&br if ruleno = //"+ s_1 +"//"+ toword.i +"then"+ @(+, replace$,"", s_2)+"else"

Function gentestgrammar seq.word lr1parser(testgrammar, empty:seq.seq.word)

Function gentestgrammar2 seq.word lr1parser(testgrammar2, empty:seq.seq.word)


Function testgrammar seq.seq.seq.word 
 [ ["G F #","$_1"], 
 ["F E","$_1"], 
 ["E 1","1"], 
 ["E 2","2"], 
 ["E 3","3"], 
 ["E E + E","$_1 + $_3"]]
 
 
Function testgrammar2 seq.seq.seq.word 
 [ ["G F #","$_1"], 
 ["F E","$_1"], 
 [" E W "," 
let id=code.$_1
if hasdigit.id_1 then bindinfo(dict.$_1, id, [mytype(  &quot  int  &quot  )])
else let f = lookup(dict.$_1,  id_1 ,empty:seq.mytype ) assert not.isempty.f report  &quot  cannot find   &quot  +id
bindinfo(dict.$_1,  [mangledname.f_1], [resulttype.f_1]) 
"],
[" A let W = E ","  
let e = $_4 let name= (code.$_2)_1
let newdict=dict.$_1 +symbol(name,mytype(  &quot  local  &quot  ),empty:seq.mytype,(types.e)_1)
     bindinfo(newdict,code.e +   &quot  define  &quot  +name,types.e)
"],
[" E A E "," 
let dict=dict.$_1
  let f=lookup( dict,last.code.$_1,empty:seq.mytype)
  assert not.isempty.f report   &quot  error  &quot  
bindinfo(dict.$_1 - f,code.$_1 + code.$_2 +   &quot  undefine  &quot  , types.$_2 )
"],
[" E E + E "," 
let types = types.$_1 + types.$_3 
let f = lookup(dict.$_1,    &quot  +  &quot  _1 ,types )assert not.isempty.f report  &quot  cannot find +  &quot  
bindinfo(dict.$_1, code.$_1 + code.$_3 + mangledname.f_1, [resulttype.f_1]) 
"]]


Function gentau seq.word lr1parser(taurules, tauruleprec)



Function taurules seq.seq.seq.word 
 [ ["G F #","$_1"], 
 // Instead of making function a key word with rule"F function W T E"we use"F W W T E"// 
  ["F W W(P)T E", 
  "let P = sons.$_4 tree(label.$_1, [ tree(label.$_2, @(+, firstson, empty:seq.tree.word, P)+ $_6)]+ $_7 + P)"], 
 ["F W N(P)T E", 
 "let P = sons.$_4 tree(label.$_1, [ tree(label.$_2, @(+, firstson, empty:seq.tree.word, P)+ $_6)]+ $_7 + P)"], 
 ["F W W T E", "tree(label.$_1, [ tree(label.$_2, [ $_3])]+ $_4)"], 
 ["F W W:T E", "tree(label.$_1, [ tree(merge([ label.$_2]+ &quot  :  &quot + print.$_4), [ $_4]), $_5]) "],
 ["F W W is W P",
 "let s=sons.result.subtrees_5 let kind=label.result.subtrees_4
 let q=if kind in  &quot  encoding Encoding &quot _1 then    [s_1_1] else @(+,insertson.[result.subtrees_2],empty:seq.tree.word,s)
tree(if kind= &quot  record  &quot _1 then  &quot  struct  &quot _1 else kind, [result.subtrees_2]+q)"],
 [ "F W T" , "tree(label.$_1, [$_2])"],
 ["P T","tree( &quot  P  &quot _1, [ tree( &quot : &quot _1, [ $_1])])"], 
 ["P P, T","tree( &quot  P  &quot _1, sons.$_1 + tree( &quot : &quot _1, [ $_3]))"], 
 ["P W:T","tree( &quot  P  &quot _1, [ tree(label.$_1, [ $_3])])"], 
 ["P P, W:T","tree( &quot  P  &quot _1, sons.$_1 + tree(label.$_3, [ $_5]))"], 
 ["E W","$_1"], 
 ["E N(L)","tree(label.$_1, sons.$_3)"], 
 ["E W(L)","tree(label.$_1, sons.$_3)"], 
 ["E(E)","$_2"], 
 ["E { E }","$_2"], 
 ["E if E then E else E","tree( &quot  if  &quot _1, [ $_2, $_4, $_6])"], 
 ["E E^E","tree(label.$_2, [ $_1, $_3])"], 
 ["E E_E","tree(label.$_2, [ $_1, $_3])"], 
 ["E-E", 
 "let t = $_2 if nosons.t = 0 ∧ hasdigit(label.t)then tree(merge( &quot - &quot  + label.t))else if nosons.t = 2 ∧ label.t =  &quot  makereal  &quot _1 ∧ nosons.t_1 = 0 ∧ hasdigit(label.t_1)then tree(label.t, [ tree(merge( &quot - &quot  + label.t_1)), t_2])else tree( &quot - &quot _1, [ $_2])"], 
 ["E W.E","tree(label.$_1, [ $_3])"], 
 ["E N.E","tree(label.$_1, [ $_3])"], 
 ["E E * E","tree(label.$_2, [ $_1, $_3])"], 
 ["E E-E","tree(label.$_2, [ $_1, $_3])"], 
 ["E E = E","tree(label.$_2, [ $_1, $_3])"], 
 ["E E > E","tree(label.$_2, [ $_1, $_3])"], 
 ["E E ∧ E","tree(label.$_2, [ $_1, $_3])"], 
 ["E E ∨ E","tree(label.$_2, [ $_1, $_3])"], 
 ["L E","tree( &quot  L  &quot _1, [ $_1])"], 
 ["L L, E","tree( &quot  L  &quot _1, sons.$_1 + $_3)"], 
 ["E [ L]","tree( &quot  $build  &quot _1, sons.$_2)"], 
 [ "A let W = E"  ,"tree( &quot  let  &quot _1,[ $_2, $_4])"],
 ["E A E", "let a = $_1 tree( &quot  let  &quot _1, [ a_1, a_2, $_2])"], 
 ["E assert E report E E","tree( &quot  assert  &quot _1, [ $_2, $_5, $_4])"], 
 ["E I","$_1"], 
 ["E I.I", 
 "let d = decode.label.$_3 tree( &quot  makereal  &quot _1, [ tree.encodeword(decode.label.$_1 + d), tree.countdigits(d, 1, 0)])"], 
 ["T W","$_1"], 
 ["T W.T","tree(label.$_1, [ $_3])"], 
 ["E W:T","tree(merge([ label.$_1,  &quot : &quot _1]+ print.$_3))"], 
 ["E $wordlist","$_1"], 
 ["E comment E","tree( &quot  comment  &quot _1, [ $_2]+ sons.$_1)"], 
 ["N_","$_1"], 
 ["N-","$_1"], 
 ["N =","$_1"], 
 ["N >","$_1"], 
 ["N *","$_1"], 
 ["N ∧","$_1"], 
 ["N ∨","$_1"], 
 ["K E","$_1"], 
 ["K N","$_1"], 
 ["E @(K, K, E, E)","tree( &quot  @  &quot _1, [ $_3, $_5, $_7, $_9])"]]

function tauruleprec seq.seq.word 
 ["E E_E", 
 "_", 
 "E comment E", 
 "E W.E", 
 "E N.E", 
 ".", 
 "E E * E", 
 "*", 
 "E-E", 
 "E E-E", 
 "-", 
 "E E > E",
 "E E = E", 
 "=", ">",
 "E E ∧ E", 
 "∧", 
 "E E ∨ E", 
 "∨"]


Function gentau2 seq.word     lr1parser(taurules2, tauruleprec)





function taurules2 seq.seq.seq.word
[[" G F # ","  $_1  
"],[" F W W(FP)T E ","let functype=code.$_6
   let exptype=types.$_7
   assert mytype.functype=exptype_1 &or exptype_1=mytype.&quot  internal &quot   report  &quot  function type of &quot  +print.mytype.functype+ &quot  does not match expression type  &quot  +print.exptype_1
    bindinfo(dict,code.$_7,[ mytype.code.$_2,mytype.functype]+types.$_4)    
"],[" F W N(FP)T E ","let functype=code.$_6
   let exptype=types.$_7
   assert mytype.functype=exptype_1 &or exptype_1=mytype.&quot  internal &quot   report  &quot  function type of &quot  +print.mytype.functype+ &quot  does not match expression type  &quot  +print.exptype_1
    bindinfo(dict,code.$_7,[ mytype.code.$_2,mytype.functype]+types.$_4)    
"],[" F W W T E ","
   let functype=code.$_3
   let exptype=types.$_4
   assert mytype.functype=exptype_1 &or exptype_1=mytype.&quot  internal &quot   report  &quot  function type of  &quot  +print.mytype.functype+ &quot  does not match expression type  &quot  +print.exptype_1
    bindinfo(dict,code.$_4,[ mytype.code.$_2,mytype.functype])     
"],[" F W W:T E ","
let functype=code.$_4
   let exptype=types.$_5
   assert mytype.functype=exptype_1 &or exptype_1=mytype.&quot  internal &quot   report  &quot  function type of &quot  +print.mytype.functype+ &quot  does not match expression type &quot  +print.exptype_1
bindinfo(dict,code.$_5,[ mytype.[merge(code.$_2+ &quot  : &quot  +print.mytype.functype)],mytype.functype])
 "],[" F W W is W P ","bindinfo(dict,code.$_4+code.$_2+@(+,cvttotext,&quot &quot,types.$_5)
,types.$_5)  
"],[" F W T "," $_2  
"],[" FP  P ","bindinfo(@(addparameter.cardinality.dict,identity,dict,types.$_1 ), &quot &quot,
   @(+,parameter,empty:seq.mytype,types.$_1))  "],
[" P T "," bindinfo(dict, &quot   &quot  ,[ mytype(code.$_1+&quot : &quot)])   
"],[" P P, T "," bindinfo(dict, &quot   &quot  ,types.$_1+[ mytype(code.$_3+&quot : &quot)])  
"],[" P W:T "," 
    bindinfo(dict, &quot   &quot  ,[ mytype(code.$_3+code.$_1)])   
"],[" P P, W:T "," 
bindinfo(dict, &quot   &quot  ,types.$_1+[ mytype(code.$_5+code.$_3)])  
"],[" E W ","let id = code.$_1 
let f = lookup(dict, id_1, empty:seq.mytype)
assert not.isempty.f report  errormessage(&quot  cannot find id &quot  + id ,input,place)
bindinfo(dict, [ mangledname.f_1], [ resulttype.f_1]) 
"],[" E N(L) ","unaryop( $_1,$_3,input,place)  
"],[" E W(L) ","unaryop( $_1,$_3,input,place)  
"],[" E(E) ","$_2  
"],[" E { E } ","$_2  
"],[" E if E then E else E ","
let thenpart=$_4
assert (types.$_2)_1 =mytype.&quot  boolean &quot   report  &quot  cond of if must be boolean &quot  
assert (types.$_4) =(types.$_6) report  &quot  then and else types are different &quot  
  let newcode= code.$_2 + code.$_4 + code.$_6 
   bindinfo(dict,newcode+  &quot  if &quot  ,types.thenpart)
"],[" E E^E ","opaction(subtrees,input,place)  
"],[" E E_E ","opaction(subtrees,input,place)  
"],[" E-E ","unaryop( $_1,$_2,input,place)  
"],[" E W.E ","unaryop( $_1,$_3,input,place)  
"],[" E N.E ","unaryop( $_1,$_3,input,place)  
"],[" E E * E ","opaction(subtrees,input,place)  
"],[" E E-E ","opaction(subtrees,input,place)
"],[" E E = E ","opaction(subtrees,input,place)  
"],[" E E > E ","opaction(subtrees,input,place) 
"],[" E E ∧ E ","opaction(subtrees,input,place)  
"],[" E E ∨ E "," opaction(subtrees,input,place)  
"],[" L E ","$_1  
"],[" L L, E ","
bindinfo(dict,code.$_1+code.$_3,types.$_1+types.$_3)
"],[" E [ L]","
 let types=types($_2)
 assert @(∧, =(types_1), true, types )report  &quot  types do not match in build &quot   
    bindinfo( dict,&quot LIT 0 LIT  &quot+toword.(length.types)+ code.$_2+ &quot  RECORD &quot  +toword.(length.types+2), [mytype(towords(types_1)+ &quot  seq &quot   )])
 "],[" A let W = E "," let e = $_4 let name =(code.$_2)_1 
let newdict = dict + symbol(name, mytype( &quot  local &quot  ), empty:seq.mytype,(types.e)_1,&quot &quot)
bindinfo(newdict, code.e + &quot  define &quot  + name, types.e)
"],
[" E A E ","let t = code.$_1 let f = lookup(dict, last.code.$_1, empty:seq.mytype)
assert not.isempty.f report  &quot  error &quot  bindinfo(dict.$_1-f_1, subseq(t,1,length.t-2) + code.$_2 + &quot  SET &quot +last.code.$_1 , types.$_2)
"],[" E assert E report E E ","
assert types($_2)_1 = mytype.&quot  boolean &quot  report  &quot  condition in assert must be boolean in: &quot    
  assert types($_4)_1 = mytype.&quot  word seq &quot  report  &quot  report in assert must be seq of word in: &quot   
  let newcode=code.$_2 + code.$_5 + code.$_4 +   &quot  assertZbuiltinZwordzseq   if  &quot   
  bindinfo(dict,newcode,types.$_5)
"],[" E I ","$_1  
"],[" E I.I "," let d = decode.(code.$_3)_2 
bindinfo(dict, &quot LIT &quot +[ encodeword(decode.(code.$_1)_2 + d)]+&quot LIT &quot +countdigits(d, 1, 0)+&quot  makerealZrealZintZint  &quot ,[mytype.&quot  real  &quot] )
"],[" T W ","$_1  
"],[" T W.T ","bindinfo(dict,code.$_3+code.$_1,types.$_1)  
"],[" E W:T ","
let f = lookup(dict,  merge(code.$_1 + &quot :  &quot+ print.mytype.code.$_3), empty:seq.mytype)
assert not.isempty.f report errormessage( &quot cannot find  &quot+ code.$_1 + &quot: &quot+ print.mytype.code.$_3,input,place)
bindinfo(dict, [ mangledname.f_1], [ resulttype.f_1])
"],[" E $wordlist ","let s = code.$_1
   bindinfo(dict,  &quot  WORDS &quot  +toword.length.s+s,[mytype.&quot  word seq &quot  ])
"],[" E comment E "," $_2  
"],[" N_","$_1  
"],[" N-","$_1  
"],[" N = "," $_1  
"],[" N > "," $_1  
"],[" N * "," $_1  
"],[" N ∧ "," $_1  
"],[" N ∨ ","  $_1  
"],[" K W.E "," bindinfo(dict, code.$_1+code.$_3,types.$_3) 
"],[" K N.E "," bindinfo(dict, code.$_1+code.$_3,types.$_3) 
"],[" K N(L) "," bindinfo(dict, code.$_1+code.$_3,types.$_3)   
"],[" K W(L) "," bindinfo(dict, code.$_1+code.$_3,types.$_3)  
"],[" K N "," bindinfo(dict, code.$_1,empty:seq.mytype) 
"],[" K W "," bindinfo(dict, code.$_1,empty:seq.mytype)     
"],[" E @(K, K, E, E) ","apply($_3,$_5,$_7,$_9)"]
]

