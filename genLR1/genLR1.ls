#!/usr/local/bin/tau

Library genLR1  tauparser genlex  testparser parse
 uses stdlib tools 
 exports tauparser genLR1 genlex testparser

Module genLR1

A paragraph of just a single word function crashes the compiler

/run genLR1 gentestgrammer

/run genLR1 gentau


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
 {"&br &quot"+ @(seperator."|", print,"", toseq.s)+"&br &quot"}

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
  {"??"+ @(+, isambiguous,"", actions)+"&br noactions"+ toword.length.actions +"&br nosymbols:"+ toword.length.alphabet +"alphabet:"+ alphabet +"&br norules"+ toword.length.grammarandact +"&br nostate"+ toword.length.mapping.estate +"&br follow"+ @(+, print,"", toseq.arcs.follow.graminfo)+ let a = @(addaction.alphabet, identity, dseq.0, actions)
   {"&br &br function tokenlist seq.word &quot"+ alphabet +"&quot"+"&br &br function startstate int"+ toword.initialstateno +"&br &br function actiontable seq.int ["+ @(seperator.",", toword,"", a)+"]"+"&br &br"+ generatereduce(grammarandact, alphabet)+"&br function printstate(stateno:int)seq.word &br ["+ @(seperator.",", print,"", mapping.estate)+"]_stateno"} }

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
 {"function reduce(stk:stack.stkele, ruleno:int)stack.stkele // generated function // 
 &br let rulelen = ["+ @(seperator.",", rulelength,"", grammarandact)+"]_ruleno 
 &br let newstk = pop(stk, rulelen)&br let subtrees = top(stk, rulelen)
 &br let newtree ="+ @(+, reduceline.grammarandact,"", arithseq(length.grammarandact, 1, 1))+
 "&br let leftsidetoken = ["+ @(seperator.",", leftside.alphabet,"", grammarandact)+"]_ruleno 
 &br let actioncode = actiontable_(leftsidetoken + length.tokenlist * stateno.top.newstk)&br assert actioncode > 0 report &quot ?? &quot 
 &br push(newstk, stkele(actioncode, newtree))"}

function rulelength(a:seq.seq.word)word toword(length(a_1) - 1)

function leftside(alphabet:seq.word, a:seq.seq.word)word toword.findindex(a_1_1, alphabet)

function replace$(w:word)seq.word 
 if w ="$"_1 then"result.subtrees"else [ w]

function reduceline(grammerandact:seq.seq.seq.word, i:int)seq.word 
 let s = grammerandact_i 
  if i = length.grammerandact 
  then"&br assert ruleno = //"+ s_1 +"//"+ toword.i +"report &quot invalid rule number &quot + toword.ruleno &br"+ @(+, replace$,"", s_2)
  else"&br if ruleno = //"+ s_1 +"//"+ toword.i +"then"+ @(+, replace$,"", s_2)+"else"

Function gentestgrammar seq.word lr1parser(testgrammar, empty:seq.seq.word)

Function testgrammar seq.seq.seq.word 
 [ ["G F #","$_1"], 
 ["F E","$_1"], 
 ["E 1","1"], 
 ["E 2","2"], 
 ["E 3","3"], 
 ["E E + E","$_1 + $_3"]]

Function gentau seq.word lr1parser(taurules, tauruleprec)

Function taurules seq.seq.seq.word 
 [ ["G F #","$_1"], 
 // Instead of making function a key word with rule"F function W T E"we use"F W W T E"// 
  ["F W W(P)T E", 
  "let P = sons.$_4 tree(label.$_1, [ tree(label.$_2, @(+, firstson, empty:seq.tree.word, P)+ $_6)]+ $_7 + P)"], 
 ["F W N(P)T E", 
 "let P = sons.$_4 tree(label.$_1, [ tree(label.$_2, @(+, firstson, empty:seq.tree.word, P)+ $_6)]+ $_7 + P)"], 
 ["F W W T E","tree(label.$_1, [ tree(label.$_2, [ $_3])]+ $_4)"], 
 ["F W W:T E", 
 "tree(label.$_1, [ tree(merge([ label.$_2]+ &quot:&quot + print.$_4), [ $_4]), $_5])"], 
 ["P T","tree(&quot P &quot_1, [ tree(&quot:&quot_1, [ $_1])])"], 
 ["P P, T","tree(&quot P &quot_1, sons.$_1 + tree(&quot:&quot_1, [ $_3]))"], 
 ["P W:T","tree(&quot P &quot_1, [ tree(label.$_1, [ $_3])])"], 
 ["P P, W:T","tree(&quot P &quot_1, sons.$_1 + tree(label.$_3, [ $_5]))"], 
 ["E W","$_1"], 
 ["E N(L)","tree(label.$_1, sons.$_3)"], 
 ["E W(L)","tree(label.$_1, sons.$_3)"], 
 ["E(E)","$_2"], 
 ["E { E }","$_2"], 
 ["E if E then E else E","tree(&quot if &quot_1, [ $_2, $_4, $_6])"], 
 ["E E^E","tree(label.$_2, [ $_1, $_3])"], 
 ["E E_E","tree(label.$_2, [ $_1, $_3])"], 
 ["E-E", 
 "let t = $_2 if nosons.t = 0 ∧ hasdigit(label.t)then tree(merge(&quot-&quot + label.t))else if nosons.t = 2 ∧ label.t = &quot makereal &quot_1 ∧ nosons.t_1 = 0 ∧ hasdigit(label.t_1)then tree(label.t, [ tree(merge(&quot-&quot + label.t_1)), t_2])else tree(&quot-&quot_1, [ $_2])"], 
 ["E W.E","tree(label.$_1, [ $_3])"], 
 ["E N.E","tree(label.$_1, [ $_3])"], 
 ["E E * E","tree(label.$_2, [ $_1, $_3])"], 
 ["E E-E","tree(label.$_2, [ $_1, $_3])"], 
 ["E E = E","tree(label.$_2, [ $_1, $_3])"], 
 ["E E ∧ E","tree(label.$_2, [ $_1, $_3])"], 
 ["E E ∨ E","tree(label.$_2, [ $_1, $_3])"], 
 ["L E","tree(&quot L &quot_1, [ $_1])"], 
 ["L L, E","tree(&quot L &quot_1, sons.$_1 + $_3)"], 
 ["E [ L]","tree(&quot $build &quot_1, sons.$_2)"], 
 ["E let W = E E","tree(&quot let &quot_1, [ $_2, $_4, $_5])"], 
 ["E assert E report E E","tree(&quot assert &quot_1, [ $_2, $_5, $_4])"], 
 ["E I","$_1"], 
 ["E I.I", 
 "let d = decode.label.$_3 tree(&quot makereal &quot_1, [ tree.encodeword(decode.label.$_1 + d), tree.countdigits(d, 1, 0)])"], 
 ["T W","$_1"], 
 ["T W.T","tree(label.$_1, [ $_3])"], 
 ["E W:T","tree(merge([ label.$_1, &quot:&quot_1]+ print.$_3))"], 
 ["E $wordlist","$_1"], 
 ["E comment E","tree(&quot comment &quot_1, [ $_2]+ sons.$_1)"], 
 ["N_","$_1"], 
 ["N-","$_1"], 
 ["N =","$_1"], 
 ["N *","$_1"], 
 ["N ∧","$_1"], 
 ["N ∨","$_1"], 
 ["K E","$_1"], 
 ["K N","$_1"], 
 ["E @(K, K, E, E)","tree(&quot @ &quot_1, [ $_3, $_5, $_7, $_9])"]]

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
 "E E = E", 
 "=", 
 "E E ∧ E", 
 "∧", 
 "E E ∨ E", 
 "∨"]

