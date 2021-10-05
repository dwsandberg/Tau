#!/usr/local/bin/tau ; use genLR1 ; gentau2

gentau2

Module genLR1

use format

use standard

use otherseq.action

use seq.action

use otherseq.action2

use seq.action2

use seq.dottedrule

use set.dottedrule

use otherseq.int

use seq.int

use set.int

use sparseseq.int

use otherseq.ruleprec

use seq.ruleprec

use encoding.state

use seq.state

use graph.word

use otherseq.word

use seq.word

use set.word

use stack.word

use seq.seq.action

use seq.set.dottedrule

use seq.encodingpair.state

use seq.arc.word

use set.arc.word

use otherseq.seq.word

use seq.seq.word

use stack.seq.word

use seq.seq.seq.word

type state is toset:set.dottedrule

type dottedrule is place:int, rule:seq.word

type action is stateno:int, lookahead:word, codedaction:int

type grammarinfo is grammar:seq.seq.word, follow:graph.word, ruleprec:seq.seq.word

function =(a:state, b:state)boolean toset.a = toset.b

function =(a:dottedrule, b:dottedrule)boolean rule.a = rule.b ∧ place.a = place.b

function ?(a:dottedrule, b:dottedrule)ordering rule.a ? rule.b ∧ place.a ? place.b

function hash(p:dottedrule)int hash.rule.p + place.p

function assignencoding(p:seq.encodingpair.state, a:state)int length.p + 1

function =(a:action, b:action)boolean lookahead.a = lookahead.b ∧ stateno.a = stateno.b

function ?(a:action, b:action)ordering lookahead.a ? lookahead.b ∧ stateno.a ? stateno.b

type action2 is toaction:action

function ?(a1:action2, b1:action2)ordering
let a = toaction.a1
let b = toaction.b1
stateno.a ? stateno.b ∧ codedaction.a ? codedaction.b ∧ lookahead.a ? lookahead.b

function print(a:action)seq.word
" /br state:" + toword.stateno.a + "lookahead:" + lookahead.a
+ if codedaction.a < 0 then"reduce" + toword.-codedaction.a
else"shift" + toword.codedaction.a

function print(grammar:seq.seq.word, actions:seq.action)seq.word
let d = sort.for b = empty:seq.action2, a ∈ actions do b + action2.a /for(b)
let c = for b = empty:seq.action, a ∈ d do b + toaction.a /for(b)
print(grammar, c, 1,-1, 0,"")

function print(grammar:seq.seq.word, a:seq.action, i:int, laststate:int, lastaction:int, result:seq.word)seq.word
if i > length.a then result
else
 let this = a_i
 let p1 =
  if laststate ≠ stateno.this then
   if laststate > 0 then print.decode.to:encoding.state(laststate)else""/if
   + " /br state:"
   + toword.stateno.this
  else""
 let p2 =
  if lastaction ≠ codedaction.this then
   if codedaction.this < 0 then"reduce" + grammar_(-codedaction.this) + ";"
   else"shift" + toword.codedaction.this
  else""
 print(grammar, a, i + 1, stateno.this, codedaction.this, result + p1 + p2 + lookahead.this)

function hash(s:state)int hash.(toseq.toset.s)_1

/function print(a:seq.arc.word)seq.word for arc ∈ a, b ="",,, b + tail.arc + head.arc

function follow(grammar:seq.seq.word)graph.word
let allarcs =
 for acc = empty:seq.arc.word, rule ∈ grammar do
  acc
  + for arcs = empty:seq.arc.word, i = 1, e ∈ rule do
   next(if i > 2 then arcs + arc(rule_(i - 1), rule_i)else arcs, i + 1)
  /for(arcs)
 /for(acc)
follow(newgraph.allarcs, grammar)

function follow(g:graph.word, grammar:seq.seq.word)graph.word
let g2 =
 for newgraph = g, rule ∈ grammar do
  let a =
   for acc = empty:seq.arc.word, succ ∈ toseq.successors(g, rule_1)do acc + arc(last.rule, succ)/for(acc)
  newgraph
  + for acc = a, pred ∈ toseq.predecessors(g, rule_1)do acc + arc(pred, rule_2)/for(acc)
 /for(newgraph)
if g = g2 then g else follow(g2, grammar)

function ruleno(grammar:seq.seq.word, rule:seq.word)int
let ruleno = if rule = ""then 0 else findindex(rule, grammar)
assert ruleno ≤ length.grammar report"rule not found" + rule
ruleno

function state(stateno:int)state
if stateno = 0 then state.empty:set.dottedrule else data.encoding:seq.encodingpair.state_stateno

function shift(stateno:int, lookahead:word, newstateno:int)action action(stateno, lookahead, newstateno)

function reduce(stateno:int, lookahead:word, ruleno:int)action action(stateno, lookahead,-ruleno)

type ruleprec is lookahead:word, rules:seq.int

function print(grammar:seq.seq.word, p:ruleprec)seq.word
"lookahead:" + lookahead.p
+ for acc ="", @e ∈ rules.p do acc + grammar_@e + " /br |"/for(acc >> 2)

function =(a:ruleprec, b:ruleprec)boolean lookahead.a = lookahead.b

function print(a:seq.seq.word)seq.word
for acc ="", @e ∈ a do acc + @e + " /br"/for(acc >> 1)

function print(p:dottedrule)seq.word
subseq(rule.p, 1, place.p - 1) + "'" + subseq(rule.p, place.p, length.rule.p)

function print(s:state)seq.word
for acc = '  /br ', dotrule ∈ toseq.toset.s do acc + print.dotrule + " /br |"/for(acc >> 2)

Function initialstate(grammar:seq.seq.word)set.dottedrule close2(grammar, asset.[ dottedrule(2,"G F #")])

Function finalstate(grammar:seq.seq.word)set.dottedrule close2(grammar, asset.[ dottedrule(3,"G F #")])

function close2(g:seq.seq.word, s:set.dottedrule)set.dottedrule
let newset = for acc = s, dotrule ∈ toseq.s do acc ∪ close(g, dotrule)/for(acc)
if s = newset then s else close2(g, newset)

function close(grammar:seq.seq.word, p:dottedrule)set.dottedrule
if place.p > length.rule.p then empty:set.dottedrule
else
 asset.for acc = empty:seq.dottedrule, rule ∈ grammar do
  if rule_1 = (rule.p)_(place.p)then acc + dottedrule(2, rule)else acc
 /for(acc)

function advance(g:seq.seq.word, state:set.dottedrule, next:word)set.dottedrule
close2(g
, asset.for acc = empty:seq.dottedrule, p ∈ toseq.state do
 if place.p ≤ length.rule.p ∧ (rule.p)_(place.p) = next then acc + dottedrule(place.p + 1, rule.p)
 else acc
/for(acc)
)

function finished(s:state)seq.seq.word
for acc = empty:seq.seq.word, p ∈ toseq.toset.s do
 acc + if place.p = length.rule.p + 1 then [ rule.p]else empty:seq.seq.word
/for(acc)

function shifts(s:state)seq.word
toseq.asset.for acc = empty:seq.word, p ∈ toseq.toset.s do
 acc
 + if place.p = length.rule.p + 1 then empty:seq.word else [(rule.p)_(place.p)]
/for(acc)

function resolveamb(ruleprec:seq.seq.word, grammar:seq.seq.word, dup:seq.action)seq.action
if length.dup = 1 then dup
else if length.dup ≥ 2 ∧ codedaction.dup_1 < 0 ∧ codedaction.dup_2 < 0 then
 { contains reduce reduce conflict }
 let rule1 = grammar_(-codedaction.dup_1)
 let rule2 = grammar_(-codedaction.dup_2)
 let reducepos1 =
  for r = 0, i = 1, p ∈ ruleprec while r = 0 do next(if length.p > 1 ∧ p = rule1 then i else 0, i + 1)/for(r)
 let reducepos2 =
  for r = 0, i = 1, p ∈ ruleprec while r = 0 do next(if length.p > 1 ∧ p = rule2 then i else 0, i + 1)/for(r)
 if reducepos1 = 0 ∧ reducepos2 = 0 then dup
 else
  resolveamb(ruleprec
  , grammar
  , if between(reducepos1, 1, reducepos2)then [ dup_1] + dup << 2 else dup << 1
  )
else if length.dup = 2 ∧ codedaction.dup_1 < 0 ∧ codedaction.dup_2 > 0 then
 let rule1 = grammar_(-codedaction.dup_1)
 let shiftpos =
  for r = 0, i = 1, p ∈ ruleprec while r = 0 do next(if length.p = 1 ∧ p_1 = lookahead.dup_2 then i else 0, i + 1)/for(r)
 let reducepos =
  for r = 0, i = 1, p ∈ ruleprec while r = 0 do next(if length.p > 1 ∧ p = rule1 then i else 0, i + 1)/for(r)
 if between(reducepos, 1, shiftpos)then { choose reduce } [ dup_1]
 else if between(shiftpos, 1, reducepos)then { choose shift } [ dup_2]else dup
else dup

Function lr1parser(grammarandact:seq.seq.seq.word, ruleprec:seq.seq.word, terminals:seq.word, attributename:seq.word)seq.word
let grammar2 = for acc = empty:seq.seq.word, @e ∈ grammarandact do acc + first.@e /for(acc)
let nontermials = for acc = empty:set.word, rule ∈ grammar2 do acc + first.rule /for(acc)
assert isempty(asset.terminals ∩ nontermials)report"terminals and nontermials sets must be distinct"
let alphabet = terminals + toseq.nontermials
let initialstateno = valueofencoding.encode.state.initialstate.grammar2
let finalstateno = valueofencoding.encode.state.finalstate.grammar2
let symbolsused = for acc = empty:set.word, rule ∈ grammar2 do acc ∪ asset.rule /for(acc)
let missingsymbols = symbolsused \ asset.alphabet
assert isempty(symbolsused \ asset.alphabet)
report"Symbols not included in alphabet" + toseq(symbolsused \ asset.alphabet)
assert isempty(asset.alphabet \ symbolsused)
report"Symbols in alphabet but not used" + toseq(asset.alphabet \ symbolsused)
let k =
 for problems ="", item ∈ ruleprec do
  problems
  + if length.item = 1 ∧ item_1 ∉ alphabet then"lookahead" + item + "is not in alphabet"
  else if length.item > 1 ∧ item ∉ grammar2 then"rule is not in grammar:" + item else""
 /for(problems)
assert isempty.k report"ruleprec problem" + k
let graminfo = grammarinfo(grammar2, follow.grammar2, ruleprec)
let actions = closestate(graminfo, 1, empty:seq.action, asset.terminals)
{ assert false report print(grammar2, actions)}
let dups = dups.actions
let actions2 =
 for acc = empty:seq.seq.action, @e ∈ dups.actions do acc + resolveamb(ruleprec, grammar2, @e)/for(acc)
let actions3 = for acc = empty:seq.action, @e ∈ actions2 do acc + @e /for(acc)
let amb =
 for acc ="", @e ∈ actions2 do
  acc
  + if length.@e > 1 then" /br >>>>" + print(grammar2, @e)else empty:seq.word
 /for(acc)
if length.amb > 0 then
"ambiguous actions:" + amb + " /br prec rules"
 + for acc ="", @e ∈ ruleprec do acc + "|" + @e /for(acc)
else""/if
+ print(grammar2, actions3)
+ generatereduce(grammarandact, alphabet, attributename)
+ '  /p function tokenlist:T seq.word"'
+ alphabet
+ '"'
+ " /p function startstate:T int"
+ toword.initialstateno
+ " /p function finalstate:T int"
+ toword.finalstateno
+ " /p noactions"
+ toword.length.actions
+ " /br nosymbols:"
+ toword.length.alphabet
+ " /br norules"
+ toword.length.grammarandact
+ " /br nostate"
+ toword.length.encoding:seq.encodingpair.state
+ if length.amb = 0 then
 let x =
  for table = sparseseq.0, @e ∈ actions3 do
   replaceS(table, findindex(lookahead.@e, alphabet) + length.alphabet * stateno.@e, [ codedaction.@e])
  /for(table)
 " /p function actiontable:T seq.int ["
 + for acc ="", @e ∈ x do acc + toword.@e + ","/for(acc >> 1)
 + "]"
else""/if
+ " /p follow"
+ print.follow.graminfo

function print(a:graph.word)seq.word
for acc ="nodes", node ∈ toseq.nodes.a do
 acc + " /br" + node + "followed by:" + toseq.successors(a, node)
/for(acc)

function dups(s:seq.action)seq.seq.action
if isempty.s then empty:seq.seq.action else dups(1, sort.s, 1, empty:seq.seq.action)

function dups(startofrun:int, s:seq.action, i:int, result:seq.seq.action)seq.seq.action
if i > length.s then result + subseq(s, startofrun, i)
else if s_startofrun = s_i then dups(startofrun, s, i + 1, result)
else dups(i, s, i + 1, result + subseq(s, startofrun, i - 1))

function closestate(graminfo:grammarinfo, stateno:int, result:seq.action, alphabet:set.word)seq.action
let m = encoding:seq.encodingpair.state
if stateno > length.m then result
else
 let state = data.m_stateno
 let reductions = finished.state
 let reduceActions =
  for acc = empty:seq.action, rule ∈ reductions do
   acc
   + for acc2 = empty:seq.action, lookahead ∈ toseq(successors(follow.graminfo, first.rule) ∩ alphabet)do acc2 + reduce(stateno, lookahead, ruleno(grammar.graminfo, rule))/for(acc2)
  /for(acc)
 let newresult =
  for acc = result + reduceActions, lookahead ∈ toseq.asset.shifts.state do
   let newstate = advance(grammar.graminfo, toset.state, lookahead)
   let newstateno = if isempty.newstate then 0 else valueofencoding.encode.state.newstate
   acc + shift(stateno, lookahead, newstateno)
  /for(acc)
 closestate(graminfo, stateno + 1, newresult, alphabet)

Function generatereduce(grammarandact:seq.seq.seq.word, alphabet:seq.word, attribute:seq.word)seq.word
" /br  /br Function action(ruleno:int, input:seq.token." + attribute
+ ", R:reduction."
+ attribute
+ ")"
+ attribute
+ for acc ="", i = 1, e ∈ grammarandact do next(acc + reduceline(e, i, length.grammarandact), i + 1)/for(acc)
+ " /p function rulelength:T seq.int ["
+ for acc ="", @e ∈ grammarandact do acc + toword(length.@e_1 - 1) + ","/for(acc >> 1)
+ "] /p function leftside:T seq.int ["
+ for acc ="", @e ∈ grammarandact do acc + toword.findindex(@e_1_1, alphabet) + ","/for(acc >> 1)
+ ']'

function reduceline(grammerandact:seq.seq.word, i:int, last:int)seq.word
let s = grammerandact
let prefix =
 if i = 1 then" /br if"
 else if i = last then" /br else assert"else" /br else if"
let part2 =
"ruleno = {" + s_1 + "}" + toword.i
 + if i = last then ' report"invalid rule number"+ toword.ruleno  /br ' else"then"
prefix + part2
+ for acc ="", w ∈ s_2 do
 acc + if w ∈ "let assert"then" /br" + w else [ w]
/for(acc)

Function gentau2 seq.word
{ used to generater tau parser for Pass1 of the tau compiler. }
lr1parser(taurules2, tauruleprec, taualphabet,"bindinfo")

function taualphabet seq.word".=():>]-for * comment, [_/if is I if # then else let assert report ∧ ∨ $wordlist while /for W do"

function tauruleprec seq.seq.word
{ list of rules and lookaheads. The position of the lookahead is noted. Rule reductions after are discard and rule the first 
 rule listed before the position is used to reduce. }
{ [""]}
["("
,"E NM"
, ' E comment E '
,"E E_E"
,"_"
,"E W.E"
,"E E * E"
,"E-E"
,"*"
,"E E-E"
,"-"
,"E E > E"
,"E E = E"
,"="
,">"
,"E E ∧ E"
,"∧"
,"E E ∨ E"
,"∨"
]
+ ["/for"
,"/if"
,"E if E then E else E"
,"E assert E report D E"
,"A W = E"
,"E let A E"
,"D E"
]

function taurules2 seq.seq.seq.word
[ [ ' G F # ', ' R_1 ']
, [ ' F W NM(FP)T E ', ' createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)']
, [ ' F W_(FP)T E ', ' createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)']
, [ ' F W-(FP)T E ', ' createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)']
, [ ' F W =(FP)T E ', ' createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)']
, [ ' F W >(FP)T E ', ' createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)']
, [ ' F W *(FP)T E ', ' createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)']
, [ ' F W ∧(FP)T E ', ' createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)']
, [ ' F W ∨(FP)T E ', ' createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)']
, [ ' F W NM T E '
, ' createfunc(R, common, place, tokentext.R_2, empty:seq.mytype, R_3, R_4)'
]
, [ ' F W NM is P '
, ' let tp = resolvetype(if isabstract.modname.common then tokentext.R_2 +".T"else tokentext.R_2, common, place)bindinfo 
(dict.R, empty:seq.symbol, [ tp]+ types.R_4, text.R_4)'
]
, [ ' FP P ', ' if mode.common ∉"symbol"then addparameters(R_1, common, place)else R_1 ']
, [ ' P T ', ' addpara(dict.R,":", R_1, place)']
, [ ' P P, T ', ' addpara(dict.R,":", R_3, place, R_1)']
, [ ' P W:T ', ' addpara(dict.R, tokentext.R_1, R_3, place)']
, [ ' P P, W:T ', ' addpara(dict.R, tokentext.R_3, R_5, place, R_1)']
, [ ' P comment W:T ', ' addpara(dict.R, tokentext.R_2, R_4, place)']
, [ ' P P, comment W:T ', ' addpara(dict.R, tokentext.R_4, R_6, place, R_1)']
, [ ' E NM '
, ' if mode.common ∈"body text"then let f = lookupbysig(dict.R, text.R_1, empty:seq.mytype, common, place)bindinfo(
 dict.R, [ f], [ resulttype.f],"")else R_1 '
]
, [ ' E NM(L)', ' unaryop(R, common, place, tokentext.R_1, R_3)']
, [ ' E(E)', ' R_2 ']
, [ ' E if E then E else E ', ' ifexp(R, R_2, R_4, R_6, common, place)']
, [ ' E if E then E else E /if ', ' ifexp(R, R_2, R_4, R_6, common, place)']
, [ ' E E_E ', ' opaction(R, common, place)']
, [ ' E-E ', ' unaryop(R, common, place, tokentext.R_1, R_2)']
, [ ' E W.E ', ' unaryop(R, common, place, tokentext.R_1, R_3)']
, [ ' E E * E ', ' opaction(R, common, place)']
, [ ' E E-E ', ' opaction(R, common, place)']
, [ ' E E = E ', ' opaction(R, common, place)']
, [ ' E E > E ', ' opaction(R, common, place)']
, [ ' E E ∧ E ', ' opaction(R, common, place)']
, [ ' E E ∨ E ', ' opaction(R, common, place)']
, [ ' L E ', ' R_1 ']
, [ ' L L, E ', ' bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3,"")']
, [ ' E [ L]'
, ' let types = types.R_2 assert for acc = true, @e = types do acc ∧ types_1 = @e /for(acc)report errormessage("types do not match 
 in build", common, place)bindinfo(dict.R, code.R_2 + Sequence(types_1, length.types), [ seqof.types_1],"")'
]
, [ ' A W = E '
, ' let name = tokentext.R_1 assert isempty.lookupbysig(dict.R, name)report errormessage("duplicate symbol:"+ name 
, common, place)let newdict = dict.R + Local(name_1,(types.R_3)_1, cardinality.dict.R)bindinfo(newdict, code.R 
_3 + Define(name_1, cardinality.dict.R), types.R_3, name)'
]
, [ ' E let A E '
, ' let letsym = if mode.common ∈"text"then [ symbol(internalmod,"let", typeint, first.types.R_3, first.types.R_3)
]else empty:seq.symbol bindinfo(dict.R_1, code.R_2 + code.R_3 + letsym, types.R_3,"")'
]
, [ ' E assert E report D E '
, ' assert(types.R_2)_1 = typeboolean report errormessage("condition in assert must be boolean in:", common, place)assert 
(types.R_4)_1 = seqof.typeword report errormessage("report in assert must be seq of word in:", common, place)let typ 
 =(types.R_5)_1 let assertsym = symbol(builtinmod.typ,"assert", seqof.typeword, typ)bindinfo(dict.R, [ Start.(
 types.R_5)_1]+ code.R_2 + Br2(1, 2)+ code.R_5 + Exit + code.R_4 + assertsym + Exit + if mode.common ∈"text"then symbol(
 internalmod,"report", typeint)else EndBlock, types.R_5,"")'
]
, [ ' E I ', ' bindlit.R ']
, [ ' E I.I '
, ' bindinfo(dict.R, [ Words(tokentext.R_1 +"."+ tokentext.R_3), symbol(moduleref."stdlib UTF8","makereal", seqof 
.typeword, typereal)], [ typereal],"")'
]
, [ ' T W ', ' R_1 ']
, [ ' T W.T '
, ' bindinfo(dict.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1 +"."+ tokentext.R_3)'
]
, [ ' E $wordlist '
, ' let s = tokentext.R_1 bindinfo(dict.R, [ Words.if mode.common ∈"text"then s else subseq(s, 2, length.s-1)], [ seqof 
.typeword],"")'
]
, [ ' E comment E '
, ' if mode.common ∈"text"then bindinfo(dict.R, [ Words.tokentext.R_1]+ code.R_2 + symbol(internalmod,"{", seqof.
 typeword, first.types.R_2, first.types.R_2), types.R_2,"")else R_2 '
]
, [ ' NM W ', ' R_1 ']
, [ ' NM W:T '
, ' bindinfo(dict.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1 + tokentext.R_3)'
]
, [ ' F1 W = E '
, ' let name = tokentext.R_1 assert isempty.lookupbysig(dict.R, name)report errormessage("duplicate symbol:"+ name 
, common, place)bindinfo(dict.R_1, code.R_3, types.R_3, name)'
]
, [ ' F1 F1, W = E '
, ' let name = tokentext.R_3 assert isempty.lookupbysig(dict.R, name)report errormessage("duplicate symbol:"+ name 
, common, place)bindinfo(dict.R, code.R_1 + code.R_5, types.R_1 + types.R_5, tokentext.R_1 + tokentext.R_3)'
]
, [ ' F2 F1, W-E '
, ' let name = tokentext.R_3 assert isempty.lookupbysig(dict.R, name)report errormessage("duplicate symbol:"+ name 
, common, place)forlocaldeclare(dict.R, code.R_1 + code.R_5, last.types.R_5, [ last(tokentext.R_3)], types.R_1 
, tokentext.R_1, common, place)'
]
, [ ' E for F2 do E /for(E)', ' forbody(dict.R_1, R_2, R_4, R_1, R_7, common, place)']
, [ ' E for F2 while E do E /for(E)', ' forbody(dict.R_1, R_2, R_6, R_4, R_9, common, place)']
, [ ' D E ', ' R_1 ']
]

Function gentaupretty seq.word
{ used to generater tau parser for Pass1 of the tau compiler. }
lr1parser(tauprettyrules, tauruleprec, taualphabet,"attribute2")

function tauprettyrules seq.seq.seq.word
{ after generator grammar change %%% to \ }
[ [ ' G F # ', ' R_1 ']
, [ ' F W NM(FP)T E '
, ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'
]
, [ ' F W_(FP)T E '
, ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'
]
, [ ' F W-(FP)T E '
, ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'
]
, [ ' F W =(FP)T E '
, ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'
]
, [ ' F W >(FP)T E '
, ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'
]
, [ ' F W *(FP)T E '
, ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'
]
, [ ' F W ∧(FP)T E '
, ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'
]
, [ ' F W ∨(FP)T E '
, ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'
]
, [ ' F W NM T E ', ' pretty.[ key.R_1, R_2, R_3, R_4]']
, [ ' F W NM is P ', ' pretty.[ key.R_1, R_2, R_3, list.R_4]']
, [ ' FP P ', ' list.R_1 ']
, [ ' P T ', ' R_1 ']
, [ ' P P, T ', ' R_1 + R_3 ']
, [ ' P W:T ', ' pretty.[ R_1, R_2, R_3]']
, [ ' P P, W:T ', ' R_1 + pretty.[ R_3, R_4, R_5]']
, [ ' P comment W:T ', ' pretty.[ R_1, R_2, R_3, R_4]']
, [ ' P P, comment W:T ', ' R_1 + pretty.[ R_3, R_4, R_5, R_6]']
, [ ' E NM ', ' R_1 ']
, [ ' E NM(L)'
, ' if length.R_3 = 1 ∧ length.text.R_1 = 1 then wrap(3, R_1,".", R_3)else pretty.[ R_1, R_2, list.R_3, R_4]'
]
, [ ' E(E)', ' R_2 ']
, [ ' E if E then E else E '
, ' let x1 ="%%%keyword if"+ removeclose.text.R_2 +"%%%keyword then"let x = attribute(x1 + removeclose.text.R_4)let 
 t = if width.R_2 + width.R_4 + width.R_6 < 30 then [ x, key.R_5, R_6]else if width.R_2 + width.R_4 < 30 then [ x, elseblock.R 
_6]else [ attribute(x1 + removeclose.text.block.R_4), elseblock.R_6]pretty(t + attribute."\ if")'
]
, [ ' E if E then E else E /if '
, ' let x1 ="%%%keyword if"+ removeclose.text.R_2 +"%%%keyword then"let x = attribute(x1 + removeclose.text.R_4)let 
 t = if width.R_2 + width.R_4 + width.R_6 < 30 then [ x, key.R_5, R_6]else if width.R_2 + width.R_4 < 30 then [ x, elseblock.R 
_6]else [ attribute(x1 + removeclose.text.block.R_4), elseblock.R_6]pretty(t + attribute."\ if")'
]
, [ ' E E_E ', ' wrap(1, R_1, text.R_2, R_3)']
, [ ' E-E ', ' unaryminus.R_2 ']
, [ ' E W.E ', ' wrap(3, R_1, text.R_2, R_3)']
, [ ' E E * E ', ' wrap(4, R_1, text.R_2, R_3)']
, [ ' E E-E ', ' wrap(5, R_1, text.R_2, R_3)']
, [ ' E E = E ', ' wrap(6, R_1, text.R_2, R_3)']
, [ ' E E > E ', ' wrap(7, R_1, text.R_2, R_3)']
, [ ' E E ∧ E ', ' wrap(8, R_1, text.R_2, R_3)']
, [ ' E E ∨ E ', ' wrap(9, R_1, text.R_2, R_3)']
, [ ' L E ', ' R_1 ']
, [ ' L L, E ', ' R_1 + R_3 ']
, [ ' E [ L]', ' pretty.[ R_1, list.R_2, R_3]']
, [ ' A W = E ', ' pretty.[ R_1, R_2, R_3]']
, [ ' E let A E '
, ' { checkpara(pretty.[ R_1, R_2], block("%%%br let assert", R_3))} attribute("%%%keyword let"+ subseq(text.R_2, 1 
, 2)+ protect(text.R_2 << 2, text.block("%%%br let assert", R_3)))'
]
, [ ' E assert E report D E '
, ' pretty.[ key.R_1, R_2, attribute("%%%keyword report"+ protect(text.R_4, text.block("%%%br let assert", R_5)))
]'
]
, [ ' E I ', ' R_1 ']
, [ ' E I.I ', ' pretty.[ R_1, R_2, R_3]']
, [ ' T W ', ' R_1 ']
, [ ' T W.T ', ' pretty.[ R_1, R_2, R_3]']
, [ ' E $wordlist '
, ' attribute2.[ prettyresult(0, length.text.R_1,"%%% { literal"+ escapeformat.text.R_1 +"%%% }")]'
]
, [ ' E comment E '
, ' let t ="%%% { comment {"+ escapeformat.text.R_1 << 1 >> 1 +"} %%% }"let t2 = if width.R_1 + width.R_2 > 30 ∧(text.R_2)_1 ≠"
 %%%br"_1 then t +"%%%br"else t pretty.[ attribute2.[ prettyresult(0, length.text.R_1, t2)], R_2]'
]
, [ ' NM W ', ' R_1 ']
, [ ' NM W:T ', ' pretty.[ R_1, R_2, R_3]']
, [ ' F1 W = E ', ' pretty.[ R_1, R_2, R_3]']
, [ ' F1 F1, W = E ', ' pretty.[ R_1, R_2, R_3, R_4, R_5]']
, [ ' F2 F1 ', ' R_1 ']
, [ ' E for F2 do E /for(E)'
, ' if width.R_2 + width.R_4 < 30 then pretty.[ key.R_1, list.R_2, attribute("%%%keyword do"+ removeclose.text.R_4 +"
 %%%keyword /for"), R_6, R_7, R_8]else pretty.[ key.R_1, list.R_2, attribute("%%%keyword do"+ removeclose.text.block 
.R_4 +"%%%br %%%keyword /for"), R_6, R_7, R_8]'
]
, [ ' E for F2 while(E)E /for(E)'
, ' pretty.[ key.R_1, list.R_2, attribute("%%%keyword while("+ text.R_5 +")"+ removeclose.text.R_7 +"%%%keyword /for 
"), R_9, R_10, R_11]'
]
, [ ' D E ',"R_1"]
]

Function test11 seq.word
extractgrammer.' function action(ruleno:int, dupinput:seq.word, place:int, R:reduction.bindinfo)bindinfo let common = common.
 dict.R if ruleno = { G F # } 1 then R_1 else if ruleno = { F W NM(FP)T E } 2 then createfunc(R, common, place, tokentext.R_2, types 
.R_4, R_6, R_7)else if ruleno = { F W_(FP)T E } 3 then createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)else 
 if ruleno = { F W-(FP)T E } 4 then createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)else if ruleno = { F W =(
 FP)T E } 5 then createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)else if ruleno = { F W >(FP)T E } 6 then createfunc 
(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)else if ruleno = { F W *(FP)T E } 7 then createfunc(R, common, place 
, tokentext.R_2, types.R_4, R_6, R_7)else if ruleno = { F W ∧(FP)T E } 8 then createfunc(R, common, place, tokentext.R_2 
, types.R_4, R_6, R_7)else if ruleno = { F W ∨(FP)T E } 9 then createfunc(R, common, place, tokentext.R_2, types.R_4, R_6 
, R_7)else if ruleno = { F W NM T E } 10 then createfunc(R, common, place, tokentext.R_2, empty:seq.mytype, R_3, R_4)else 
 if ruleno = { F W NM is P } 11 then let tp = resolvetype(if isabstract.modname.common then tokentext.R_2 +".T"else tokentext 
.R_2, common, place)bindinfo(dict.R, empty:seq.symbol, [ tp]+ types.R_4, text.R_4)else if ruleno = { FP P } 12 then if 
 mode.common ∉"symbol"then addparameters(R_1, common, place)else R_1 else if ruleno = { P T } 13 then addpara(dict.R,"
:", R_1, place)else if ruleno = { P P, T } 14 then addpara(dict.R,":", R_3, place, R_1)else if ruleno = { P W:T } 15 then addpara 
(dict.R, tokentext.R_1, R_3, place)else if ruleno = { P P, W:T } 16 then addpara(dict.R, tokentext.R_3, R_5, place, R_1 
)else if ruleno = { P comment W:T } 17 then addpara(dict.R, tokentext.R_2, R_4, place)else if ruleno = { P P, comment W:T } 18 
 then addpara(dict.R, tokentext.R_4, R_6, place, R_1)else if ruleno = { E NM } 19 then if mode.common ∈"body text"then let 
 f = lookupbysig(dict.R, text.R_1, empty:seq.mytype, common, place)bindinfo(dict.R, [ f], [ resulttype.f],"")else 
 R_1 else if ruleno = { E NM(L)} 20 then unaryop(R, common, place, tokentext.R_1, R_3)else if ruleno = { E(E)} 21 then R_2 else 
 if ruleno = { E if E then E else E } 22 then ifexp(R, R_2, R_4, R_6, common, place)else if ruleno = { E if E then E else E fi } 23 then 
 ifexp(R, R_2, R_4, R_6, common, place)else if ruleno = { E E_E } 24 then opaction(R, common, place)else if ruleno = { E-E } 25 
 then unaryop(R, common, place, tokentext.R_1, R_2)else if ruleno = { E W.E } 26 then unaryop(R, common, place, tokentext 
.R_1, R_3)else if ruleno = { E E * E } 27 then opaction(R, common, place)else if ruleno = { E E-E } 28 then opaction(R, common, 
 place)else if ruleno = { E E = E } 29 then opaction(R, common, place)else if ruleno = { E E > E } 30 then opaction(R, common, place 
)else if ruleno = { E E ∧ E } 31 then opaction(R, common, place)else if ruleno = { E E ∨ E } 32 then opaction(R, common, place)else 
 if ruleno = { L E } 33 then R_1 else if ruleno = { L L, E } 34 then bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3, 
"")else if ruleno = { E [ L]} 35 then let types = types.R_2 assert for acc = true, @e = types do acc ∧ types_1 = @e /for(acc)report 
 errormessage("types do not match in build", common, place)bindinfo(dict.R, code.R_2 + Sequence(types_1, length.types 
), [ seqof.types_1],"")else if ruleno = { A W = E } 36 then let name = tokentext.R_1 assert isempty.lookupbysig(dict.R, name 
)report errormessage("duplicate symbol:"+ name, common, place)let newdict = dict.R + Local(name_1,(types.R_3)_1 
, cardinality.dict.R)bindinfo(newdict, code.R_3 + Define(name_1, cardinality.dict.R), types.R_3, name)else if 
 ruleno = { E let A E } 37 then let letsym = if mode.common ∈"text"then [ symbol(internalmod,"let", typeint, first.types.
 R_3, first.types.R_3)]else empty:seq.symbol bindinfo(dict.R_1, code.R_2 + code.R_3 + letsym, types.R_3,"")else 
 if ruleno = { E assert E report D E } 38 then assert(types.R_2)_1 = typeboolean report errormessage("condition in assert 
 must be boolean in:", common, place)assert(types.R_4)_1 = seqof.typeword report errormessage("report in assert must 
 be seq of word in:", common, place)let typ =(types.R_5)_1 let assertsym = symbol(builtinmod.typ,"assert", seqof.typeword 
, typ)bindinfo(dict.R, [ Start.(types.R_5)_1]+ code.R_2 + Br2(1, 2)+ code.R_5 + Exit + code.R_4 + assertsym + Exit + if 
 mode.common ∈"text"then symbol(internalmod,"report", typeint)else EndBlock, types.R_5,"")else if ruleno = { E I } 
 39 then bindlit.R else if ruleno = { E I.I } 40 then bindinfo(dict.R, [ Words(tokentext.R_1 +"."+ tokentext.R_3), symbol 
(moduleref."stdlib UTF8","makereal", seqof.typeword, typereal)], [ typereal],"")else if ruleno = { T W } 41 then R_1 
 else if ruleno = { T W.T } 42 then bindinfo(dict.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1 +"."+ tokentext 
.R_3)else if ruleno = { E $wordlist } 43 then let s = tokentext.R_1 bindinfo(dict.R, [ Words.if mode.common ∈"text"then 
 s else subseq(s, 2, length.s-1)], [ seqof.typeword],"")else if ruleno = { E comment E } 44 then if mode.common ∈"text"then 
 bindinfo(dict.R, [ Words.tokentext.R_1]+ code.R_2 + symbol(internalmod,"{", seqof.typeword, first.types.R_2, 
 first.types.R_2), types.R_2,"")else R_2 else if ruleno = { NM W } 45 then R_1 else if ruleno = { NM W:T } 46 then bindinfo(dict 
.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1 + tokentext.R_3)else if ruleno = { F1 W = E } 47 then let name = tokentext 
.R_1 assert isempty.lookupbysig(dict.R, name)report errormessage("duplicate symbol:"+ name, common, place)bindinfo 
(dict.R_1, code.R_3, types.R_3, name)else if ruleno = { F1 F1, W = E } 48 then let name = tokentext.R_3 assert isempty.lookupbysig 
(dict.R, name)report errormessage("duplicate symbol:"+ name, common, place)bindinfo(dict.R, code.R_1 + code.R_
 5, types.R_1 + types.R_5, tokentext.R_1 + tokentext.R_3)else if ruleno = { F2 F1 } 49 then forlocaldeclare(R_1, common 
, place)else if ruleno = { E for F2 do E end(E)} 50 then forbody(dict.R_1, R_2, R_4, R_1, R_7, common, place)else if ruleno 
 = { E for F2 while E do E end(E)} 51 then forbody(dict.R_1, R_2, R_6, R_4, R_9, common, place)else assert ruleno = { D E } 52 report 
"invalid rule number"+ toword.ruleno R_1 '

Function extractgrammer(z:seq.word)seq.word
{ use to extract grammar and rules from action procedure generated by genLR1 }
extractgrammer(z, 1,"BEGIN", 1,"")

function extractgrammer(z:seq.word, i:int, state:seq.word, mark:int, result:seq.word)seq.word
if i > length.z then"[ '" + result + subseq(z, mark, i - 1) + "]]"
else if z_i ∈ "{ }"then
 if state = "BEGIN"then extractgrammer(z, i + 1,"INRULE", i + 1, result)
 else if state = "INRULE"then
  extractgrammer(z
  , i + 3
  ,"INACTION"
  , i + 3
  , result + "'" + subseq(z, mark, i - 1) + "', '"
  )
 else extractgrammer(z, i + 1, state, mark, result)
else if subseq(z, i, i + 4) ∈ ["else if ruleno = {","else assert ruleno = {"]then
 extractgrammer(z, i + 5,"INRULE", i + 5, result + subseq(z, mark, i - 1) + "'] /br, [")
else extractgrammer(z, i + 1, state, mark, result) 