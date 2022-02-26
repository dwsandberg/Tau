Module genLR1

use format

use pretty

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

function assignencoding(a:state)int nextencoding.a

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
print(grammar, c, 1, -1, 0, "")

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

/function print(a:seq.arc.word)seq.word for arc ∈ a, b="", , , b+tail.arc+head.arc

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

function reduce(stateno:int, lookahead:word, ruleno:int)action action(stateno, lookahead, -ruleno)

type ruleprec is lookahead:word, rules:seq.int

function print(grammar:seq.seq.word, p:ruleprec)seq.word
"lookahead:" + lookahead.p
+ for acc = "", @e ∈ rules.p do acc + grammar_@e + " /br |"/for(acc >> 2)

function =(a:ruleprec, b:ruleprec)boolean lookahead.a = lookahead.b

function print(a:seq.seq.word)seq.word
for acc = "", @e ∈ a do acc + @e + " /br"/for(acc >> 1)

function print(p:dottedrule)seq.word
subseq(rule.p, 1, place.p - 1) + singlequote + subseq(rule.p, place.p, length.rule.p)

function print(s:state)seq.word
for acc = " /br", dotrule ∈ toseq.toset.s do acc + print.dotrule + " /br |"/for(acc >> 2)

Function initialstate(grammar:seq.seq.word)set.dottedrule close2(grammar, asset.[dottedrule(2, "G F #")])

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
 acc + if place.p = length.rule.p + 1 then[rule.p]else empty:seq.seq.word
/for(acc)

function shifts(s:state)seq.word
toseq.asset.for acc = empty:seq.word, p ∈ toseq.toset.s do
 acc
 + if place.p = length.rule.p + 1 then empty:seq.word else[(rule.p)_(place.p)]
/for(acc)

function resolveamb(ruleprec:seq.seq.word, grammar:seq.seq.word, dup:seq.action)seq.action
if length.dup = 1 then dup
else if length.dup ≥ 2 ∧ codedaction.dup_1 < 0 ∧ codedaction.dup_2 < 0 then
 {contains reduce reduce conflict}
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
  , if between(reducepos1, 1, reducepos2)then[dup_1] + dup << 2 else dup << 1
  )
else if length.dup = 2 ∧ codedaction.dup_1 < 0 ∧ codedaction.dup_2 > 0 then
 let rule1 = grammar_(-codedaction.dup_1)
 let shiftpos = 
  for r = 0, i = 1, p ∈ ruleprec
  while r = 0
  do next(if length.p = 1 ∧ p_1 = lookahead.dup_2 then i else 0, i + 1)
  /for(r)
 let reducepos = 
  for r = 0, i = 1, p ∈ ruleprec while r = 0 do next(if length.p > 1 ∧ p = rule1 then i else 0, i + 1)/for(r)
 if between(reducepos, 1, shiftpos)then{choose reduce}[dup_1]
 else if between(shiftpos, 1, reducepos)then{choose shift}[dup_2]else dup
else dup

function printRulePrecedence(ruleprec:seq.seq.word) seq.word
 for acc = "{RulePrecedence", @e ∈ ruleprec do acc + "|" + @e /for(acc+"|}")

Function lr1parser(grammarandact:seq.seq.seq.word
, ruleprec:seq.seq.word
, terminals:seq.word
, attributename:seq.word
, codeonly:boolean
, parameterized:boolean
)seq.word
let grammar2 = for acc = empty:seq.seq.word, @e ∈ grammarandact do acc + first.@e /for(acc)
let nontermials = for acc = empty:set.word, rule ∈ grammar2 do acc + first.rule /for(acc)
assert isempty(asset.terminals ∩ nontermials)report"terminals and nontermials sets must be distinct"
let alphabet = terminals + toseq.nontermials
let initialstateno = valueofencoding.encode.state.initialstate.grammar2
let symbolsused = for acc = empty:set.word, rule ∈ grammar2 do acc ∪ asset.rule /for(acc)
let missingsymbols = symbolsused \ asset.alphabet
assert isempty(symbolsused \ asset.alphabet)
report"Symbols not included in alphabet" + toseq(symbolsused \ asset.alphabet)
assert isempty(asset.alphabet \ symbolsused)
report"Symbols in alphabet but not used" + toseq(asset.alphabet \ symbolsused)
let k = 
 for problems = "", item ∈ ruleprec do
  problems
  + if length.item = 1 ∧ item_1 ∉ alphabet then"lookahead" + item + "is not in alphabet"
  else if length.item > 1 ∧ item ∉ grammar2 then"rule is not in grammar:" + item else""
 /for(problems)
assert isempty.k report"ruleprec problem" + k
let graminfo = grammarinfo(grammar2, follow.grammar2, ruleprec)
let actions = closestate(graminfo, 1, empty:seq.action, asset.terminals)
{assert false report print(grammar2, actions)}
let dups = dups.actions
let actions2 = 
 for acc = empty:seq.seq.action, @e ∈ dups.actions do acc + resolveamb(ruleprec, grammar2, @e)/for(acc)
let actions3 = for acc = empty:seq.action, @e ∈ actions2 do acc + @e /for(acc)
let amb = 
 for acc = "", @e ∈ actions2 do
  acc
  + if length.@e > 1 then" /br >>>>" + print(grammar2, @e)else empty:seq.word
 /for(acc)
let finalstatebody = 
 for txt = "", a ∈ actions3 do
  if lookahead.a = first."#" ∧ codedaction.a > 0 then txt + toword.codedaction.a else txt
  /for(txt)
 let para=if parameterized then ":T" else ""
  let result = 
 [generatereduce(grammarandact, alphabet, attributename,ruleprec)
 , "function rulelength"+para+" seq.int"
 + for acc = "[", @e ∈ grammarandact do acc + toword(length.@e_1 - 1) + ", "/for(acc >> 1 + "]")
 , "function leftside"+para+" seq.int"
 + for acc = "[", @e ∈ grammarandact do acc + toword.findindex(@e_1_1, alphabet) + ", "/for(acc >> 1 + "]")
 , "function tokenlist" + para +  "seq.word"  + dq.alphabet 
 , "function startstate"+para+" int" + toword.initialstateno
 , "function finalstate"+para+" int" + finalstatebody
 , "function actiontable"+para+" seq.int"
 + if length.amb = 0 then
  let x = 
   for table = sparseseq.0, @e ∈ actions3 do
    replaceS(table, findindex(lookahead.@e, alphabet) + length.alphabet * stateno.@e, [codedaction.@e])
   /for(table)
  for acc = "[", @e ∈ x do acc + toword.@e + ", "/for(acc >> 1 + "]")
 else"{action table omitted}[0]"
 ]
let header = 
 " /p noactions" + toword.length.actions + "nosymbols:" + toword.length.alphabet
 + "norules:"
 + toword.length.grammarandact
 + "nostate:"
 + toword.length.encoding:seq.encodingpair.state
 + " /p"
 + printRulePrecedence.ruleprec
 + if length.amb > 0 then "ambiguous actions:" + amb else""/if
 + if codeonly then "" else print(grammar2, actions3) 
for txt = header, p ∈ result do
 txt + " /p" + if codeonly then pretty.towords.textformat.p else p
/for(if codeonly then txt else txt + " /p follow" + print.follow.graminfo   /if)

function print(a:graph.word)seq.word
for acc = "nodes", node ∈ toseq.nodes.a do
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
 
Function generatereduce(grammarandact:seq.seq.seq.word, alphabet:seq.word, attributename:seq.word, ruleprec:seq.seq.word)seq.word
"Function action(ruleno:int, input:seq.token." + attributename + ", R:reduction."
+ attributename
+ ")"
+ attributename
+ "{Alphabet"
+ alphabet
+ "}"
+ if isempty.ruleprec then""else printRulePrecedence.ruleprec /if
+ for acc = "", i = 1, e ∈ grammarandact do 
 let reduceline = 
  " /br else if ruleno={" + e_1 + "}" + toword.i + "then"
+ for acc2 = "", w ∈ e_2 do
 acc2 + if w ∈ "let assert"then" /br" + w else[w]
 /for(acc2)
next(acc + reduceline, i + 1)
/for(
acc << 2 + " else{ruleno}assert false report"
+dq."invalid rule number"+"+toword.ruleno  R_1 ")
 
 Function LR1gen (location:seq.word,codeonly:boolean,parameterized:boolean) seq.word
{Assumption:Word ruleno is not used in any action.First use of ruleprec in comment that defines the precedence}
for rules = empty:seq.seq.seq.word
, terminals = ""
, attribute = first."ATTR"
, ruleprec = empty:seq.seq.word
, p ∈ breakparagraph.getfile:UTF8(location + ".ls")
do
 if subseq(p, 1, 2) ∈ ["Function action", "function action"]then
     let x = findindex("Alphabet"_1,p)
       let newterminals= subseq(p,x+1,x+findindex("}"_1,p << x)-1) 
     let a = findindex("RulePrecedence"_1,p)
      let c=break(subseq(p,a,a+findindex("}"_1,p << a)),"|",false) << 1
     let newruleprec =      c >> 1
  next(for acc = empty:seq.seq.seq.word, b ∈ break(p, "ruleno", false)do
      if subseq(b,1,2)="={" then
       let k= findindex(first."}",b)
        acc+[subseq( b,3,k-1) , subseq(b,k+3 ,length.b-2)]
      else acc
  /for(acc)
  , newterminals
  , p_(findindex(first.")", p) + 1)
  , newruleprec
  )
    else next(rules,terminals,attribute,ruleprec)
/for(let nonTerminals = for acc = empty:set.word, r ∈ rules do acc + first.first.r /for(acc)
let terminals2 = 
 for acc = "", t ∈ terminals do if t ∈ nonTerminals then acc else acc + t /for(acc)
   lr1parser(rules,ruleprec,terminals2,"attribute",codeonly,parameterized)  )

use textio

Function gentau seq.word
{used to generater tau parser for Pass1 of the tau compiler. }
lr1parser(taurules2, tauruleprec, taualphabet, "bindinfo", false,true)

function taualphabet seq.word".=():>]-for * comment, [_/if is I if # then else let assert report ∧ ∨ $wordlist while /for W do"

function tauruleprec seq.seq.word
{list of rules and lookaheads. The position of the lookahead is noted. Rule reductions after position are discarded and 
rule the first rule listed before the position is used to reduce. }
["("
, "E NM"
, "E comment E"
, "E E_E"
, "_"
, "E W.E"
, "E E * E"
, "E-E"
, "*"
, "E E-E"
, "-"
, "E E > E"
, "E E=E"
, "="
, ">"
, "E E ∧ E"
, "∧"
, "E E ∨ E"
, "∨"
, "/for"
, "/if"
, "E if E then E else E"
, "E assert E report D E"
, "A W=E"
, "E let A E"
, "D E"
]

function taurules2 seq.seq.seq.word
[["G F #", "R_1"]
, ["F W NM(FP)T E", "createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)"]
, ["F W_(FP)T E", "createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)"]
, ["F W-(FP)T E", "createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)"]
, ["F W=(FP)T E", "createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)"]
, ["F W >(FP)T E", "createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)"]
, ["F W *(FP)T E", "createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)"]
, ["F W ∧(FP)T E", "createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)"]
, ["F W ∨(FP)T E", "createfunc(R, common, place, tokentext.R_2, types.R_4, R_6, R_7)"]
, ["F W NM T E"
, "createfunc(R, common, place, tokentext.R_2, empty:seq.mytype, R_3, R_4)"
]
, ["F W NM is P"
, ' let tp=resolvetype(if isabstract.modname.common then tokentext.R_2+".T"else tokentext.R_2, common, place)bindinfo 
(dict.R, empty:seq.symbol, [tp]+types.R_4, text.R_4)'
]
, ["FP P", ' if mode.common ∉"symbol"then addparameters(R_1, common, place)else R_1 ']
, ["P T", ' addpara(dict.R, ":", R_1, place)']
, ["P P, T", ' addpara(dict.R, ":", R_3, place, R_1)']
, ["P W:T", "addpara(dict.R, tokentext.R_1, R_3, place)"]
, ["P P, W:T", "addpara(dict.R, tokentext.R_3, R_5, place, R_1)"]
, ["P comment W:T", "addpara(dict.R, tokentext.R_2, R_4, place)"]
, ["P P, comment W:T", "addpara(dict.R, tokentext.R_4, R_6, place, R_1)"]
, ["E NM"
, ' if mode.common ∈"body text"then let f=lookupbysig(dict.R, text.R_1, empty:seq.mytype, common, place)bindinfo(
dict.R, [f], [resulttype.f], "")else R_1 '
]
, ["E NM(L)", "unaryop(R, common, place, tokentext.R_1, R_3)"]
, ["E(E)", "R_2"]
, ["E if E then E else E", "ifexp(R, R_2, R_4, R_6, common, place)"]
, ["E if E then E else E /if", "ifexp(R, R_2, R_4, R_6, common, place)"]
, ["E E_E", "opaction(R, common, place)"]
, ["E-E", "unaryop(R, common, place, tokentext.R_1, R_2)"]
, ["E W.E", "unaryop(R, common, place, tokentext.R_1, R_3)"]
, ["E E * E", "opaction(R, common, place)"]
, ["E E-E", "opaction(R, common, place)"]
, ["E E=E", "opaction(R, common, place)"]
, ["E E > E", "opaction(R, common, place)"]
, ["E E ∧ E", "opaction(R, common, place)"]
, ["E E ∨ E", "opaction(R, common, place)"]
, ["L E", "R_1"]
, ["L L, E", ' bindinfo(dict.R, code.R_1+code.R_3, types.R_1+types.R_3, "")']
, ["E[L]"
, ' let types=types.R_2 assert for acc=true, @e ∈ types do acc ∧ types_1=@e /for(acc)report errormessage("types do not match 
in build", common, place)bindinfo(dict.R, code.R_2+Sequence(types_1, length.types), [seqof.types_1], "")'
]
, ["A W=E"
, ' let name=tokentext.R_1 assert isempty.lookupbysig(dict.R, name)report errormessage("duplicate symbol:"+name 
, common, place)let newdict=dict.R+Local(name_1, (types.R_3)_1, cardinality.dict.R)bindinfo(newdict, code.R 
_3+Define(name_1, cardinality.dict.R), types.R_3, name)'
]
, ["E let A E"
, ' let letsym=if mode.common ∈"text"then[symbol(internalmod, "let", typeint, first.types.R_3, first.types.R_3)
]else empty:seq.symbol bindinfo(dict.R_1, code.R_2+code.R_3+letsym, types.R_3, "")'
]
, ["E assert E report D E"
, ' assert(types.R_2)_1=typeboolean report errormessage("condition in assert must be boolean in:", common, place)assert 
(types.R_4)_1=seqof.typeword report errormessage("report in assert must be seq of word in:", common, place)let typ 
=(types.R_5)_1 let assertsym=symbol(builtinmod.typ, "assert", seqof.typeword, typ)bindinfo(dict.R, [Start.(
types.R_5)_1]+code.R_2+Br2(1, 2)+code.R_5+Exit+code.R_4+assertsym+Exit+if mode.common ∈"text"then symbol(
internalmod, "report", typeint)else EndBlock, types.R_5, "")'
]
, ["E I", "bindlit.R"]
, ["E I.I"
, ' bindinfo(dict.R, [Words(tokentext.R_1+"."+tokentext.R_3), makerealSymbol], [typereal], "")'
]
, ["T W", "R_1"]
, ["T W.T"
, ' bindinfo(dict.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1+"."+tokentext.R_3)'
]
, ["E $wordlist"
, ' let s=tokentext.R_1 bindinfo(dict.R, [Words.if mode.common ∈"text"then s else subseq(s, 2, length.s-1)], [seqof 
.typeword], "")'
]
, ["E comment E"
, ' if mode.common ∈"text"then bindinfo(dict.R, [Words.tokentext.R_1]+code.R_2+symbol(internalmod, "{", seqof.
typeword, first.types.R_2, first.types.R_2), types.R_2, "")else R_2 '
]
, ["NM W", "R_1"]
, ["NM W:T"
, "bindinfo(dict.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1+tokentext.R_3)"
]
, ["F1 W=E"
, ' let name=tokentext.R_1 assert isempty.lookupbysig(dict.R, name)report errormessage("duplicate symbol:"+name 
, common, place)bindinfo(dict.R_1, code.R_3, types.R_3, name)'
]
, ["F1 F1, W=E"
, ' let name=tokentext.R_3 assert isempty.lookupbysig(dict.R, name)report errormessage("duplicate symbol:"+name 
, common, place)bindinfo(dict.R, code.R_1+code.R_5, types.R_1+types.R_5, tokentext.R_1+tokentext.R_3)'
]
, ["F2 F1, W-E"
, ' let name=tokentext.R_3 assert isempty.lookupbysig(dict.R, name)report errormessage("duplicate symbol:"+name 
, common, place)forlocaldeclare(dict.R, code.R_1+code.R_5, last.types.R_5, [last(tokentext.R_3)], types.R_1 
, tokentext.R_1, common, place)'
]
, ["E for F2 do E /for(E)", "forbody(dict.R_1, R_2, R_4, R_1, R_7, common, place)"]
, ["E for F2 while E do E /for(E)", "forbody(dict.R_1, R_2, R_6, R_4, R_9, common, place)"]
, ["D E", "R_1"]
]

Function gentaupretty seq.word
{used to generater tau parser for Pass1 of the tau compiler. }
lr1parser(tauprettyrules, tauruleprec, taualphabet, "attribute2", true,true)

function tauprettyrules seq.seq.seq.word
{after generator grammar change %%% to \}
[["G F #", "R_1"]
, ["F W NM(FP)T E", "prettyfunc.R"]
, ["F W_(FP)T E", "prettyfunc.R"]
, ["F W-(FP)T E", "prettyfunc.R"]
, ["F W=(FP)T E", "prettyfunc.R"]
, ["F W >(FP)T E", "prettyfunc.R"]
, ["F W *(FP)T E", "prettyfunc.R"]
, ["F W ∧(FP)T E", "prettyfunc.R"]
, ["F W ∨(FP)T E", "prettyfunc.R"]
, ["F W NM T E"
, ' if width.R_4 > maxwidth then pretty.[attribute."%%%keyword", R_1, R_2, R_3, attribute."%%%br", R_4]else pretty.
[attribute."%%%keyword", R_1, R_2, R_3, R_4]'
]
, ["F W NM is P", ' pretty.[attribute."%%%keyword", R_1, R_2, R_3, list.R_4]']
, ["FP P", "list.R_1"]
, ["P T", "R_1"]
, ["P P, T", "R_1+R_3"]
, ["P W:T", "pretty.[R_1, R_2, R_3]"]
, ["P P, W:T", "R_1+pretty.[R_3, R_4, R_5]"]
, ["P comment W:T", "pretty.[R_1, R_2, R_3, R_4]"]
, ["P P, comment W:T", "R_1+pretty.[R_3, R_4, R_5, R_6]"]
, ["E NM", "R_1"]
, ["E NM(L)"
, ' if length.R_3=1 ∧ length.text.R_1=1 then wrap(3, R_1, ".", R_3)else pretty.[R_1, attribute."(", list.R_3, attribute 
.")"]'
]
, ["E(E)", "R_2"]
, ["E if E then E else E", "ifthenelse.R"]
, ["E if E then E else E /if", "ifthenelse.R"]
, ["E E_E", "wrap(1, R_1, text.R_2, R_3)"]
, ["E-E", "unaryminus.R_2"]
, ["E W.E", "wrap(3, R_1, text.R_2, R_3)"]
, ["E E * E", "wrap(4, R_1, text.R_2, R_3)"]
, ["E E-E", "wrap(5, R_1, text.R_2, R_3)"]
, ["E E=E", "wrap(6, R_1, text.R_2, R_3)"]
, ["E E > E", "wrap(7, R_1, text.R_2, R_3)"]
, ["E E ∧ E", "wrap(8, R_1, text.R_2, R_3)"]
, ["E E ∨ E", "wrap(9, R_1, text.R_2, R_3)"]
, ["L E", "R_1"]
, ["L L, E", "R_1+R_3"]
, ["E[L]", "pretty.[R_1, list.R_2, R_3]"]
, ["A W=E", "pretty.[R_1, if width.R_3 > maxwidth then block.R_3 else R_3]"]
, ["E let A E"
, ' attribute2.[prettyresult(0, 10000, "%%%keyword let"+first.text.R_2+[space, "="_1, space]+protect(text.R_2 
<< 1, text.R_3))]'
]
, ["E assert E report D E"
, ' attribute2.[prettyresult(0, 10000, "%%%keyword assert"+text.R_2+if width.R_2+width.R_4 > maxwidth then"%%%br 
"else""/if+"%%%keyword report"+protect(text.R_4, text.R_5))]'
]
, ["E I", "R_1"]
, ["E I.I", "pretty.[R_1, R_2, R_3]"]
, ["T W", "R_1"]
, ["T W.T", "pretty.[R_1, R_2, R_3]"]
, ["E $wordlist", ' attribute("%%%< literal"+escapeformat.text.R_1+"%%%>")']
, ["E comment E"
, ' precAttribute(prec.(toseq.R_2)_1, "%%%< comment"+escapeformat.text.R_1+"%%%>"+if width.R_1+width.R_2 > maxwidth 
then"%%%br"+text.R_2 else text.R_2)'
]
, ["NM W", "R_1"]
, ["NM W:T", "pretty.[R_1, R_2, R_3]"]
, ["F1 W=E", ' pretty.[R_1, attribute.[space, "="_1, space], R_3]']
, ["F1 F1, W=E", ' R_1+pretty.[R_3, attribute.[space, "="_1, space], R_5]']
, ["F2 F1, W-E", ' R_1+pretty.[R_3, attribute."∈", R_5]']
, ["E for F2 do E /for(E)"
, ' if width.R_2+width.R_4 < maxwidth then pretty.[attribute."%%%keyword for", list.R_2, attribute("%%%keyword do 
"+removeclose.text.R_4+"%%%keyword /for"), R_6, R_7, R_8]else pretty.[attribute."%%%keyword for", list.R_2, attribute 
("%%%keyword do"+removeclose.text.block.R_4+"%%%br %%%keyword /for"), R_6, R_7, R_8]'
]
, ["E for F2 while E do E /for(E)"
, ' if width.R_2+width.R_4+width.R_6 < maxwidth then pretty.[attribute."%%%keyword for", list.R_2, attribute("%%%keyword 
while"+text.R_4+"%%%keyword do"+removeclose.text.R_6+"%%%keyword /for"), R_8, R_9, R_10]else pretty.[attribute 
."%%%keyword for", list.R_2, attribute("%%%br %%%keyword while"+text.R_4+"%%%br %%%keyword do"+removeclose.text 
.R_6+"%%%br %%%keyword /for"), R_8, R_9, R_10]'
]
, ["D E", "R_1"]
]

 /<  command LR1gen LR1 />  A parser generator for a subset of LR1 grammars. 

 /<  option * -args  />  path to location of the code file from which the grammar will be extracted

 /<  option f -c  />  Only produces the generated code

 /<  option f -p />  adds :T to function name  to allowing them to be put into a parameterized module

To get started building a new parser the following function will work to produce tables for a new parser

type ATTR is val:int

type stkele is stateno:int, attribute:ATTR

type reduction is toseq:seq.stkele

function forward(stk:ATTR, token:ATTR)ATTR token

Function _(r:reduction, n:int)ATTR attribute.(toseq.r)_n

use stack.stkele

use seq.stkele

Function sampleparse(input:seq.word)int
for lrpart = push(empty:stack.stkele, stkele(startstate, ATTR.0))
, idx = 1
, this ∈ input + "#"
while stateno.top.lrpart ≠ finalstate
do{lexical analysis is down here}
  {Assume the input is only integers}
let tokenno = 
 if findindex(this, tokenlist) > length.tokenlist then findindex("I"_1, tokenlist)
 else findindex("#"_1, tokenlist)
let attribute = ATTR.if this ∈ {end marked}"#"then 0 else toint.this
 next(step(lrpart, input, attribute , tokenno, idx), idx + 1)
/for(val.attribute.undertop(lrpart, 1))

function step(stk:stack.stkele, input:seq.word, attrib:ATTR, tokenno:int, place:int)stack.stkele
let stateno = stateno.top.stk
let actioncode = actiontable_(tokenno + length.tokenlist * stateno)
assert place ∈ [1, 2, 3, 4]report"here" + toword.place + input
if actioncode > 0 then
 if stateno = finalstate then stk
 else push(stk, stkele(actioncode, forward(attribute.top.stk, attrib)))
else
 assert actioncode < 0 report"ERROR"
   let ruleno = -actioncode
 let rulelen = rulelength_ruleno
 let newstk = pop(stk, rulelen)
 let newstateno = actiontable_(leftside_ruleno + length.tokenlist * stateno.top.newstk)
  let newstkele = stkele(newstateno, action(ruleno, input, place, reduction.top(stk, rulelen)))
 step(push(newstk, newstkele), input, attrib, tokenno, place) 

-----

This part is generated with LR1 command (with the exception of the action header.)

Function action(ruleno:int, input:seq.word , place:int, R:reduction)ATTR
{Alphabet I # F G}
if ruleno = {G F #}1 then R_1
else if ruleno = {F F I}2 then
 {The left side of the grammar is F and the right side is F I}ATTR(val.R_1 + val.R_2)
else if ruleno = {F I}3 then R_1
else
 {ruleno}
 assert false report"invalid rule number" + toword.ruleno
 R_1

function rulelength seq.int[2, 2, 1]

function leftside seq.int[4, 3, 3]

function tokenlist seq.word"I # F G"

function startstate int 1

function finalstate int 4

function actiontable seq.int[0, 0, 0, 0, 3, 0, 2, 0, 5, 4, 0, 0, -3, -3, 0, 0, 0, 0, 0, 0, -2, -2]

 ----