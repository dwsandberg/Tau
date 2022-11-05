Module genLR1

use otherseq.action

use seq.seq.action

use otherseq.action2

use set.dottedrule

use file

use seq.file

use sparseseq.int

use pretty

use standard

use encoding.state

use seq.state

use taulextable

use textio

use seq.arc.word

use graph.word

use otherseq.word

use otherseq.seq.word

use seq.seq.seq.word

use set.word

type state is toset:set.dottedrule

type dottedrule is place:int, rule:seq.word

type action is stateno:int, lookahead:word, codedaction:int

type grammarinfo is grammar:seq.seq.word, follow:graph.word

function =(a:state, b:state) boolean toset.a = toset.b

function =(a:dottedrule, b:dottedrule) boolean
rule.a = rule.b ∧ place.a = place.b

function >1(a:dottedrule, b:dottedrule) ordering
rule.a >1 rule.b ∧ place.a >1 place.b

function hash(p:dottedrule) int hash.rule.p + place.p

function =(a:action, b:action) boolean
lookahead.a = lookahead.b ∧ stateno.a = stateno.b

function >1(a:action, b:action) ordering
lookahead.a >1 lookahead.b ∧ stateno.a >1 stateno.b

type action2 is toaction:action

function >1(a1:action2, b1:action2) ordering
let a = toaction.a1
let b = toaction.b1
stateno.a >1 stateno.b ∧ codedaction.a >1 codedaction.b ∧ lookahead.a >1 lookahead.b

function recovery(alphabet:seq.word, grammar:seq.seq.word) seq.word
{let nonTerminals = for acc = empty:set.word, r ∈ grammar do acc+first.r /for (acc) let
 x = alphasort.grammar for acc ="", last = first.x, r /in x << 1+" B B" do if first.r /ne first.last
 then next (acc+" /br"+last, r) else if length.r < length.last /or last_2 /in" $wordlist" then
 next (acc, r) else next (acc, last) /for (" /br PASS1"+acc)+%n.alphasort.grammar}
for txt = "", s ∈ encodingdata:state do
 for acc = "", hasreduce = 0, p ∈ toseq.toset.s
 while hasreduce = 0
 do
  if place.p = length.rule.p + 1 then
   next(acc, findindex(grammar, rule.p))
  else if place.p = 2 ∨ (rule.p)_1 = (rule.p)_2 ∧ place.p = 3 then
   next(acc, hasreduce)
  else
   next(acc + (rule.p)_(place.p), hasreduce)
 /for (
  let tmp = 
   if hasreduce > 0 ∨ isempty.acc then
    "}-$(hasreduce)"
   else
    [first.acc] + "}" + %.findindex(alphabet, first.acc)
  let stateno = valueofencoding.encode.s
  txt + ", {$(stateno) $(tmp)"
 )
/for ("[$(txt << 1)]")

function print(grammar:seq.seq.word, actions:seq.action) seq.word
let d = sort.for b = empty:seq.action2, a ∈ actions do b + action2.a /for (b)
let c = for b = empty:seq.action, a ∈ d do b + toaction.a /for (b)
for result = "", laststate = 1, lastaction = -1, this ∈ c do
 let p1 = 
  if laststate ≠ stateno.this then
   if laststate > 0 then print.decode.to:encoding.state(laststate) else "" /if
   + "/br state:"
   + toword.stateno.this
  else
   ""
 let p2 = 
  if lastaction ≠ codedaction.this then
   if codedaction.this < 0 then
    "reduce $(grammar_(-codedaction.this)) ;"
   else
    "shift" + toword.codedaction.this
  else
   ""
 next(result + p1 + p2 + lookahead.this, stateno.this, codedaction.this)
/for (result)

function hash(s:state) int hash.(toseq.toset.s)_1

function follow(grammar:seq.seq.word) graph.word
let allarcs = 
 for acc = empty:seq.arc.word, rule ∈ grammar do
  acc
  + for arcs = empty:seq.arc.word, i = 1, e ∈ rule do
   next(if i > 2 then arcs + arc(rule_(i - 1), rule_i) else arcs, i + 1)
  /for (arcs)
 /for (acc)
follow(newgraph.allarcs, grammar)

function follow(g:graph.word, grammar:seq.seq.word) graph.word
let g2 = 
 for newgraph = g, rule ∈ grammar do
  let a = 
   for acc = empty:seq.arc.word, succ ∈ toseq.successors(g, rule_1) do
    acc + arc(last.rule, succ)
   /for (acc)
  newgraph
  + for acc = a, pred ∈ toseq.predecessors(g, rule_1) do
   acc + arc(pred, rule_2)
  /for (acc)
 /for (newgraph)
if g = g2 then g else follow(g2, grammar)

function ruleno(grammar:seq.seq.word, rule:seq.word) int
let ruleno = if rule = "" then 0 else findindex(grammar, rule)
assert ruleno ≤ length.grammar report "rule not found $(rule)"
ruleno

function shift(stateno:int, lookahead:word, newstateno:int) action
action(stateno, lookahead, newstateno)

function reduce(stateno:int, lookahead:word, ruleno:int) action
action(stateno, lookahead,-ruleno)

function print(p:dottedrule) seq.word
subseq(rule.p, 1, place.p - 1) + "'" + subseq(rule.p, place.p, length.rule.p)

function print(s:state) seq.word
for acc = "/br", dotrule ∈ toseq.toset.s do
 acc + print.dotrule + "/br |"
/for (acc >> 2)

function initialstate(grammar:seq.seq.word) set.dottedrule
close2(grammar, asset.[dottedrule(2, "G F #")])

function close2(g:seq.seq.word, s:set.dottedrule) set.dottedrule
let newset = for acc = s, dotrule ∈ toseq.s do acc ∪ close(g, dotrule) /for (acc)
if s = newset then s else close2(g, newset)

function close(grammar:seq.seq.word, p:dottedrule) set.dottedrule
if place.p > length.rule.p then
 empty:set.dottedrule
else
 asset.for acc = empty:seq.dottedrule, rule ∈ grammar do
  if rule_1 = (rule.p)_(place.p) then acc + dottedrule(2, rule) else acc
 /for (acc)

function advance(g:seq.seq.word, state:set.dottedrule, next:word) set.dottedrule
close2(g
 , asset.for acc = empty:seq.dottedrule, p ∈ toseq.state do
  if place.p ≤ length.rule.p ∧ (rule.p)_(place.p) = next then
   acc + dottedrule(place.p + 1, rule.p)
  else
   acc
 /for (acc))

function finished(s:state) seq.seq.word
for acc = empty:seq.seq.word, p ∈ toseq.toset.s do
 acc + if place.p = length.rule.p + 1 then [rule.p] else empty:seq.seq.word
/for (acc)

function shifts(s:state) seq.word
toseq.asset.for acc = empty:seq.word, p ∈ toseq.toset.s do
 acc + if place.p = length.rule.p + 1 then empty:seq.word else [(rule.p)_(place.p)]
/for (acc)

function resolveamb(ruleprec:seq.seq.word, grammar:seq.seq.word, dup:seq.action) seq.action
if length.dup = 1 then
 dup
else if length.dup ≥ 2 ∧ codedaction.dup_1 < 0 ∧ codedaction.dup_2 < 0 then
 {contains reduce reduce conflict}
 let rule1 = grammar_(-codedaction.dup_1)
 let rule2 = grammar_(-codedaction.dup_2)
 let reducepos1 = 
  for r = 0, i = 1, p ∈ ruleprec
  while r = 0
  do
   next(if length.p > 1 ∧ p = rule1 then i else 0, i + 1)
  /for (r)
 let reducepos2 = 
  for r = 0, i = 1, p ∈ ruleprec
  while r = 0
  do
   next(if length.p > 1 ∧ p = rule2 then i else 0, i + 1)
  /for (r)
 if reducepos1 = 0 ∧ reducepos2 = 0 then
  dup
 else
  resolveamb(ruleprec
   , grammar
   , if between(reducepos1, 1, reducepos2) then [dup_1] + dup << 2 else dup << 1)
else if length.dup = 2 ∧ codedaction.dup_1 < 0 ∧ codedaction.dup_2 > 0 then
 let rule1 = grammar_(-codedaction.dup_1)
 let shiftpos = 
  for r = 0, i = 1, p ∈ ruleprec
  while r = 0
  do
   next(if length.p = 1 ∧ p_1 = lookahead.dup_2 then i else 0, i + 1)
  /for (r)
 let reducepos = 
  for r = 0, i = 1, p ∈ ruleprec
  while r = 0
  do
   next(if length.p > 1 ∧ p = rule1 then i else 0, i + 1)
  /for (r)
 if between(reducepos, 1, shiftpos) then
  {choose reduce} [dup_1]
 else if between(shiftpos, 1, reducepos) then {choose shift} [dup_2] else dup
else
 dup

function printRulePrecedence(ruleprec:seq.seq.word) seq.word
for acc = "{RulePrecedence", @e ∈ ruleprec do
 acc + "|" + @e
/for (acc + "|}")

function lr1parser(grammarandact:seq.seq.seq.word
 , ruleprec:seq.seq.word
 , terminals:seq.word
 , attributename:seq.word
 , codeonly:boolean
 , parameterized:boolean) seq.seq.word
{ruleprec is a list of rules and lookaheads. The position of the lookahead is noted
 . Rule reductions after position are discarded and rule the first rule listed before the position is
 used to reduce. }
let grammar2 = for acc = empty:seq.seq.word, @e ∈ grammarandact do acc + first.@e /for (acc)
let nontermials = for acc = empty:set.word, rule ∈ grammar2 do acc + first.rule /for (acc)
assert isempty(asset.terminals ∩ nontermials) report "terminals and nontermials sets must be distinct"
let alphabet = terminals + toseq.nontermials
let initialstateno = addorder.state.initialstate.grammar2
let symbolsused = for acc = empty:set.word, rule ∈ grammar2 do acc ∪ asset.rule /for (acc)
let missingsymbols = symbolsused \ asset.alphabet
assert isempty(symbolsused \ asset.alphabet)
report "Symbols not included in alphabet $(toseq(symbolsused \ asset.alphabet))"
assert isempty(asset.alphabet \ symbolsused)
report "Symbols in alphabet but not used $(toseq(asset.alphabet \ symbolsused))"
let k = 
 for problems = "", item ∈ ruleprec do
  problems
  + if length.item = 1 ∧ item_1 ∉ alphabet then
   "lookahead $(item) is not in alphabet"
  else if length.item > 1 ∧ item ∉ grammar2 then
   "rule is not in grammar:$(item)"
  else
   ""
 /for (problems)
assert isempty.k report "ruleprec problem $(k)"
let graminfo = grammarinfo(grammar2, follow.grammar2)
let actions = closestate(graminfo, 1, empty:seq.action, asset.terminals)
assert true report print(grammar2, actions)
let dups = dups.actions
let actions2 = 
 for acc = empty:seq.seq.action, @e ∈ dups.actions do
  acc + resolveamb(ruleprec, grammar2, @e)
 /for (acc)
let actions3 = for acc = empty:seq.action, @e ∈ actions2 do acc + @e /for (acc)
let amb = 
 for acc = "", @e ∈ actions2 do
  acc + if length.@e > 1 then "/br >>>> $(print(grammar2, @e))" else empty:seq.word
 /for (acc)
let finalstatebody = 
 for txt = "", a ∈ actions3 do
  if lookahead.a = first."#" ∧ codedaction.a > 0 then
   txt + toword.codedaction.a
  else
   txt
 /for (txt)
let para = if parameterized then ":T" else ""
let result = 
 [generatereduce(grammarandact, alphabet, attributename, ruleprec)] + lextable.terminals
 + [
  "function rulelength $(para) seq.int $(for acc = "
   [", @e ∈ grammarandact do
   acc + toword(length.@e_1 - 1) + ",
    "
  /for (acc >> 1 + "]"))"
  , "function leftside $(para) seq.int $(for acc = "
   [", @e ∈ grammarandact do
   acc + toword.findindex(alphabet, @e_1_1) + ",
    "
  /for (acc >> 1 + "]"))"
  , "function tokenlist $(para) seq.word $(dq.alphabet)"
  , "function startstate $(para) int $(initialstateno)"
  , "function finalstate $(para) int $(finalstatebody)"
  , "function recovery $(para) seq.int $(recovery(alphabet, grammar2))"
  , "function actiontable $(para) seq.int
   $(if length.amb = 0 then
   let x = 
    for table = sparseseq.0, @e ∈ actions3 do
     replaceS(table
      , findindex
      (alphabet, lookahead.@e) + length.alphabet * stateno.@e
      , [codedaction.@e])
    /for (table)
   for acc = "[", @e ∈ x do acc + toword.@e + "
    ," /for (acc >> 1 + "]")
  else
   "{action table omitted} [0]"
  )"]
let header = 
 "/p noactions" + toword.length.actions + "nosymbols:" + toword.length.alphabet
 + "norules:"
 + toword.length.grammarandact
 + "nostate:"
 + toword.length.encodingdata:state
 + "/p"
 + printRulePrecedence.ruleprec
 + if length.amb > 0 then "ambiguous actions:$(amb)" else "" /if
 + if codeonly then "" else print(grammar2, actions3) + print.follow.graminfo
[header] + result

function print(a:graph.word) seq.word
for acc = "nodes", node ∈ toseq.nodes.a do
 acc + "/br" + node + "followed by:" + toseq.successors(a, node)
/for (acc)

function dups(s:seq.action) seq.seq.action
if isempty.s then empty:seq.seq.action else dups(1, sort.s, 1, empty:seq.seq.action)

function dups(startofrun:int, s:seq.action, i:int, result:seq.seq.action) seq.seq.action
if i > length.s then
 result + subseq(s, startofrun, i)
else if s_startofrun = s_i then
 dups(startofrun, s, i + 1, result)
else
 dups(i, s, i + 1, result + subseq(s, startofrun, i - 1))

function closestate(graminfo:grammarinfo, stateno:int, result:seq.action, alphabet:set.word) seq.action
let m = encodingdata:state
if stateno > length.m then
 result
else
 let state = m_stateno
 let reductions = finished.state
 let reduceActions = 
  for acc = empty:seq.action, rule ∈ reductions do
   acc
   + for acc2 = empty:seq.action
    , lookahead ∈ toseq(successors(follow.graminfo, first.rule) ∩ alphabet)
   do
    acc2 + reduce(stateno, lookahead, ruleno(grammar.graminfo, rule))
   /for (acc2)
  /for (acc)
 let newresult = 
  for acc = result + reduceActions, lookahead ∈ toseq.asset.shifts.state do
   let newstate = advance(grammar.graminfo, toset.state, lookahead)
   let newstateno = if isempty.newstate then 0 else addorder.state.newstate
   acc + shift(stateno, lookahead, newstateno)
  /for (acc)
 closestate(graminfo, stateno + 1, newresult, alphabet)

function generatereduce(grammarandact:seq.seq.seq.word
 , alphabet:seq.word
 , attributename:seq.word
 , ruleprec:seq.seq.word) seq.word
"function action (ruleno:int, input:seq.token.$(attributename), R:reduction.$(attributename))
 $(attributename) {Alphabet $(alphabet)} $(if isempty.ruleprec then "" else printRulePrecedence.ruleprec)
 $(for acc = "", i = 1, e ∈ grammarandact do
 let reduceline = "else if ruleno = {$(e_1)
  }" + toword.i + "then" + e_2
 next(acc + reduceline, i + 1)
/for (
 acc << 1 + "else {ruleno} assert false
  report" + dq."invalid rule number"
 + "+toword.ruleno R_1"
))"

Function LR1(input:seq.file, o:seq.word, codeonly:boolean, parameterized:boolean) seq.file
{* A parser generator for a subset of LR1 grammars. 
 /br Codeonly:Only produces generated code
 /br Parameterized:adds T to function name to allowing them to be put into a parameterized module
 /br Assumption:Word ruleno is not used in any action.First use of ruleprec in comment that defines the
 precedence}
let location = breakparagraph.data.first.input
let funcidx = 
 for funcidx = 1, p ∈ location
 while funcidx > 0
 do
  if subseq(p, 1, 2) ∈ ["Function action", "function action"] then
   -funcidx
  else
   funcidx + 1
 /for (-funcidx)
let p = location_funcidx
let x = findindex(p, "Alphabet"_1)
let terminals = subseq(p, x + 1, x + findindex(p << x, "}"_1) - 1)
let a = findindex(p, "RulePrecedence"_1)
let c = 
 break(subseq(p, a, a + findindex(p << a, "}"_1)), "|", false) << 1
let ruleprec = c >> 1
let rules = 
 for acc = empty:seq.seq.seq.word, b ∈ break(p, "ruleno", false) do
  if subseq(b, 1, 2) = "= {" then
   let k = findindex(b, first."}")
   acc + [subseq(b, 3, k - 1), subseq(b, k + 3, length.b - 2)]
  else
   acc
 /for (acc)
let attribute = p_(findindex(p, first.")") + 1)
let nonTerminals = for acc = empty:set.word, r ∈ rules do acc + first.first.r /for (acc)
let terminals2 = 
 for acc = "", t ∈ terminals do if t ∈ nonTerminals then acc else acc + t /for (acc)
let result = lr1parser(rules, ruleprec, terminals2, [attribute], codeonly, parameterized)
for txt = first.result, action = "", otherfuncs = "", p2 ∈ result << 1 do
 let pretty = pretty.p2
 let isaction = subseq(p2, 1, 2) ∈ ["Function action", "function action"]
 next(txt + "/p" + pretty
  , if isaction then pretty else action
  , if isempty.action ∨ isaction then otherfuncs else otherfuncs + "/p" + pretty)
/for (
 let file2 = 
  if length.input < 2 ∨ isempty.otherfuncs then
   empty:seq.file
  else
   for done = false, newfile = "", p3 ∈ breakparagraph.data.input_2
   while not.done
   do
    if subseq(p3, 1, 2) ∈ ["Function lextable", "function lextable"] then
     next(true, newfile)
    else if not.isempty.p3 ∧ first.p3 ∈ "Function function Export type unbound" then
     next(done, newfile + "/p" + pretty.p3)
    else
     next(done, newfile + "/p" + p3)
   /for ([file(filename."+tmp tables.ls", newfile << 1 + otherfuncs)])
 for newfile = "", p3 ∈ location do
  newfile + "/p"
  + if subseq(p3, 1, 2) ∈ ["Function action", "function action"] then
   {use old function header}
   let j = findindex(p, ")"_1)
   subseq(p, 1, j) + action << findindex(action, ")"_1)
  else if not.isempty.p3 ∧ first.p3 ∈ "Function function Export type" then pretty.p3 else p3
 /for ([file(o, txt), file(filename."+tmp action.ls", newfile << 1)] + file2)
) 