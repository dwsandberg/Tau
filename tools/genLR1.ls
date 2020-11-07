#!/usr/local/bin/tau

Module genLR1

/run genLR1 test11

/run genLR1 gentau2

run genLR1 gentaupretty

use seq.action


use seq.dottedrule

use seq.set.dottedrule

use set.dottedrule

use fileio

use format

use otherseq.int

use seq.int

use encoding.state

use seq.state

use stdlib

use seq.arc.word

use set.arc.word

use graph.word

use otherseq.word

use otherseq.seq.word

use seq.seq.seq.word

use seq.seq.word

use seq.word

use set.word



use encoding.state

use stack.word

use stack.seq.word


type state is record toset:set.dottedrule


type dottedrule is record place:int, rule:seq.word


type action is record stateno:int, lookahead:word, codedaction:int

type grammarinfo is record grammar:seq.seq.word, follow:graph.word, ruleprec:seq.seq.word

function =(a:state, b:state)boolean toset.a = toset.b

function =(a:dottedrule, b:dottedrule)boolean rule.a = rule.b ∧ place.a = place.b

function ?(a:dottedrule, b:dottedrule)ordering rule.a ? rule.b ∧ place.a ? place.b

function hash(p:dottedrule)int hash.rule.p + place.p

function assignencoding(l:int, a:state) int l+1


function =(a:action, b:action)boolean lookahead.a = lookahead.b ∧ stateno.a = stateno.b

function hash(s:state)int hash.(toseq.toset.s)_1

function backarc(tail:word, head:word)arc.word arc(head, tail)

function follow1(s:seq.word, i:int)arc.word
 assert i > 1 ∧ i < length.s report s + toword.i
  arc(s_i, s_(i + 1))

function follow2(rule:seq.word)seq.arc.word
 @(+, follow1(rule), empty:seq.arc.word, arithseq(length.rule - 2, 1, 2))

function follow(grammar:seq.seq.word)graph.word follow(newgraph.@(+, follow2, empty:seq.arc.word, grammar), grammar)

function follow3(g:graph.word, rule:seq.word)seq.arc.word
 let a = @(+, arc(last.rule), empty:seq.arc.word, toseq.successors(g, rule_1))
  @(+, backarc(rule_2), a, toseq.predecessors(g, rule_1))

function follow(g:graph.word, grammar:seq.seq.word)graph.word
 let g2 = @(+, follow3(g), g, grammar)
  if g = g2 then g else follow(g2, grammar)

function ruleno(grammar:seq.seq.word, rule:seq.word)int
 let ruleno = if rule = ""then 0 else findindex(rule, grammar)
  assert ruleno ≤ length.grammar report"rule not found" + rule
   ruleno

function state(stateno:int)state if stateno = 0 then state.empty:set.dottedrule else data.(encoding:seq.encodingpair.state)_stateno

function shift(stateno:int, lookahead:word, newstateno:int)action action(stateno, lookahead, newstateno)

function reduce(stateno:int, lookahead:word, ruleno:int)action action(stateno, lookahead, - ruleno)

function getaction(ruleprec:seq.seq.word, grammar:seq.seq.word, state:state, stateno:int, reductions:seq.seq.word, lookahead:word)action
 let newstate = advance(grammar, toset.state, lookahead)
 let newstateno = if not.isempty.newstate then valueofencoding.encode( state.newstate)else 0
  if length.reductions = 0 ∧ newstateno ≠ 0 then shift(stateno, lookahead, newstateno)
  else if length.reductions = 1 ∧ newstateno = 0 then reduce(stateno, lookahead, ruleno(grammar, reductions_1))
  else
   let lookplace = findindex([ lookahead], ruleprec)
   let yy = if lookplace > length.ruleprec then empty:seq.seq.word
   else @(+, tosubstate(reductions), empty:seq.seq.word, subseq(ruleprec, 1, lookplace - 1))
    if length.yy = 1 then reduce(stateno, lookahead, ruleno(grammar, yy_1))
    else if length.yy = 0 ∧ newstateno ≠ 0 then shift(stateno, lookahead, newstateno)
    else
     let r = if length.yy = 0 then reductions else yy
      if length.r = 2 ∧ r_1 = "E - E"
      ∧ r_2 = "E E - E"then
      // assert false report"<>"+ lookahead + toword.length.yy + print.r //
       reduce(stateno, lookahead, ruleno(grammar, r_2))
      else // ERROR ambiguous // action(stateno, lookahead, 0)

function print(a:seq.seq.word)seq.word @(seperator(" &br"), identity,"", a)

function printstate(stateno:int)seq.word [ toword.stateno]

function alphabet(grammar:seq.seq.word)seq.word toseq.asset.@(+, identity,"", grammar)

function addaction(alphabet:seq.word, table:seq.int, a:action)seq.int
 replace(table, findindex(lookahead.a, alphabet) + length.alphabet * stateno.a, codedaction.a)

function first(a:seq.seq.word)seq.word a_1

function first(a:seq.word)word a_1

function tosubstate(state:seq.seq.word, rule:seq.word)seq.seq.word
 if rule in state then [ rule]else empty:seq.seq.word

function print(p:dottedrule)seq.word
 subseq(rule.p, 1, place.p - 1) + "'"
 + subseq(rule.p, place.p, length.rule.p)

function print(s:state)seq.word
 '  &br"' + @(seperator("|"), print,"", toseq.toset.s) + '  &br"'

Function initialstate(grammar:seq.seq.word)set.dottedrule close(grammar, asset.[ dottedrule(2,"G F #")])

function close(g:seq.seq.word, s:set.dottedrule)set.dottedrule
 let newset = @(∪, close(g), s, toseq.s)
  if s = newset then s else close(g, newset)

function close(g:seq.seq.word, p:dottedrule)set.dottedrule
 if place.p > length.rule.p then empty:set.dottedrule
 else asset.@(+, startswith((rule.p)_(place.p)), empty:seq.dottedrule, g)

function startswith(first:word, x:seq.word)seq.dottedrule
 if x_1 = first then [ dottedrule(2, x)]else empty:seq.dottedrule

function advance(g:seq.seq.word, state:set.dottedrule, next:word)set.dottedrule
 close(g, asset.@(+, advance(next), empty:seq.dottedrule, toseq.state))

function advance(next:word, p:dottedrule)seq.dottedrule
 if place.p ≤ length.rule.p ∧ (rule.p)_(place.p) = next then
 [ dottedrule(place.p + 1, rule.p)]
 else empty:seq.dottedrule

function finished(p:dottedrule)seq.seq.word
 if place.p = length.rule.p + 1 then [ rule.p]else empty:seq.seq.word

function finished(s:state)seq.seq.word @(+, finished, empty:seq.seq.word, toseq.toset.s)

function shifts(p:dottedrule)seq.word
 if place.p = length.rule.p + 1 then empty:seq.word else [(rule.p)_(place.p)]

function shifts(s:state)seq.word toseq.asset.@(+, shifts, empty:seq.word, toseq.toset.s)

Function lr1parser(grammarandact:seq.seq.seq.word, ruleprec:seq.seq.word, alphabet:seq.word)seq.word
 let grammar2 = @(+, first, empty:seq.seq.word, grammarandact)
 let initialstateno = valueofencoding.encode(  state.initialstate.grammar2)
 let missingsymbols = asset.alphabet - asset.alphabet.grammar2
  assert isempty.missingsymbols report"Symbols not included in alphabet" + toseq.missingsymbols
  let graminfo = grammarinfo(grammar2, follow.grammar2, ruleprec)
  let actions = closestate(graminfo, 1, empty:seq.action)
  let amb = @(+, isambiguous,"", actions)
   {(if length.amb > 0 then"ambiguous actions:" + amb else"")
   + generatereduce(grammarandact, alphabet,"attribute")
   + '  &p function tokenlist seq.word"'
   + alphabet
   + '"'
   + " &p function startstate:T int"
   + toword.initialstateno
   + " &p noactions"
   + toword.length.actions
   + " &br nosymbols:"
   + toword.length.alphabet
   + " &br norules"
   + toword.length.grammarandact
   + " &br nostate"
   + toword.length.encoding:seq.encodingpair.state
   + " &p function actiontable:T seq.int ["
   + @(seperator(","), toword,"", @(addaction(alphabet), identity, dseq.0, actions))
   + "]"
   + " &p follow"
   + @(seperator("|"), print,"", toseq.arcs.follow.graminfo)
   + printstatefunc(encoding:seq.encodingpair.state, 1,"")}

function printstatefunc(s:seq.encodingpair.state, i:int, result:seq.word)seq.word
 if i > length.s then result + "]_stateno"
 else
  let a = if i > 1 then","else '  &p function printstate(stateno:int)seq.word  &br [ '
  let b ="//" + toword.i + "//" + print.data(s_i)
   printstatefunc(s, i + 1, result + a + b)

function isambiguous(a:action)seq.word
 if codedaction.a = 0 then" &br" + toword.stateno.a + lookahead.a else""

function print(a:arc.word)seq.word [ tail.a] + ">" + head.a

use seq.encodingpair.state

use encoding.state

function closestate(graminfo:grammarinfo, stateno:int, result:seq.action)seq.action
 let m = encoding:seq.encodingpair.state
  if stateno > length.m then result
  else
   let state = data.m_stateno
   let reductions = finished.state
   let follows = @(∪, successors(follow.graminfo), empty:set.word, @(+, first,"", reductions))
   let newresult = @(+, getaction(ruleprec.graminfo, grammar.graminfo, state, stateno, reductions), result, toseq(asset.shifts.state ∪ follows))
    closestate(graminfo, stateno + 1, newresult)

Function generatereduce(grammarandact:seq.seq.seq.word, alphabet:seq.word, attribute:seq.word)seq.word
 " &br  &br Function action(ruleno:int, input:seq.token." + attribute + ", R:reduction."
 + attribute
 + ")"
 + attribute
 + @(+, reduceline(grammarandact),"", arithseq(length.grammarandact, 1, 1))
 + " &p function rulelength:T seq.int ["
 + @(seperator(","), rulelength,"", grammarandact)
 + "] &p function leftside:T seq.int ["
 + @(seperator(","), leftside(alphabet),"", grammarandact)
 + ']'

function rulelength(a:seq.seq.word)word toword(length.a_1 - 1)

function leftside(alphabet:seq.word, a:seq.seq.word)word toword.findindex(a_1_1, alphabet)

function replace$(w:word)seq.word if w = "let"_1 then" &br let"else [ w]

function reduceline(grammerandact:seq.seq.seq.word, i:int)seq.word
 let s = grammerandact_i
  if i = length.grammerandact then
  " &br assert ruleno = //" + s_1 + "//" + toword.i
   + ' report"invalid rule number"+ toword.ruleno  &br '
   + @(+, replace$,"", s_2)
  else
   " &br if ruleno = //" + s_1 + "//" + toword.i + "then"
   + @(+, replace$,"", s_2)
   + "else"

Function gentau2 seq.word // used to generater tau parser for Pass1 of the tau compiler. //
let a = lr1parser(taurules2, tauruleprec,".=():>]- { } comment, [_^is T if # then else let assert report ∧ ∨ * $wordlist @ A E G F W P N L I K FP NM")
let discard = createfile([ merge."junk/newgrammer.ls"], processtotext.a)
 a

function tauruleprec seq.seq.word ["E E_E","_","E comment E","E W.E","E N.E",".","E - E","E E * E","*","E E - E"
,"-","E E > E","E E = E","=",">","E E ∧ E","∧","E E ∨ E","∨"]

function taurules2 seq.seq.seq.word [ [ ' G F # ', ' R_1 ']
, [ ' F W NM(FP)T E ', ' createfunc(R, input, code.R_2, types.R_4, R_6, R_7)']
, [ ' F W NM T E ', ' createfunc(R, input, code.R_2, empty:seq.mytype, R_3, R_4)']
, [ ' F W W is W P ', ' assert(code.R_4)_1 in"record encoding sequence"report errormessage("Expected record encoding or sequence after is in type definition got:"+ code.R_4, input, place.R)bindinfo(dict.R, code.R_4 + code.R_2 + code.R_5, types.R_5)']
, [ ' F T ', ' bindinfo(dict.R, gettype.R_1, empty:seq.mytype)']
, [ ' FP P ', ' bindinfo(@(addparameter(cardinality.dict.R, input, place.R), identity, dict.R, types.R_1),"", types.R_1)']
, [ ' P T ', // use // ' bindinfo(dict.R,"", [ mytype(gettype.R_1 +":")])']
, [ ' P P, T ', ' bindinfo(dict.R,"", types.R_1 + [ mytype(gettype.R_3 +":")])']
, [ ' P W:T ', ' bindinfo(dict.R, code.R_1 + code.R_3, [ mytype(gettype.R_3 + code.R_1)])']
, [ ' P P, W:T ', ' bindinfo(dict.R, code.R_1 + code.R_3 + code.R_5, types.R_1 + [ mytype(gettype.R_5 + code.R_3)])']
, [ ' P comment W:T ', ' bindinfo(dict.R,"//"+ code.R_1 +"//"+ code.R_2 + code.R_4, [ mytype(gettype.R_4 + code.R_2)])']
, [ ' P P, comment W:T ', ' bindinfo(dict.R,"//"+ code.R_3 +"//"+ code.R_1 + code.R_4 + code.R_6, types.R_1 + [ mytype(gettype.R_6 + code.R_4)])']
, [ ' E NM ', ' let id = code.R_1 let f = lookupbysig(dict.R, id_1, empty:seq.mytype, input, place.R)bindinfo(dict.R, [ mangledname.f], [ resulttype.f])']
, [ ' E NM(L)', ' unaryop(R, input, code.R_1, R_3)']
, [ ' E(E)', ' R_2 ']
, [ ' E { E } ', ' R_2 ']
, [ ' E if E then E else E ', ' let thenpart = R_4 assert(types.R_2)_1 = mytype."boolean"report errormessage("cond of if must be boolean", input, place.R)assert types.R_4 = types.R_6 report errormessage("then and else types are different", input, place.R)let newcode = code.R_2 + code.R_4 + code.R_6 bindinfo(dict.R, newcode +"if", types.thenpart)']
, [ ' E E^E ', ' opaction(R, input)']
, [ ' E E_E ', ' opaction(R, input)']
, [ ' E - E ', ' unaryop(R, input, code.R_1, R_2)']
, [ ' E W.E ', ' unaryop(R, input, code.R_1, R_3)']
, [ ' E N.E ', ' unaryop(R, input, code.R_1, R_3)']
, [ ' E E * E ', ' opaction(R, input)']
, [ ' E E - E ', ' opaction(R, input)']
, [ ' E E = E ', ' opaction(R, input)']
, [ ' E E > E ', ' opaction(R, input)']
, [ ' E E ∧ E ', ' opaction(R, input)']
, [ ' E E ∨ E ', ' opaction(R, input)']
, [ ' L E ', ' R_1 ']
, [ ' L L, E ', ' bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3)']
, [ ' E [ L]', ' let types = types.R_2 assert @(∧, =(types_1), true, types)report errormessage("types do not match in build", input, place.R)bindinfo(dict.R,"LIT 0 LIT"+ toword.length.types + code.R_2 +"RECORD"+ toword(length.types + 2), [ mytype(towords.types_1 +"seq")])']
, [ ' A let W = E ', ' let e = R_4 let name =(code.R_2)_1 assert isempty.lookup(dict.R, name, empty:seq.mytype)report errormessage("duplicate symbol:"+ name, input, place.R)let newdict = dict.R + symbol(name, mytype."local", empty:seq.mytype,(types.e)_1,"")bindinfo(newdict, code.e +"define"+ name, types.e)']
, [ ' E A E ', ' let t = code.R_1 let f = lookup(dict.R, last.code.R_1, empty:seq.mytype)assert not.isempty.f report"internal error/could not find local symbol to delete from dict with name"+ last.code.R_1 bindinfo(dict.R_1 - f_1, subseq(t, 1, length.t - 2)+ code.R_2 +"SET"+ last.code.R_1, types.R_2)']
, [ ' E assert E report E E ', ' assert(types.R_2)_1 = mytype."boolean"report errormessage("condition in assert must be boolean in:", input, place.R)assert(types.R_4)_1 = mytype."word seq"report errormessage("report in assert must be seq of word in:", input, place.R)let newcode = code.R_2 + code.R_5 + code.R_4 +"assertZbuiltinZwordzseq if"bindinfo(dict.R, newcode, types.R_5)']
, [ ' E I ', ' bindinfo(dict.R,"LIT"+ code.R_1, [ mytype."int"])']
, [ ' E I.I ', ' bindinfo(dict.R,"WORDS 3"+ code.R_1 +"."+ code.R_3 +"makerealZUTF8Zwordzseq", [ mytype."real"])']
, [ ' T W ', ' isdefined(R, input, code.R_1)']
, [ ' T W.T ', ' isdefined(R, input, towords.(types.R_3)_1 + code.R_1)']
, [ ' E $wordlist ', ' let s = code.R_1 bindinfo(dict.R,"WORDS"+ toword.(length.s - 2)+ subseq(s, 2, length.s - 1), [ mytype."word seq"])']
, [ ' E comment E ', ' let s = code.R_1 bindinfo(dict.R, code.R_2 +"COMMENT"+ toword.(length.s - 2)+ subseq(s, 2, length.s - 1), types.R_2)']
, [ ' N_', ' R_1 ']
, [ ' N - ', ' R_1 ']
, [ ' N = ', ' R_1 ']
, [ ' N > ', ' R_1 ']
, [ ' N * ', ' R_1 ']
, [ ' N ∧ ', ' R_1 ']
, [ ' N ∨ ', ' R_1 ']
, [ ' K W.E ', ' bindinfo(dict.R, code.R_1 + code.R_3, types.R_3)']
, [ ' K N.E ', ' bindinfo(dict.R, code.R_1 + code.R_3, types.R_3)']
, [ ' K NM(L)', ' bindinfo(dict.R, code.R_1 + code.R_3, types.R_3)']
, [ ' K NM ', ' R_1 ']
, [ ' NM W ', ' R_1 ']
, [ ' NM N ', ' R_1 ']
, [ ' NM W:T ', ' bindinfo(dict.R, [ merge(code.R_1 +":"+ print.(types.R_3)_1)], empty:seq.mytype)']
, [ ' E @(K, K, E, E)', ' apply(R_3, R_5, R_7, R_9, input, place.R)']]

M N M W M W:T K M K M(L)K W.E K N.E - K N - K W

Function gentaupretty seq.word // used to generater tau parser for Pass1 of the tau compiler. //
let a = lr1parser(tauprettyrules, tauruleprec,".=():>]- { } comment, [_^is T if # then else let assert report ∧ ∨ * $wordlist @ A E G F W P N L I K FP")
let discard = createfile("prettygrammer.ls", processtotext.a)
 a

function tauprettyrules seq.seq.seq.word [ ["G F #","R_1"]
, ["F W NM(FP)T E","pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block(R_7)else R_7]"]
, ["F W NM T E","pretty.[ key.R_1, R_2, R_3, R_4]"]
, ["F W W is W P","pretty.[ key.R_1, R_2, R_3, R_4, list.R_5]"]
, ["F T","// use // pretty.[ R_2]"]
, ["FP P","list.R_1"]
, ["P T","R_1"]
, ["P P, T","R_1 + R_3"]
, ["P W:T","pretty.[ R_1, R_2, R_3]"]
, ["P P, W:T","R_1 + pretty.[ R_3, R_4, R_5]"]
, ["P comment W:T","pretty.[ R_1, R_2, R_3, R_4]"]
, ["P P, comment W:T","R_1 + pretty.[ R_3, R_4, R_5, R_6]"]
, ["E NM","R_1"]
, ["E NM(L)", ' if length.R_3 = 1 then wrap(3, R_1,".", R_3)else pretty.[ R_1, R_2, list.R_3, R_4]']
, ["E(E)","R_2"]
, ["E { E }","R_2"]
, ["E if E then E else E", ' pretty.[ R_1, R_2, key.R_3, R_4, key.R_5, R_6]else if width.R_2 + width.R_4 < 30 then pretty.[ R_1, R_2, key.R_3, R_4, elseblock.R_6]else pretty.[ R_1, R_2, attribute." &keyword then 
&br", block.R_4, elseblock.R_6]']
, ["E E^E","wrap(1, R_1, text.R_2, R_3)"]
, ["E E_E","wrap(1, R_1, text.R_2, R_3)"]
, ["E - E", ' unaryminus.R_2 ']
, ["E W.E","wrap(3, R_1, text.R_2, R_3)"]
, ["E N.E","wrap(3, R_1, text.R_2, R_3)"]
, ["E E * E","wrap(4, R_1, text.R_2, R_3)"]
, ["E E - E","wrap(5, R_1, text.R_2, R_3)"]
, ["E E = E","wrap(6, R_1, text.R_2, R_3)"]
, ["E E > E","wrap(7, R_1, text.R_2, R_3)"]
, ["E E ∧ E","wrap(8, R_1, text.R_2, R_3)"]
, ["E E ∨ E","wrap(9, R_1, text.R_2, R_3)"]
, ["L E","R_1"]
, ["L L, E","R_1 + R_3"]
, ["E [ L]","pretty.[ R_1, list.R_2, R_3]"]
, ["A let W = E", ' pretty.[ R_1, R_2, R_3, R_4]']
, ["E A E", ' pretty.[ R_1, checkpara(R_1, block("
&br let assert", R_2))']
, ["E assert E report E E", ' pretty.[ R_1, R_2, key.R_3, R_4, block("
&br let assert", R_5)]']
, ["E I","R_1"]
, ["E I.I","pretty.[ R_1, R_2, R_3]"]
, ["T W","R_1"]
, ["T W.T","pretty.[ R_1, R_2, R_3]"]
, ["E $wordlist", ' attribute([ prettyresult(0, length.text.R_1,"
&{ literal"+ escapeformat.text.R_1 +" &}")])']
, ["E comment E", ' let t ="
&{ comment"+ escapeformat.text.R_1 +" &}"let t2 = if width.R_1 + width.R_2 > 30 ∧(text.R_2)_1 ≠"
&br"_1 then t +"
&br"else t pretty.[ attribute.[ prettyresult(0, length.text.R_1, t2)], R_2]']
, ["N_","R_1"]
, ["N -","R_1"]
, ["N =","R_1"]
, ["N >","R_1"]
, ["N *","R_1"]
, ["N ∧","R_1"]
, ["N ∨","R_1"]
, ["K W.E","pretty.[ R_1, R_2, R_3]"]
, ["K N.E","pretty.[ R_1, R_2, R_3]"]
, ["K NM(L)","pretty.[ R_1, R_2, list.R_3, R_4]"]
, [ ' K NM ', ' R_1 ']
, [ ' NM W ', ' R_1 ']
, [ ' NM N ', ' R_1 ']
, [ ' NM W:T ',"pretty.[ R_1, R_2, R_3]"]
, ["E @(K, K, E, E)","pretty.[ R_1, R_2, list(R_3 + R_5 + R_7 + R_9), R_10]"]]

Function test11 seq.word extractgrammer
.' Function action(ruleno:int, input:seq.token.attribute, R:reduction.attribute)attribute if ruleno = // G F # // 1 then R_1 else if ruleno = // F W W(FP)T E // 2 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]else if ruleno = // F W N(FP)T E // 3 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]else if ruleno = // F W W T E // 4 then pretty.[ key.R_1, R_2, R_3, R_4]else if ruleno = // F W W:T T E // 5 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6]else if ruleno = // F W W:T(FP)T E // 6 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, R_7, R_8, R_9]else if ruleno = // F W W is W P // 7 then pretty.[ key.R_1, R_2, R_3, R_4, list.R_5]else if ruleno = // F W T // 8 then // use // pretty.[ key.R_1, R_2]else if ruleno = // FP P // 9 then list.R_1 else if ruleno = // P T // 10 then R_1 else if ruleno = // P P, T // 11 then R_1 + R_3 else if ruleno = // P W:T // 12 then pretty.[ R_1, R_2, R_3]else if ruleno = // P P, W:T // 13 then R_1 + pretty.[ R_3, R_4, R_5]else if ruleno = // P comment W:T // 14 then pretty.[ R_1, R_2, R_3, R_4]else if ruleno = // P P, comment W:T // 15 then R_1 + pretty.[ R_3, R_4, R_5, R_6]else if ruleno = // E W // 16 then R_1 else if ruleno = // E N(L)// 17 then if length.R_3 = 1 then wrap(3, R_1,".", R_3)else pretty.[ R_1, R_2, list.R_3, R_4]else if ruleno = // E W(L)// 18 then if length.R_3 = 1 then wrap(3, R_1,".", R_3)else pretty.[ R_1, R_2, list.R_3, R_4]else if ruleno = // E W:T(L)// 19 then pretty.[ R_1, R_2, R_3, R_4, list.R_5, R_6]else if ruleno = // E(E)// 20 then R_2 else if ruleno = // E { E } // 21 then R_2 else if ruleno = // E if E then E else E // 22 then if width.R_2 + width.R_4 + width.R_6 < 30 then pretty.[ R_1, R_2, key.R_3, R_4, key.R_5, R_6]else if width.R_2 + width.R_4 < 30 then pretty.[ R_1, R_2, key.R_3, R_4, elseblock.R_6]else pretty.[ R_1, R_2, attribute." &keyword then 
&br", block.R_4, elseblock.R_6]else if ruleno = // E E^E // 23 then wrap(1, R_1, text.R_2, R_3)else if ruleno = // E E_E // 24 then wrap(1, R_1, text.R_2, R_3)else if ruleno = // E - E // 25 then unaryminus.R_2 else if ruleno = // E W.E // 26 then wrap(3, R_1, text.R_2, R_3)else if ruleno = // E N.E // 27 then wrap(3, R_1, text.R_2, R_3)else if ruleno = // E E * E // 28 then wrap(4, R_1, text.R_2, R_3)else if ruleno = // E E - E // 29 then wrap(5, R_1, text.R_2, R_3)else if ruleno = // E E = E // 30 then wrap(6, R_1, text.R_2, R_3)else if ruleno = // E E > E // 31 then wrap(7, R_1, text.R_2, R_3)else if ruleno = // E E ∧ E // 32 then wrap(8, R_1, text.R_2, R_3)else if ruleno = // E E ∨ E // 33 then wrap(9, R_1, text.R_2, R_3)else if ruleno = // L E // 34 then R_1 else if ruleno = // L L, E // 35 then R_1 + R_3 else if ruleno = // E [ L]// 36 then pretty.[ R_1, list.R_2, R_3]else if ruleno = // A let W = E // 37 then pretty.[ R_1, R_2, R_3, R_4]else if ruleno = // E A E // 38 then checkpara(R_1, block("
&br let assert", R_2))else if ruleno = // E assert E report E E // 39 then pretty.[ R_1, R_2, key.R_3, R_4, block("
&br let assert", R_5)]else if ruleno = // E I // 40 then R_1 else if ruleno = // E I.I // 41 then pretty.[ R_1, R_2, R_3]else if ruleno = // T W // 42 then R_1 else if ruleno = // T W.T // 43 then pretty.[ R_1, R_2, R_3]else if ruleno = // E W:T // 44 then pretty.[ R_1, R_2, R_3]else if ruleno = // E $wordlist // 45 then // attribute("
&{ literal"+ escapeformat.fixstring(text.R_1, 1)+" &}")// attribute([ prettyresult(0, length.text.R_1,"
&{ literal"+ escapeformat.text.R_1 +" &}")])else if ruleno = // E comment E // 46 then let t ="
&{ comment"+ escapeformat.text.R_1 +" &}"let t2 = if width.R_1 + width.R_2 > 30 ∧(text.R_2)_1 ≠"
&br"_1 then t +"
&br"else t pretty.[ attribute.[ prettyresult(0, length.text.R_1, t2)], R_2]else if ruleno = // N_// 47 then R_1 else if ruleno = // N - // 48 then R_1 else if ruleno = // N = // 49 then R_1 else if ruleno = // N > // 50 then R_1 else if ruleno = // N * // 51 then R_1 else if ruleno = // N ∧ // 52 then R_1 else if ruleno = // N ∨ // 53 then R_1 else if ruleno = // K W.E // 54 then pretty.[ R_1, R_2, R_3]else if ruleno = // K N.E // 55 then pretty.[ R_1, R_2, R_3]else if ruleno = // K N(L)// 56 then pretty.[ R_1, R_2, list.R_3, R_4]else if ruleno = // K W(L)// 57 then pretty.[ R_1, R_2, list.R_3, R_4]else if ruleno = // K N // 58 then R_1 else if ruleno = // K W // 59 then R_1 else assert ruleno = // E @(K, K, E, E)// 60 report"invalid rule number"+ toword.ruleno pretty.[ R_1, R_2, list.(R_3 + R_5 + R_7 + R_9), R_10]'

Function extractgrammer(z:seq.word)seq.word // use to extract grammar and rules from action procedure generated by genLR1 // extractgrammer(z, 1,"BEGIN", 1,"")

function extractgrammer(z:seq.word, i:int, state:seq.word, mark:int, result:seq.word)seq.word
 if i > length.z then
 "[ '" + result + subseq(z, mark, i - 1) + "]]"
 else if z_i = "//"_1 then
 if state = "BEGIN"then extractgrammer(z, i + 1,"INRULE", i + 1, result)
  else if state = "INRULE"then
  extractgrammer(z, i + 3,"INACTION", i + 3, result + "'" + subseq(z, mark, i - 1) + "', '")
  else extractgrammer(z, i + 1, state, mark, result)
 else if subseq(z, i, i + 4) in ["else if ruleno = //","else assert ruleno = //"]then
 extractgrammer(z, i + 5,"INRULE", i + 5, result + subseq(z, mark, i - 1) + "'] &br, [")
 else extractgrammer(z, i + 1, state, mark, result)