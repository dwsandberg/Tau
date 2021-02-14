#!/usr/local/bin/tau ; use genLR1 ;  gentau2

Module genLR1

/run genLR1 test11

/run genLR1 gentau2

use format

use standard

use otherseq.action

use seq.action

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

function assignencoding(l:int, a:state)int l + 1

function =(a:action, b:action)boolean lookahead.a = lookahead.b ∧ stateno.a = stateno.b

function ?(a:action, b:action)ordering stateno.a ? stateno.b ∧ lookahead.a ? lookahead.b  

function print(a:action)seq.word
 " &br state:" + toword.stateno.a + "lookahead:" + lookahead.a
 + if codedaction.a < 0 then"reduce" + toword.-codedaction.a
 else"shift" + toword.codedaction.a
 
function print(grammar:seq.seq.word, a:seq.action)seq.word print(grammar, a, 1,-1, 0,"")

function print (grammar:seq.seq.word,a:seq.action,i:int,laststate:int,lastaction:int,result:seq.word) seq.word
 if i > length.a then result
 else
 let this=a_i
  let p1 = if laststate ≠ stateno.this then" &br state:" + toword.stateno.this else""
  let p2 = if lastaction ≠ codedaction.this then
  if codedaction.this < 0 then"reduce" + grammar_(-codedaction.this) + ";"
    else "shift"+toword.codedaction.this
     else ""
    print(grammar,a,i+1,stateno.this,codedaction.this,result+p1+p2+lookahead.this)
    
function hash(s:state)int hash.(toseq.toset.s)_1

function backarc(tail:word, head:word)arc.word arc(head, tail)

function follow1(s:seq.word, i:int)arc.word
 assert i > 1 ∧ i < length.s report s + toword.i
  arc(s_i, s_(i + 1))

function follow2(rule:seq.word)seq.arc.word
 for @e ∈ arithseq(length.rule - 2, 1, 2), acc = empty:seq.arc.word ,,, acc + follow1(rule, @e)

function follow(grammar:seq.seq.word)graph.word
 follow(newgraph.for @e ∈ grammar, acc = empty:seq.arc.word ,,, acc + follow2.@e, grammar)

function follow3(g:graph.word, rule:seq.word)seq.arc.word
 let a = for @e ∈ toseq.successors(g, rule_1), acc = empty:seq.arc.word ,,, acc + arc(last.rule, @e)
  for @e ∈ toseq.predecessors(g, rule_1), acc = a ,,, acc + backarc(rule_2, @e)

function follow(g:graph.word, grammar:seq.seq.word)graph.word
 let g2 = for @e ∈ grammar, acc = g ,,, acc + follow3(g, @e)
  if g = g2 then g else follow(g2, grammar)

function ruleno(grammar:seq.seq.word, rule:seq.word)int
 let ruleno = if rule = ""then 0 else findindex(rule, grammar)
  assert ruleno ≤ length.grammar report"rule not found" + rule
   ruleno

function state(stateno:int)state
 if stateno = 0 then state.empty:set.dottedrule else data.encoding:seq.encodingpair.state_stateno

function shift(stateno:int, lookahead:word, newstateno:int)action action(stateno, lookahead, newstateno)

function reduce(stateno:int, lookahead:word, ruleno:int)action action(stateno, lookahead,-ruleno)

type ruleprec is  lookahead:word, rules:seq.int

function print(grammar:seq.seq.word, p:ruleprec)seq.word
 "lookahead:" + lookahead.p
 + for @e ∈ rules.p, acc ="",,, list(acc,"|", grammar_@e)
  

             
function =(a:ruleprec,b:ruleprec) boolean  lookahead.a=lookahead.b 
   
function print(a:seq.seq.word)seq.word for @e ∈ a, acc ="",,, list(acc," &br", @e)

function printstate(stateno:int)seq.word [ toword.stateno]

function alphabet(grammar:seq.seq.word)seq.word toseq.asset.for @e ∈ grammar, acc ="",,, acc + @e



function tosubstate(state:seq.seq.word, rule:seq.word)seq.seq.word
 if rule ∈ state then [ rule]else empty:seq.seq.word

function print(p:dottedrule)seq.word
 subseq(rule.p, 1, place.p - 1) + "'"
 + subseq(rule.p, place.p, length.rule.p)

function print(s:state)seq.word
 '  &br"' + for @e ∈ toseq.toset.s, acc ="",,, list(acc,"|", print.@e);
 + '  &br"'

Function initialstate(grammar:seq.seq.word)set.dottedrule close(grammar, asset.[ dottedrule(2,"G F #")])

Function finalstate(grammar:seq.seq.word)set.dottedrule close(grammar, asset.[ dottedrule(3,"G F #")])

function close(g:seq.seq.word, s:set.dottedrule)set.dottedrule
 let newset = for @e ∈ toseq.s, acc = s ,,, acc ∪ close(g, @e)
  if s = newset then s else close(g, newset)

function close(g:seq.seq.word, p:dottedrule)set.dottedrule
 if place.p > length.rule.p then empty:set.dottedrule
 else
  asset.for @e ∈ g, acc = empty:seq.dottedrule ,,, acc + startswith((rule.p)_(place.p), @e)

function startswith(first:word, x:seq.word)seq.dottedrule
 if x_1 = first then [ dottedrule(2, x)]else empty:seq.dottedrule

function advance(g:seq.seq.word, state:set.dottedrule, next:word)set.dottedrule
 close(g, asset.for @e ∈ toseq.state, acc = empty:seq.dottedrule ,,, acc + advance(next, @e))

function advance(next:word, p:dottedrule)seq.dottedrule
 if place.p ≤ length.rule.p ∧ (rule.p)_(place.p) = next then
 [ dottedrule(place.p + 1, rule.p)]
 else empty:seq.dottedrule

 
function finished(s:state)seq.seq.word for p ∈ toseq.toset.s, acc = empty:seq.seq.word ,,, 
acc + if place.p = length.rule.p + 1 then [ rule.p]else empty:seq.seq.word



function shifts(s:state)seq.word
 toseq.asset.for p ∈ toseq.toset.s, acc = empty:seq.word ,,, 
  acc +  if place.p = length.rule.p + 1 then empty:seq.word else [(rule.p)_(place.p)]

function resolveamb(ruleprec:seq.seq.word,grammar:seq.seq.word,dup:seq.action) seq.action
    if length.dup=1 then dup else 
    if length.dup > 1 &and codedaction.dup_1 < 0 &and  codedaction.dup_2 > 0 then
      let rule1=grammar_-(codedaction.dup_1)
      let shiftpos=   for p &in ruleprec , r=0,i, length.p=1 &and p_1=lookahead.dup_2 , 
       if length.p=1 &and p_1=lookahead.dup_2 then i else 0 
      let reducepos= for p &in ruleprec , r=0,i, length.p > 1 &and p=rule1 , 
       if length.p > 1 &and p=rule1 then i else 0 
       if between(reducepos, 1,shiftpos) then  \\ choose reduce \\ [dup_1]
       else  if between(shiftpos,1,reducepos ) then \\ choose shift \\ [dup_2]
       else
      dup
      else dup
      
Function lr1parser(grammarandact:seq.seq.seq.word, ruleprec:seq.seq.word, alphabet:seq.word,attributename:seq.word)seq.word
 let grammar2 = for @e ∈ grammarandact, acc = empty:seq.seq.word ,,, acc + first.@e
 let initialstateno = valueofencoding.encode.state.initialstate.grammar2
 let finalstateno=valueofencoding.encode.state.finalstate.grammar2  
 let missingsymbols = asset.alphabet - asset.alphabet.grammar2
    assert isempty.missingsymbols report"Symbols not included in alphabet"+ toseq.missingsymbols 
  let graminfo = grammarinfo(grammar2, follow.grammar2, ruleprec)
  let actions = closestate(graminfo, 1, empty:seq.action)
   \\ assert false report print(grammar2, actions)\\
    let dups=dups.actions 
   let actions2 = for @e ∈ dups.actions, acc = empty:seq.seq.action ,,, acc + 
     resolveamb(ruleprec,  grammar2,@e)
    let actions3=for @e ∈ actions2, acc = empty:seq.action ,,, acc + @e
   let amb = for @e ∈ actions2, acc ="",,, acc + 
        if length.@e > 1 then   "&br >>>>"+print(grammar2,@e)  else empty:seq.word
    if length.amb > 0 then
    "ambiguous actions:" + amb + " &br prec rules"
     + for @e ∈ ruleprec, acc ="",,,  acc+"|"+@e  
    else"";
   + print(grammar2,actions3)  
   + generatereduce(grammarandact, alphabet,attributename)
   + '  &p function tokenlist:T seq.word"'
   + alphabet
   + '"'
    + " &p function startstate:T int"
    + toword.initialstateno
    + " &p function finalstate:T int"
    + toword.finalstateno
   +    " &p noactions"
   + toword.length.actions
   + " &br nosymbols:"
   + toword.length.alphabet
   + " &br norules"
   + toword.length.grammarandact
   + " &br nostate"
   + toword.length.encoding:seq.encodingpair.state
    + if length.amb = 0 then
    let x = for @e ∈ actions3, table = sparseseq.0 ,,, 
     replaceS(table, findindex(lookahead.@e, alphabet) + length.alphabet * stateno.@e, [codedaction.@e])
      " &p function actiontable:T seq.int ["
      + for @e ∈ x, acc ="",,, list(acc,",", [ toword.@e]);
   + "]" 
    else"";
   + " &p follow"
    + print.follow.graminfo
    + printstatefunc(encoding:seq.encodingpair.state, 1,"")
 
function print(a:graph.word)seq.word for node ∈ toseq.nodes.a, acc ="nodes",,, acc + 
    "&br"+node+ "followed by:"+ toseq.successors(a,node)
 

function dups(s:seq.action)seq.seq.action
 if isempty.s then empty:seq.seq.action else dups(1, sort.s, 1, empty:seq.seq.action)
   
function dups(  startofrun:int,s:seq.action,i:int,result:seq.seq.action  ) seq.seq.action
 if i > length.s then result + subseq(s, startofrun, i)
    else   if s_startofrun=s_i then dups(startofrun,s,i+1,result)
 else dups(i, s, i + 1, result + subseq(s, startofrun, i - 1))

function printstatefunc(s:seq.encodingpair.state, i:int, result:seq.word)seq.word
 if i > length.s then result + "]_stateno"
 else
  let a = if i > 1 then","else '  &p function printstate(stateno:int)seq.word  &br [ '
  let b ="//" + toword.i + "//" + print.data.s_i
   printstatefunc(s, i + 1, result + a + b)


function closestate(graminfo:grammarinfo, stateno:int, result:seq.action)seq.action
 let m = encoding:seq.encodingpair.state
  if stateno > length.m then result
  else
   let state = data.m_stateno
   let reductions = finished.state
   let reduceActions= for rule &in reductions ,acc=empty:seq.action ,,, 
      acc+
      for lookahead &in  toseq.successors(follow.graminfo, first.rule) , acc2=empty:seq.action ,,,
       acc2+reduce(stateno, lookahead, ruleno(grammar.graminfo, rule))
   let newresult= for lookahead ∈ toseq.asset.shifts.state ,acc=result+reduceActions ,,, 
       let newstate = advance(grammar.graminfo, toset.state, lookahead)
       let newstateno = if isempty.newstate then 0 else valueofencoding.encode.state.newstate  
       acc+shift(stateno, lookahead, newstateno)
        closestate(graminfo, stateno + 1, newresult)
      


Function generatereduce(grammarandact:seq.seq.seq.word, alphabet:seq.word, attribute:seq.word)seq.word
 " &br  &br Function action(ruleno:int, input:seq.token." + attribute + ", R:reduction."
 + attribute
 + ")"
 + attribute
 + for e ∈ grammarandact, acc ="", i, , acc + reduceline(e, i, length.grammarandact);
 + " &p function rulelength:T seq.int ["
 + for @e ∈ grammarandact, acc ="",,, list(acc,",", [ toword(length.@e_1 - 1)]);
 + "] &p function leftside:T seq.int ["
 + for @e ∈ grammarandact, acc ="",,, list(acc,",", [ toword.findindex(@e_1_1, alphabet)]);
 + ']'

function reduceline(grammerandact:seq.seq.word, i:int,last:int)seq.word
 let s = grammerandact 
 let prefix = if i = 1 then" &br if"else if i = last then" &br else assert"else" &br else if"
 let part2 ="ruleno = \\" + s_1 + "\\" + toword.i
 + if i = last then ' report"invalid rule number"+ toword.ruleno  &br ' else"then"
  prefix + part2 + for w ∈ s_2, acc ="",,, acc + if w ∈ "let assert"then" &br" + w else [ w]
   
Function gentau2 seq.word \\ used to generater tau parser for Pass1 of the tau compiler. \\ lr1parser(taurules2, tauruleprec, taualphabet,"bindinfo")
 
function taualphabet seq.word".=():>]-for * comment, [_; is T if # then else let assert report ∧ ∨  $wordlist A E G F W P L I  FP NM D  B"

function tauruleprec seq.seq.word \\ list of rules and lookaheads. 
The position of the lookahead is noted. Rule reductions after are discard and rule the first rule listed 
before the position is used to reduce. \\
["(","T","T W", "W","NM","E NM","E E_E"
,"_","E W.E","E E * E","*","E-E","E E-E","-","E-E","E E > E","E E = E"
,"=",">","E E ∧ E","∧","E E ∨ E","∨",' E comment E ',"E A E ", "E assert E report D E",";","D E"]

function taurules2 seq.seq.seq.word [
[  ' G F # ', ' R_1 '] 
, [ ' F W NM(FP)T E ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W _(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W -(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W =(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W >(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W *(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W ∧(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W ∨(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W NM T E ', ' createfunc(R, input, place, tokentext.R_2, empty:seq.mytype, R_3, R_4)'] 
, [ ' F W NM is  P ', ' bindinfo(dict.R, empty:seq.symbol, types.R_4, "record"+ tokentext.R_2) 
'] 
, [ ' F T ', ' R_1 '] 
, [ ' FP P ', ' bindinfo(for @e ∈ types.R_1, acc = dict.R ,,, addparameter(acc, cardinality.dict.R, input, place, @e), empty:seq.symbol, types.R_1,"")'] 
, [ ' P T ', ' bindinfo(dict.R, empty:seq.symbol, [ addabstract(":"_1, gettype.R_1)],"")'] 
, [ ' P P, T ', ' bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ addabstract(":"_1, gettype.R_3)],"")'] 
, [ ' P W:T ', ' bindinfo(dict.R, empty:seq.symbol, [ addabstract((tokentext.R_1)_1, gettype.R_3)],"")'] 
, [ ' P P, W:T ', ' bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ addabstract((tokentext.R_3)_1, gettype.R_5)],"")'] 
, [ ' P comment W:T ', ' bindinfo(dict.R, empty:seq.symbol, [ addabstract((tokentext.R_2)_1, gettype.R_4)],"")'] 
, [ ' P P, comment W:T ', ' bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ addabstract((tokentext.R_4)_1, gettype.R_6)],"")'] 
, [ ' E NM ', ' let id = tokentext.R_1 let f = lookupbysig(dict.R, id, empty:seq.mytype, input, place)bindinfo(dict.R, [ f], [ resulttype.f],"")'] 
, [ ' E NM(L)', ' unaryop(R, input, place, tokentext.R_1, R_3)'] 
, [ ' E(E)', ' R_2 '] 
, [ ' E if E then E else D ', ' let thenpart = R_4 assert(types.R_2)_1 = mytype."boolean"report errormessage("cond of if must be boolean", input, place)assert types.R_4 = types.R_6 report errormessage("then and else types are different", input, place)let newcode = code.R_2 + [ Lit.2, Lit.3, Br]+ code.R_4 + Exit + code.R_6 + [ Exit, Block((types.R_4)_1, 3)]bindinfo(dict.R, newcode, types.thenpart,"")'] 
, [ ' E E_E ', ' opaction(R, input, place)'] 
, [ ' E-E ', ' unaryop(R, input, place, tokentext.R_1, R_2)'] 
, [ ' E W.E ', ' unaryop(R, input, place, tokentext.R_1, R_3)'] 
, [ ' E E * E ', ' opaction(R, input, place)'] 
, [ ' E E-E ', ' opaction(R, input, place)'] 
, [ ' E E = E ', ' opaction(R, input, place)'] 
, [ ' E E > E ', ' opaction(R, input, place)'] 
, [ ' E E ∧ E ', ' opaction(R, input, place)'] 
, [ ' E E ∨ E ', ' opaction(R, input, place)'] 
, [ ' L E ', ' R_1 '] 
, [ ' L L, E ', ' bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3,"")'] 
, [ ' E [ L]', ' let types = types.R_2 assert for @e ∈ types, acc = true ,,, acc ∧ types_1 = @e report errormessage("types do not match in build", input, place)bindinfo(dict.R, code.R_2 + Sequence(types_1, length.types), [ addabstract("seq"_1, types_1)],"")'] 
, [ ' A let W = D ', ' let e = R_4 let name = tokentext.R_2 assert isempty.lookup(dict.R, name, empty:seq.mytype)report errormessage("duplicate symbol:"+ name, input, place)let newdict = dict.R + Local(name,(types.e)_1)bindinfo(newdict, code.e + Define.name, types.e, tokentext.R_2)'] 
, [ ' E A E ', ' let name = tokentext.R_1 let f = lookup(dict.R, name, empty:seq.mytype)assert not.isempty.f report"internal error/could not find local symbol to delete from dict with name"+ name bindinfo(dict.R_1-f_1, code.R_1 + code.R_2, \\ +"SET"+ name, \\ types.R_2,"")'] 
, [ ' E assert E report D E ', ' assert(types.R_2)_1 = mytype."boolean"report errormessage("condition in assert must be boolean in:", input, place)assert(types.R_4)_1 = mytype."word seq"report errormessage("report in assert must be seq of word in:", input, place)let newcode = code.R_2 + [ Lit.2, Lit.3, Br]+ code.R_5 + Exit + code.R_4 + symbol("assert:T(word seq)", typerep.(types.R_5)_1 +"builtin", typerep.(types.R_5)_1)+ Exit + Block((types.R_5)_1, 3)bindinfo(dict.R, newcode, types.R_5,"")'] 
, [ ' E I ', ' bindlit.R '] 
, [ ' E I.I ', ' bindinfo(dict.R, [ Words(tokentext.R_1 +"."+ tokentext.R_3), symbol("makereal(word seq)","UTF8","real")], [ mytype."real"],"")'] 
, [ ' T W ', ' isdefined(R, input, place, mytype.tokentext.R_1)'] 
, [ ' T W.T ', ' isdefined(R, input, place, addabstract((tokentext.R_1)_1,(types.R_3)_1))'] 
, [ ' E $wordlist ', ' let s = tokentext.R_1 bindinfo(dict.R, [ Words.subseq(s, 2, length.s-1)], [ mytype."word seq"],"")'] 
, [ ' E comment E ', ' R_2 '] 
, [ ' NM W ', ' R_1 '] 
, [ ' NM W:T ', ' bindinfo(dict.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1 +":"+ print.(types.R_3)_1)'] 
,[ ' B for  W - E , W = E , W ,',' forpart1(first.tokentext.R_2, R_4, first.tokentext.R_6, R_8, first.tokentext.R_10, input, place) ']
,[ ' B for  W - E , W = E ,  , ','    forpart1(first.tokentext.R_2, R_4, first.tokentext.R_6, R_8, first."^", input, place) ']
 ,[ ' E , B   , D ' ,' forpart2( R_1, bindinfo(dict.R,[Litfalse],[mytype."boolean"],""),R_3, input, place) ']
, [ ' E , B E , D ', ' forpart2(R_1, R_2, R_4, input, place)']      
,[' D E ', ' R_1 ' ]
,[' D E ; ' ,' R_1 ' ] ]

Function gentaupretty seq.word \\ used to generater tau parser for Pass1 of the tau compiler. \\ lr1parser(tauprettyrules, tauruleprec, taualphabet,"attribute2")


function tauprettyrules seq.seq.seq.word \\ after generator grammar change %%% to & \\
[ 
[  ' G F # ', ' R_1 '] 
, [ ' F W NM(FP)T E ', ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'] 
, [ ' F W N(FP)T E ', ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'] 
, [ ' F W NM T E ', ' pretty.[ key.R_1, R_2, R_3, R_4]'] 
, [ ' F W NM is W P ', ' pretty.[ key.R_1, R_2, R_3, R_4, list.R_5]'] 
, [ ' F T ', ' \\ use \\ pretty.[ R_1]'] 
, [ ' FP P ', ' list.R_1 '] 
, [ ' P T ', ' R_1 '] 
, [ ' P P, T ', ' R_1 + R_3 '] 
, [ ' P W:T ', ' pretty.[ R_1, R_2, R_3]'] 
, [ ' P P, W:T ', ' R_1 + pretty.[ R_3, R_4, R_5]'] 
, [ ' P comment W:T ', ' pretty.[ R_1, R_2, R_3, R_4]'] 
, [ ' P P, comment W:T ', ' R_1 + pretty.[ R_3, R_4, R_5, R_6]'] 
, [ ' E NM ', ' R_1 '] 
, [ ' E NM(L)', ' if length.R_3 = 1 ∧ length.text.R_1 = 1 then wrap(3, R_1,".", R_3)else pretty.[ R_1, R_2, list.R_3, R_4]'] 
, [ ' E(E)', ' R_2 '] 
, [ ' E { E } ', ' R_2 '] 
, [ ' E if E then E else D ', ' if width.R_2 + width.R_4 + width.R_6 < 30 then pretty.[ R_1, R_2, key.R_3, R_4, key.R_5, R_6]else if width.R_2 + width.R_4 < 30 then pretty.[ R_1, R_2, key.R_3, R_4, elseblock.R_6]else pretty.[ R_1, R_2
, attribute."%%%keyword then %%%br", block.R_4, elseblock.R_6]'] 
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
, [ ' A let W = D ', ' pretty.[ R_1, R_2, R_3, R_4]'] 
, [ ' E A E ', ' checkpara(R_1, block("%%%br let assert", R_2))'] 
, [ ' E assert E report D E ', ' pretty.[ R_1, R_2, key.R_3, R_4, block("%%%br let assert", R_5)]'] 
, [ ' E I ', ' R_1 '] 
, [ ' E I.I ', ' pretty.[ R_1, R_2, R_3]'] 
, [ ' T W ', ' R_1 '] 
, [ ' T W.T ', ' pretty.[ R_1, R_2, R_3]'] 
, [ ' E $wordlist ', ' attribute2.[ prettyresult(0, length.text.R_1,"%%%{ literal"+ escapeformat.text.R_1 +"%%%}")]'] 
, [ ' E comment E ', ' let t ="%%%{ comment"+ escapeformat.text.R_1 +"%%%}"let t2 = if width.R_1 + width.R_2 > 30 ∧(text.R_2)_1 ≠"%%%br"_1 then t +"%%%br"else t pretty.[ attribute2.[ prettyresult(0, length.text.R_1, t2)], R_2]'] 
, [ ' N_', ' R_1 '] 
, [ ' N-', ' R_1 '] 
, [ ' N = ', ' R_1 '] 
, [ ' N > ', ' R_1 '] 
, [ ' N * ', ' R_1 '] 
, [ ' N ∧ ', ' R_1 '] 
, [ ' N ∨ ', ' R_1 '] 
, [ ' NM W ', ' R_1 '] 
, [ ' NM W:T ', ' pretty.[ R_1, R_2, R_3]'] 
, [ ' B for(W-E, W = E, W ', ' pretty.[ R_1, R_3, R_4, R_5, R_6, R_7, R_8, R_9, R_10, R_11]'] 
, [ ' B for(W-E, W = E ', ' pretty.[ R_1, R_3, R_4, R_5, R_6, R_7, R_8, R_9]'] 
, [ ' E B)E ', ' pretty.[ R_1, attribute.";", if width.R_1 < 30 then R_3 else block.R_3]'] 
, [ ' E B, E)E ', ' pretty.[ R_1, R_2, R_3, attribute.";", if width.R_1 + width.R_3 < 30 then R_5 else block.R_5]'] 
,[ ' B for  W - E , W = E , W ','  pretty.[R_1,R_2,R_3,R_4,R_5,R_6,R_7,R_8,R_9,R_10] ']
, [ ' B for W-E, W = E ', ' pretty.[ R_1, R_2, R_3, R_4, R_5, R_6, R_7, R_8]'] 
, [ ' E B ; D ', ' pretty.[ R_1, R_2, if width.R_1 < 30 then R_3 else block.R_3]'] 
, [ ' E B, E ; D ', ' pretty.[ R_1, R_2, R_3, R_4, if width.R_1 + width.R_3 < 30 then R_5 else block.R_5]'] 
,[' D E ', ' R_1 ' ]
, [ ' D E ; ', ' R_1 ']]
 
 
Function test11 seq.word extractgrammer.'
Function action(ruleno:int, input:seq.word, place:int, R:reduction.attribute2)attribute2
 if ruleno = \\ G F # \\ 1 then R_1
 else if ruleno = \\ F W NM(FP)T E \\ 2 then
 pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]
 else if ruleno = \\ F W N(FP)T E \\ 3 then
 pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]
 else if ruleno = \\ F W NM T E \\ 4 then
 pretty.[ key.R_1, R_2, R_3, R_4]
 else if ruleno = \\ F W NM is W P \\ 5 then
 pretty.[ key.R_1, R_2, R_3, R_4, list.R_5]
 else if ruleno = \\ F T \\ 6 then \\ use \\ pretty.[ R_1]
 else if ruleno = \\ FP P \\ 7 then list.R_1
 else if ruleno = \\ P T \\ 8 then R_1
 else if ruleno = \\ P P, T \\ 9 then R_1 + R_3
 else if ruleno = \\ P W:T \\ 10 then pretty.[ R_1, R_2, R_3]
 else if ruleno = \\ P P, W:T \\ 11 then
 R_1 + pretty.[ R_3, R_4, R_5]
 else if ruleno = \\ P comment W:T \\ 12 then pretty.[ R_1, R_2, R_3, R_4]
 else if ruleno = \\ P P, comment W:T \\ 13 then
 R_1 + pretty.[ R_3, R_4, R_5, R_6]
 else if ruleno = \\ E NM \\ 14 then R_1
 else if ruleno = \\ E NM(L)\\ 15 then
 if length.R_3 = 1 ∧ length.text.R_1 = 1 then
  wrap(3, R_1,".", R_3)
  else pretty.[ R_1, R_2, list.R_3, R_4]
 else if ruleno = \\ E(E)\\ 16 then R_2
 else if ruleno = \\ E { E } \\ 17 then R_2
 else if ruleno = \\ E if E then E else E \\ 18 then
 if width.R_2 + width.R_4 + width.R_6 < 30 then
  pretty.[ R_1, R_2, key.R_3, R_4, key.R_5, R_6]
  else if width.R_2 + width.R_4 < 30 then
  pretty.[ R_1, R_2, key.R_3, R_4, elseblock.R_6]
  else pretty.[ R_1, R_2, attribute." &keyword then  &br", block.R_4, elseblock.R_6]
 else if ruleno = \\ E E_E \\ 19 then wrap(1, R_1, text.R_2, R_3)
 else if ruleno = \\ E-E \\ 20 then unaryminus.R_2
 else if ruleno = \\ E W.E \\ 21 then wrap(3, R_1, text.R_2, R_3)
 else if ruleno = \\ E E * E \\ 22 then wrap(4, R_1, text.R_2, R_3)
 else if ruleno = \\ E E-E \\ 23 then wrap(5, R_1, text.R_2, R_3)
 else if ruleno = \\ E E = E \\ 24 then wrap(6, R_1, text.R_2, R_3)
 else if ruleno = \\ E E > E \\ 25 then wrap(7, R_1, text.R_2, R_3)
 else if ruleno = \\ E E ∧ E \\ 26 then wrap(8, R_1, text.R_2, R_3)
 else if ruleno = \\ E E ∨ E \\ 27 then wrap(9, R_1, text.R_2, R_3)
 else if ruleno = \\ L E \\ 28 then R_1
 else if ruleno = \\ L L, E \\ 29 then R_1 + R_3
 else if ruleno = \\ E [ L]\\ 30 then pretty.[ R_1, list.R_2, R_3]
 else if ruleno = \\ A let W = E \\ 31 then pretty.[ R_1, R_2, R_3, R_4]
 else if ruleno = \\ E A E \\ 32 then checkpara(R_1, block(" &br let assert", R_2))
 else if ruleno = \\ E assert E report E E \\ 33 then
 pretty.[ R_1, R_2, key.R_3, R_4, block(" &br let assert", R_5)]
 else if ruleno = \\ E I \\ 34 then R_1
 else if ruleno = \\ E I.I \\ 35 then pretty.[ R_1, R_2, R_3]
 else if ruleno = \\ T W \\ 36 then R_1
 else if ruleno = \\ T W.T \\ 37 then pretty.[ R_1, R_2, R_3]
 else if ruleno = \\ E $wordlist \\ 38 then
 attribute2.[ prettyresult(0, length.text.R_1," &{ literal" + escapeformat.text.R_1 + " &}")]
 else if ruleno = \\ E comment E \\ 39 then
 let t =" &{ comment \\" + escapeformat.text.R_1 << 1 >> 1 + "\\  &}"
  let t2 = if width.R_1 + width.R_2 > 30
  ∧ (text.R_2)_1 ≠ " &br"_1 then
  t + " &br"
  else t
   pretty.[ attribute2.[ prettyresult(0, length.text.R_1, t2)], R_2]
 else if ruleno = \\ N_\\ 40 then R_1
 else if ruleno = \\ N-\\ 41 then R_1
 else if ruleno = \\ N = \\ 42 then R_1
 else if ruleno = \\ N > \\ 43 then R_1
 else if ruleno = \\ N * \\ 44 then R_1
 else if ruleno = \\ N ∧ \\ 45 then R_1
 else if ruleno = \\ N ∨ \\ 46 then R_1
 else if ruleno = \\ NM W \\ 47 then R_1
 else if ruleno = \\ NM W:T \\ 48 then pretty.[ R_1, R_2, R_3]
 else if ruleno = \\ B for(W-E, W = E, W \\ 49 then
 pretty.[ R_1, R_3, R_4, R_5, R_6, R_7, R_8, R_9, R_10, R_11]
 else if ruleno = \\ B for(W-E, W = E \\ 50 then
 pretty.[ R_1, R_3, R_4, R_5, R_6, R_7, R_8, R_9]
 else if ruleno = \\ E B)E \\ 51 then
 pretty.[ R_1, attribute.";", if width.R_1 < 30 then R_3 else block.R_3]
 else if ruleno = \\ E B, E)E \\ 52 then
 pretty.[ R_1, R_2, R_3, attribute.";", if width.R_1 + width.R_3 < 30 then R_5 else block.R_5]
 else if ruleno = \\ B for W-E, W = E, W \\ 53 then
 pretty.[ R_1, R_2, R_3, R_4, R_5, R_6, R_7, R_8, R_9, R_10]
 else if ruleno = \\ B for W-E, W = E \\ 54 then
 pretty.[ R_1, R_2, R_3, R_4, R_5, R_6, R_7, R_8]
 else if ruleno = \\ E B ; D \\ 55 then
 pretty.[ R_1, R_2, if width.R_1 < 30 then R_3 else block.R_3]
 else if ruleno = \\ E B, E ; D \\ 56 then
 pretty.[ R_1, R_2, R_3, R_4, if width.R_1 + width.R_3 < 30 then R_5 else block.R_5]
 else if ruleno = \\ D E \\ 57 then R_1
 else
  assert ruleno = \\ D E ; \\ 58 report"invalid rule number" + toword.ruleno
   R_1
   '

Function extractgrammer(z:seq.word)seq.word \\ use to extract grammar and rules from action procedure generated by genLR1 \\ extractgrammer(z, 1,"BEGIN", 1,"")

function extractgrammer(z:seq.word, i:int, state:seq.word, mark:int, result:seq.word)seq.word
 if i > length.z then
 "[ '" + result + subseq(z, mark, i - 1) + "]]"
 else if z_i = "\\"_1 then
 if state = "BEGIN"then extractgrammer(z, i + 1,"INRULE", i + 1, result)
  else if state = "INRULE"then
  extractgrammer(z, i + 3,"INACTION", i + 3, result + "'" + subseq(z, mark, i - 1) + "', '")
  else extractgrammer(z, i + 1, state, mark, result)
 else if subseq(z, i, i + 4) ∈ ["else if ruleno = \\","else assert ruleno = \\"]then
 extractgrammer(z, i + 5,"INRULE", i + 5, result + subseq(z, mark, i - 1) + "'] &br, [")
 else extractgrammer(z, i + 1, state, mark, result)
 
 function taurules3 seq.seq.seq.word [
[  ' G F # ', ' R_1 '] 
, [ ' F W NM(FP)T E ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W _(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W -(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W =(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W >(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W *(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W ∧(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W ∨(FP)T E  ', ' createfunc(R, input, place, tokentext.R_2, types.R_4, R_6, R_7)'] 
, [ ' F W NM T E    ', ' createfunc(R, input, place, tokentext.R_2, empty:seq.mytype, R_3, R_4)'] 
, [ ' F W NM is P ', ' assert(tokentext.R_4)_1 ∈"record"report errormessage("Expected record or sequence after is in type definition got:"+ tokentext.R_4, input, place)bindinfo(dict.R, empty:seq.symbol, types.R_5, tokentext.R_4 + tokentext.R_2)'] 
, [ ' FP P ', ' bindinfo(for @e ∈ types.R_1, acc = dict.R ; addparameter(acc, cardinality.dict.R, input, place, @e), empty:seq.symbol, types.R_1,"")'] 
, [ ' T W ', ' isdefined(R, input, place, mytype.tokentext.R_1)'] 
, [ ' T W.T ', ' isdefined(R, input, place, addabstract((tokentext.R_1)_1,(types.R_3)_1))'] 
, [    '  T2  T ' , ' R_1 ']
, [    '  T2 W : T ' , ' R_1 ']
, [    '  T3 comment T2 ', ' R_1 ']
, [    '  P   P , T3  ' , ' R_1 ']
, [    '  P   T3   ' , ' R_1 ']
, [ ' E NM ', ' let id = tokentext.R_1 let f = lookupbysig(dict.R, id, empty:seq.mytype, input, place)bindinfo(dict.R, [ f], [ resulttype.f],"")'] 
, [ ' E NM(L)', ' unaryop(R, input, place, tokentext.R_1, R_3)'] 
, [ ' E(E)', ' R_2 ']  
, [ ' L E ', ' R_1 '] 
, [ ' L L, E ', ' bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3,"")'] 
, [ ' E [ L]', ' let types = types.R_2 assert for @e ∈ types, acc = true ,,, acc ∧ types_1 = @e report errormessage("types do not match in build", input, place)bindinfo(dict.R, code.R_2 + Sequence(types_1, length.types), [ addabstract("seq"_1, types_1)],"")'] 
, [ ' E I ', ' bindlit.R '] 
, [ ' E I.I ', ' bindinfo(dict.R, [ Words(tokentext.R_1 +"."+ tokentext.R_3), symbol("makereal(word seq)","UTF8","real")], [ mytype."real"],"")'] 
, [ ' NM W ', ' R_1 '] 
, [ ' NM W:T ', ' bindinfo(dict.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1 +":"+ print.(types.R_3)_1)'] 
, [ ' E $wordlist ', ' let s = tokentext.R_1 bindinfo(dict.R, [ Words.subseq(s, 2, length.s-1)], [ mytype."word seq"],"")'] 
, [ ' E if E then E else D ', ' let thenpart = R_4 assert(types.R_2)_1 = mytype."boolean"report errormessage("cond of if must be boolean", input, place)assert types.R_4 = types.R_6 report errormessage("then and else types are different", input, place)let newcode = code.R_2 + [ Lit.2, Lit.3, Br]+ code.R_4 + Exit + code.R_6 + [ Exit, Block((types.R_4)_1, 3)]bindinfo(dict.R, newcode, types.thenpart,"")'] 
,[' D E ', ' R_1 ' ]
,[' D E ; ' ,' R_1 ' ] ]

, [ ' E E_E ', ' opaction(R, input, place)'] 
, [ ' E-E ', ' unaryop(R, input, place, tokentext.R_1, R_2)'] 
, [ ' E W.E ', ' unaryop(R, input, place, tokentext.R_1, R_3)'] 
, [ ' E E * E ', ' opaction(R, input, place)'] 
, [ ' E E-E ', ' opaction(R, input, place)'] 
, [ ' E E = E ', ' opaction(R, input, place)'] 
, [ ' E E > E ', ' opaction(R, input, place)'] 
, [ ' E E ∧ E ', ' opaction(R, input, place)'] 
, [ ' E E ∨ E ', ' opaction(R, input, place)'] 
, [ ' E comment E ', ' R_2 '] 
, [ ' A let W = D ', ' let e = R_4 let name = tokentext.R_2 assert isempty.lookup(dict.R, name, empty:seq.mytype)report errormessage("duplicate symbol:"+ name, input, place)let newdict = dict.R + Local(name,(types.e)_1)bindinfo(newdict, code.e + Define.name, types.e, tokentext.R_2)'] 
, [ ' E A E ', ' let name = tokentext.R_1 let f = lookup(dict.R, name, empty:seq.mytype)assert not.isempty.f report"internal error/could not find local symbol to delete from dict with name"+ name bindinfo(dict.R_1-f_1, code.R_1 + code.R_2, \\ +"SET"+ name, \\ types.R_2,"")'] 
, [ ' E assert E report D E ', ' assert(types.R_2)_1 = mytype."boolean"report errormessage("condition in assert must be boolean in:", input, place)assert(types.R_4)_1 = mytype."word seq"report errormessage("report in assert must be seq of word in:", input, place)let newcode = code.R_2 + [ Lit.2, Lit.3, Br]+ code.R_5 + Exit + code.R_4 + symbol("assert:T(word seq)", typerep.(types.R_5)_1 +"builtin", typerep.(types.R_5)_1)+ Exit + Block((types.R_5)_1, 3)bindinfo(dict.R, newcode, types.R_5,"")'] 
,[ ' B for  W - E , W = E , W ,',' forpart1(first.tokentext.R_2, R_4, first.tokentext.R_6, R_8, first.tokentext.R_10, input, place) ']
,[ ' B for  W - E , W = E ,   ,','    forpart1(first.tokentext.R_2, R_4, first.tokentext.R_6, R_8, first."^", input, place) ']
,  [ ' E B , , D ' ,' forpart2( R_1, bindinfo(dict.R,[Litfalse],[mytype."boolean"],""),R_3, input, place) ']
, [ ' E B, E , D ', ' forpart2(R_1, R_3, R_5, input, place)']      
]

Function gentau3 seq.word 
lr1parser(taurules3, tauruleprec3, taualphabet,"bindinfo")

function tauruleprec3 seq.seq.word \\ list of rules and lookaheads. The position of the lookahead is noted. Rule reductions after are discard and rule the first rule listed before the position is used to reduce. \\
["."]

,":",",","(","T","W","NM","N","$wordlist","E E_E"
,"_","E W.E","E E * E","*","E-E","E E-E","-","E-E","E E > E","E E = E"
,"=",">","E E ∧ E","∧","E E ∨ E","∨"]