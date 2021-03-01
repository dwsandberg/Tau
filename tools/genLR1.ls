#!/usr/local/bin/tau ; use genLR1 ;  gentau2

Module genLR1

/run genLR1 test11

/run genLR1 gentau2

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

function assignencoding(l:int, a:state)int l + 1

function =(a:action, b:action)boolean lookahead.a = lookahead.b ∧ stateno.a = stateno.b

function ?(a:action, b:action)ordering lookahead.a ? lookahead.b ∧ stateno.a ? stateno.b

type action2 is toaction:action

function ?(a1:action2, b1:action2)ordering 
 let a = toaction.a1
 let b = toaction.b1
  stateno.a ? stateno.b ∧ codedaction.a ? codedaction.b ∧ lookahead.a ? lookahead.b

function print(a:action)seq.word
 " &br state:" + toword.stateno.a + "lookahead:" + lookahead.a
 + if codedaction.a < 0 then"reduce" + toword.-codedaction.a
 else"shift" + toword.codedaction.a
 
function print(grammar:seq.seq.word, actions:seq.action)seq.word 
 let d = sort.for b = empty:seq.action2, a = actions do b + action2.a end(b)
 let c = for b = empty:seq.action, a = d do b + toaction.a end(b)
print(grammar, c, 1,-1, 0,"")

function print (grammar:seq.seq.word,a:seq.action,i:int,laststate:int,lastaction:int,result:seq.word) seq.word
 if i > length.a then result
 else
 let this=a_i
  let p1 = if laststate ≠ stateno.this then
  if laststate > 0 then print.decode.to:encoding.state(laststate)else"" fi
   + " &br state:"
   + toword.stateno.this
  else""
  let p2 = if lastaction ≠ codedaction.this then
  if codedaction.this < 0 then"reduce" + grammar_(-codedaction.this) + ";"
    else "shift"+toword.codedaction.this
     else ""
    print(grammar,a,i+1,stateno.this,codedaction.this,result+p1+p2+lookahead.this)
    
function hash(s:state)int hash.(toseq.toset.s)_1
 
/function print(a:seq.arc.word)seq.word for arc &in a, b ="",,, b + tail.arc + head.arc
   
function follow(grammar:seq.seq.word)graph.word
 let allarcs = for acc = empty:seq.arc.word, rule = grammar do 
 acc
 + for arcs = empty:seq.arc.word, i = 1, e = rule do 
   next(if i > 2 then arcs + arc(rule_(i - 1), rule_i)else arcs , i + 1)
  end(arcs)
 end(acc)
  follow(newgraph.allarcs, grammar)

function follow(g:graph.word, grammar:seq.seq.word)graph.word
 let g2 = for newgraph = g, rule = grammar do
  let a = for acc = empty:seq.arc.word, succ = toseq.successors(g, rule_1)do
   acc + arc(last.rule, succ)
  end(acc)
  newgraph
   + for acc = a, pred = toseq.predecessors(g, rule_1)do acc + arc(pred, rule_2)end(acc)
 end(newgraph)
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
 + for acc ="", @e = rules.p do list(acc,"&br |", grammar_@e)end(acc)
        
function =(a:ruleprec,b:ruleprec) boolean  lookahead.a=lookahead.b 
   
function print(a:seq.seq.word)seq.word
 for acc ="", @e = a do list(acc," &br", @e)end(acc)

function print(p:dottedrule)seq.word
 subseq(rule.p, 1, place.p - 1) + "'"
 + subseq(rule.p, place.p, length.rule.p)

function print(s:state)seq.word
 '  &br '
 + for acc ="", dotrule = toseq.toset.s do list(acc,"&br |", print.dotrule)end(acc)

Function initialstate(grammar:seq.seq.word)set.dottedrule close2(grammar, asset.[ dottedrule(2,"G F #")])

Function finalstate(grammar:seq.seq.word)set.dottedrule close2(grammar, asset.[ dottedrule(3,"G F #")])

function close2(g:seq.seq.word, s:set.dottedrule)set.dottedrule
 let newset = for acc = s, dotrule = toseq.s do acc ∪ close(g, dotrule)end(acc)
  if s = newset then s else close2(g, newset)

function close(grammar:seq.seq.word, p:dottedrule)set.dottedrule
 if place.p > length.rule.p then empty:set.dottedrule
 else
  asset.for acc = empty:seq.dottedrule, rule = grammar do
   if rule_1 = (rule.p)_(place.p)then acc + dottedrule(2, rule)else acc
  end(acc)
 
function advance(g:seq.seq.word, state:set.dottedrule, next:word)set.dottedrule
 close2(g, asset.for acc = empty:seq.dottedrule, p = toseq.state do
  if place.p ≤ length.rule.p ∧ (rule.p)_(place.p) = next then
  acc+ dottedrule(place.p + 1, rule.p) 
 else acc
 end(acc))
  

function finished(s:state)seq.seq.word
 for acc = empty:seq.seq.word, p = toseq.toset.s do
  acc
 + if place.p = length.rule.p + 1 then [ rule.p]else empty:seq.seq.word
 end(acc)

function shifts(s:state)seq.word
 toseq.asset.for acc = empty:seq.word, p = toseq.toset.s do
  acc
 + if place.p = length.rule.p + 1 then empty:seq.word else [(rule.p)_(place.p)]
 end(acc)
 
 
function resolveamb(ruleprec:seq.seq.word,grammar:seq.seq.word,dup:seq.action) seq.action
    if length.dup=1 then dup else 
     if   length.dup &ge 2 &and codedaction.dup_1 < 0 &and  codedaction.dup_2 < 0 then
       \\ contains reduce reduce conflict \\
         let rule1=grammar_-(codedaction.dup_1)
         let rule2=grammar_-(codedaction.dup_2)
   let reducepos1=  for r=0,i=1,p = ruleprec while r = 0  do  
           next( if length.p > 1 &and p=rule1 then i else 0 ,i+1)
            end(r)
       let reducepos2=  for r=0,i=1,p = ruleprec while r = 0 do  
           next( if length.p > 1 &and p=rule2 then i else 0 ,i+1)
            end(r)
       if reducepos1 = 0 &and reducepos2 = 0 then dup
       else 
       resolveamb(ruleprec,grammar,
       if between(reducepos1, 1,reducepos2) then   [dup_1] + dup << 2  else    dup << 1 )
    else if length.dup = 2 &and codedaction.dup_1 < 0 &and  codedaction.dup_2 > 0 then
      let rule1=grammar_-(codedaction.dup_1)
      let shiftpos=   for r=0,i=1,p = ruleprec while r = 0  do  
   next(if length.p=1 &and p_1=lookahead.dup_2 then i else 0 ,i+1)
     end (r)
    let reducepos=  for r=0,i=1,p = ruleprec while  r = 0 do  
           next( if length.p > 1 &and p=rule1 then i else 0 ,i+1)
            end(r)
       if between(reducepos, 1,shiftpos) then  \\ choose reduce \\ [dup_1]
   else if between(shiftpos, 1, reducepos)then \\ choose shift \\ [ dup_2]else dup
      else dup
            
Function lr1parser(grammarandact:seq.seq.seq.word, ruleprec:seq.seq.word, terminals:seq.word, attributename:seq.word)seq.word
 let grammar2 = for acc = empty:seq.seq.word, @e = grammarandact do acc + first.@e end(acc)
 let nontermials = for acc = empty:set.word, rule = grammar2 do acc + first.rule end(acc)
  assert isempty(asset.terminals ∩ nontermials)report"terminals and nontermials sets must be distinct"
 let alphabet=terminals +toseq.nontermials 
 let initialstateno = valueofencoding.encode.state.initialstate.grammar2
 let finalstateno=valueofencoding.encode.state.finalstate.grammar2  
  let symbolsused = for acc = empty:set.word, rule = grammar2 do acc ∪ asset.rule end(acc)
 let missingsymbols = symbolsused - asset.alphabet  
 assert isempty(symbolsused - asset.alphabet ) report"Symbols not included in alphabet"+ toseq(symbolsused - asset.alphabet  )
 assert  isempty( asset.alphabet - symbolsused ) report"Symbols in alphabet but not used"+ toseq( asset.alphabet - symbolsused  ) 
           let k = for problems ="", item = ruleprec do
            problems
    + if length.item = 1 ∧ item_1 ∉ alphabet then
    "lookahead" + item + "is not in alphabet"
    else if length.item > 1 ∧ item ∉ grammar2 then"rule is not in grammar:" + item else""
    end(problems)
 assert isempty.k report "ruleprec problem"+k
  let graminfo = grammarinfo(grammar2, follow.grammar2, ruleprec)
  let actions = closestate(graminfo, 1, empty:seq.action,asset.terminals )
   \\ assert false report print(grammar2, actions)\\
    let dups=dups.actions 
      let actions2 = for acc = empty:seq.seq.action, @e = dups.actions do acc + resolveamb(ruleprec, grammar2, @e)end(acc)
      let actions3 = for acc = empty:seq.action, @e = actions2 do acc + @e end(acc)
      let amb = for acc ="", @e = actions2
      do acc + if length.@e > 1 then" &br >>>>" + print(grammar2, @e)else empty:seq.word
      end(acc)
    if length.amb > 0 then
    "ambiguous actions:" + amb + " &br prec rules"
        + for acc ="", @e = ruleprec do acc + "|" + @e end(acc)
    else"" fi
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
       let x = for table = sparseseq.0, @e = actions3 do replaceS(table, findindex(lookahead.@e, alphabet) + length.alphabet * stateno.@e, [ codedaction.@e])end(table)
      " &p function actiontable:T seq.int ["
         + for acc ="", @e = x do list(acc,",", [ toword.@e])end(acc)
   + "]" 
    else"" fi
   + " &p follow"
    + print.follow.graminfo
   
function print(a:graph.word)seq.word
 for acc ="nodes", node = toseq.nodes.a do acc + " &br" + node + "followed by:" + toseq.successors(a, node)end(acc)

function dups(s:seq.action)seq.seq.action
 if isempty.s then empty:seq.seq.action else dups(1, sort.s, 1, empty:seq.seq.action)
   
function dups(  startofrun:int,s:seq.action,i:int,result:seq.seq.action  ) seq.seq.action
 if i > length.s then result + subseq(s, startofrun, i)
    else   if s_startofrun=s_i then dups(startofrun,s,i+1,result)
 else dups(i, s, i + 1, result + subseq(s, startofrun, i - 1))

function closestate(graminfo:grammarinfo, stateno:int, result:seq.action,alphabet:set.word)seq.action
 let m = encoding:seq.encodingpair.state
  if stateno > length.m then result
  else
   let state = data.m_stateno
   let reductions = finished.state
   let reduceActions = for acc = empty:seq.action, rule = reductions
   do acc
   + for acc2 = empty:seq.action, lookahead = toseq(successors(follow.graminfo, first.rule) ∩ alphabet)do acc2 + reduce(stateno, lookahead, ruleno(grammar.graminfo, rule))end(acc2)
   end(acc)
   let newresult = for acc = result + reduceActions, lookahead = toseq.asset.shifts.state
   do
        let newstate = advance(grammar.graminfo, toset.state, lookahead)
       let newstateno = if isempty.newstate then 0 else valueofencoding.encode.state.newstate  
    acc + shift(stateno, lookahead, newstateno)
   end(acc)
        closestate(graminfo, stateno + 1, newresult,alphabet)
      
Function generatereduce(grammarandact:seq.seq.seq.word, alphabet:seq.word, attribute:seq.word)seq.word
 " &br  &br Function action(ruleno:int, input:seq.token." + attribute + ", R:reduction."
 + attribute
 + ")"
 + attribute
 + for acc ="", i = 1, e = grammarandact do next(acc + reduceline(e, i, length.grammarandact), i + 1)end(acc)
 + " &p function rulelength:T seq.int ["
 + for acc ="", @e = grammarandact do list(acc,",", [ toword(length.@e_1 - 1)])end(acc)
 + "] &p function leftside:T seq.int ["
 + for acc ="", @e = grammarandact do list(acc,",", [ toword.findindex(@e_1_1, alphabet)])end(acc)
 + ']'

function reduceline(grammerandact:seq.seq.word, i:int,last:int)seq.word
 let s = grammerandact 
 let prefix = if i = 1 then" &br if"else if i = last then" &br else assert"else" &br else if"
 let part2 ="ruleno = \\" + s_1 + "\\" + toword.i
 + if i = last then ' report"invalid rule number"+ toword.ruleno  &br ' else"then"
  prefix + part2
  + for acc ="", w = s_2 do acc + if w ∈ "let assert"then" &br" + w else [ w]end(acc)
   
Function gentau2 seq.word \\ used to generater tau parser for Pass1 of the tau compiler. \\ lr1parser(taurules2, tauruleprec, taualphabet,"bindinfo")
 
function taualphabet seq.word".=():>]-for * comment, [_fi is I if # then else let assert report ∧ ∨ $wordlist  while end   W  do   "


function tauruleprec seq.seq.word \\ list of rules and lookaheads. 
The position of the lookahead is noted. Rule reductions after are discard and rule the first rule listed 
before the position is used to reduce. \\ \\ [""] \\
["(","E NM","E E_E","_","E W.E","E E * E","E-E","*","E E-E","-","E E > E","E E = E"
,"=",">","E E ∧ E","∧","E E ∨ E","∨" 
]+["end","fi","E if E then E else E",  ' E comment E ', "E assert E report D E","A  W = E","E let A E","D E"    ]

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
, [ ' FP P ', '  bindinfo(for acc = dict.R, @e = types.R_1 do addparameter(acc, cardinality.dict.R, input, place, @e)end(acc), empty:seq.symbol, types.R_1,"")'] 
, [ ' P T ', ' bindinfo(dict.R, empty:seq.symbol, [ addabstract(":"_1, gettype.R_1)],"")'] 
, [ ' P P, T ', ' bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ addabstract(":"_1, gettype.R_3)],"")'] 
, [ ' P W:T ', ' bindinfo(dict.R, empty:seq.symbol, [ addabstract((tokentext.R_1)_1, gettype.R_3)],"")'] 
, [ ' P P, W:T ', ' bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ addabstract((tokentext.R_3)_1, gettype.R_5)],"")'] 
, [ ' P comment W:T ', ' bindinfo(dict.R, empty:seq.symbol, [ addabstract((tokentext.R_2)_1, gettype.R_4)],"")'] 
, [ ' P P, comment W:T ', ' bindinfo(dict.R, empty:seq.symbol, types.R_1 + [ addabstract((tokentext.R_4)_1, gettype.R_6)],"")'] 
, [ ' E NM ', ' let id = tokentext.R_1 let f = lookupbysig(dict.R, id, empty:seq.mytype, input, place)bindinfo(dict.R, [ f], [ resulttype.f],"")'] 
, [ ' E NM(L)', ' unaryop(R, input, place, tokentext.R_1, R_3)'] 
, [ ' E(E)', ' R_2 '] 
, [ ' E if E then E else E ', ' let thenpart = R_4 assert(types.R_2)_1 = mytype."boolean"report errormessage("cond of if must be boolean", input, place)assert types.R_4 = types.R_6 report errormessage("then and else types are different", input, place)let newcode = code.R_2 + [ Lit.2, Lit.3, Br]+ code.R_4 + Exit + code.R_6 + [ Exit, Block((types.R_4)_1, 3)]bindinfo(dict.R, newcode, types.thenpart,"")'] 
, [ ' E if E then E else E fi ', ' let thenpart = R_4 assert(types.R_2)_1 = mytype."boolean"report errormessage("cond of if must be boolean", input, place)assert types.R_4 = types.R_6 report errormessage("then and else types are different", input, place)let newcode = code.R_2 + [ Lit.2, Lit.3, Br]+ code.R_4 + Exit + code.R_6 + [ Exit, Block((types.R_4)_1, 3)]bindinfo(dict.R, newcode, types.thenpart,"")'] 
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
, [ ' E [ L]', ' let types = types.R_2 
  assert for acc = true, @e = types do acc ∧ types_1 = @e end(acc)report errormessage("types do not match in build", input, place) bindinfo(dict.R, code.R_2 + Sequence(types_1, length.types), [ addabstract("seq"_1, types_1)],"")
'] 
, [ ' A  W = E ', ' let name = tokentext.R_1 
assert isempty.lookup(dict.R, name, empty:seq.mytype)report errormessage("duplicate symbol:"+ name, input, place) 
let newdict = dict.R + Local(name,(types.R_3 )_1)bindinfo(newdict, code.R_3 + Define.name , types.R_3, name) 
'] 
, [ ' E let A E ', '  bindinfo(dict.R_1, code.R_2  +code.R_3, types.R_3,"") '] 
, [ ' E assert E report D E ', ' assert(types.R_2)_1 = mytype."boolean"report errormessage("condition in assert must be boolean in:", input, place)assert(types.R_4)_1 = mytype."word seq"report errormessage("report in assert must be seq of word in:", input, place)let newcode = code.R_2 + [ Lit.2, Lit.3, Br]+ code.R_5 + Exit + code.R_4 + symbol("assert:T(word seq)", typerep.(types.R_5)_1 +"builtin", typerep.(types.R_5)_1)+ Exit + Block((types.R_5)_1, 3)bindinfo(dict.R, newcode, types.R_5,"")'] 
, [ ' E I ', ' bindlit.R '] 
, [ ' E I.I ', ' bindinfo(dict.R, [ Words(tokentext.R_1 +"."+ tokentext.R_3), symbol("makereal(word seq)","UTF8","real")], [ mytype."real"],"")'] 
, [ ' T W ', ' isdefined(R, input, place, mytype.tokentext.R_1)'] 
, [ ' T W.T ', ' isdefined(R, input, place, addabstract((tokentext.R_1)_1,(types.R_3)_1))'] 
, [ ' E $wordlist ', ' let s = tokentext.R_1 bindinfo(dict.R, [ Words.subseq(s, 2, length.s-1)], [ mytype."word seq"],"")'] 
, [ ' E comment E ', ' R_2 '] 
, [ ' NM W ', ' R_1 '] 
, [ ' NM W:T ', ' bindinfo(dict.R, empty:seq.symbol, empty:seq.mytype, tokentext.R_1 +":"+ print.(types.R_3)_1)'] 
, [ ' F1  W = E ',' let name = tokentext.R_1 
assert isempty.lookup(dict.R, name, empty:seq.mytype)report errormessage("duplicate symbol:"+ name, input, place) 
 bindinfo(dict.R_1, code.R_3  , types.R_3, name) 
' ] 
,[' F1  F1 , W = E ',' let name = tokentext.R_3 
assert isempty.lookup(dict.R, name, empty:seq.mytype)report errormessage("duplicate symbol:"+ name, input, place) 
  bindinfo(dict.R, code.R_1 +code.R_5, types.R_1+types.R_5,tokentext.R_1+tokentext.R_3)' ] 
,[ ' F2   F1    ',' forlocaldeclare(R_1,input, place)  ' ] 
,[ ' E  for  F2  do    E end (E)   ','  forbody(dict.R_1, R_2, R_4, R_1, R_7, input, place) ' ] 
,[ ' E  for  F2  while E  do   E   end (E)   ','  forbody(dict.R_1, R_2,  R_6,R_4, R_9,input, place) '] 
,[ ' D E ',"R_1"]
, [ ' E if E then E else E end if ', ' let thenpart = R_4 assert(types.R_2)_1 = mytype."boolean"report errormessage("cond of if must be boolean", input, place)assert types.R_4 = types.R_6 report errormessage("then and else types are different", input, place)let newcode = code.R_2 + [ Lit.2, Lit.3, Br]+ code.R_4 + Exit + code.R_6 + [ Exit, Block((types.R_4)_1, 3)]bindinfo(dict.R, newcode, types.thenpart,"")'] 
]



Function gentaupretty seq.word \\ used to generater tau parser for Pass1 of the tau compiler. \\ lr1parser(tauprettyrules, tauruleprec, taualphabet,"attribute2")


function tauprettyrules seq.seq.seq.word \\ after generator grammar change %%% to & \\
[ [ ' G F # ', ' R_1 '] 
, [ ' F W NM(FP)T E ', ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'] 
, [ ' F W_(FP)T E ', ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'] 
, [ ' F W-(FP)T E ', ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'] 
, [ ' F W =(FP)T E ', ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'] 
, [ ' F W >(FP)T E ', ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'] 
, [ ' F W *(FP)T E ', ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'] 
, [ ' F W ∧(FP)T E ', ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'] 
, [ ' F W ∨(FP)T E ', ' pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]'] 
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
, [ ' E NM(L)', ' if length.R_3 = 1 ∧ length.text.R_1 = 1 then wrap(3, R_1,".", R_3)else pretty.[ R_1, R_2, list.R_3, R_4]'] 
, [ ' E(E)', ' R_2 '] 
, [ ' E if E then E else D ', ' let x1 ="%%%keyword if"+ removeclose.text.R_2 +"%%%keyword then"let x = attribute(x1 + removeclose.text.R_4)let t = if width.R_2 + width.R_4 + width.R_6 < 30 then [ x, key.R_5, R_6]else if width.R_2 + width.R_4 < 30 then [ x, elseblock.R_6]else [ attribute(x1 + removeclose.text.block.R_4), elseblock.R_6]pretty(t + attribute.";")'] 
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
, [ ' E let A E ', ' \\ checkpara(pretty.[ R_1, R_2], block("%%%br let assert", R_3))\\ attribute("%%%keyword let"+ subseq(text.R_2, 1, 2)+ protect(text.R_2 << 2, text.block("%%%br let assert", R_3)))'] 
, [ ' E assert E report D E ', ' pretty.[ key.R_1, R_2, attribute("%%%keyword report"+ protect(text.R_4, text.block("%%%br let assert", R_5)))]'] 
, [ ' E I ', ' R_1 '] 
, [ ' E I.I ', ' pretty.[ R_1, R_2, R_3]'] 
, [ ' T W ', ' R_1 '] 
, [ ' T W.T ', ' pretty.[ R_1, R_2, R_3]'] 
, [ ' E $wordlist ', ' attribute2.[ prettyresult(0, length.text.R_1,"%%%{ literal"+ escapeformat.text.R_1 +"%%%}")]'] 
, [ ' E comment E ', ' let t ="%%%{ comment \\"+ escapeformat.text.R_1 << 1 >> 1 +"\\ %%%}"let t2 = if width.R_1 + width.R_2 > 30 ∧(text.R_2)_1 ≠"%%%br"_1 then t +"%%%br"else t pretty.[ attribute2.[ prettyresult(0, length.text.R_1, t2)], R_2]'] 
, [ ' NM W ', ' R_1 '] 
, [ ' NM W:T ', ' pretty.[ R_1, R_2, R_3]'] 
, [ ' F1 W = E ', ' pretty.[ R_1, R_2, R_3]'] 
, [ ' F1 F1, W = E ', ' pretty.[ R_1, R_2, R_3, R_4, R_5]'] 
, [ ' F2 F1 ', ' R_1 '] 
, [ ' E for F2 do E end(E)', ' if width.R_2 + width.R_4 < 30 then pretty.[ key.R_1, list.R_2, attribute("%%%keyword do"+ removeclose.text.R_4 +"%%%keyword end"), R_6, R_7, R_8]else pretty.[ key.R_1, list.R_2, attribute("%%%keyword do"+ removeclose.text.block.R_4 +"%%%br %%%keyword end"), R_6, R_7, R_8]'] 
, [ ' E for F2 while(E)E end(E)', ' toword.ruleno pretty.[ key.R_1, list.R_2, attribute("%%%keyword while("+ text.R_5 +")"+ removeclose.text.R_7 +"%%%keyword end"), R_9, R_10, R_11]']
  ]

 
 
Function test11 seq.word extractgrammer.'
Function action(ruleno:int, input:seq.word, place:int, R:reduction.attribute2)attribute2
 if ruleno = \\ G F # \\ 1 then R_1
 else if ruleno = \\ F W NM(FP)T E \\ 2 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]
 else if ruleno = \\ F W_(FP)T E \\ 3 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]
 else if ruleno = \\ F W-(FP)T E \\ 4 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]
 else if ruleno = \\ F W =(FP)T E \\ 5 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]
 else if ruleno = \\ F W >(FP)T E \\ 6 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]
 else if ruleno = \\ F W *(FP)T E \\ 7 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]
 else if ruleno = \\ F W ∧(FP)T E \\ 8 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]
 else if ruleno = \\ F W ∨(FP)T E \\ 9 then pretty.[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block.R_7 else R_7]
 else if ruleno = \\ F W NM T E \\ 10 then pretty.[ key.R_1, R_2, R_3, R_4]
 else if ruleno = \\ F W NM is P \\ 11 then pretty.[ key.R_1, R_2, R_3, list.R_4]
 else if ruleno = \\ F T \\ 12 then \\ use \\ pretty.[ R_1]
 else if ruleno = \\ FP P \\ 13 then list.R_1
 else if ruleno = \\ P T \\ 14 then R_1
 else if ruleno = \\ P P, T \\ 15 then R_1 + R_3
 else if ruleno = \\ P W:T \\ 16 then pretty.[ R_1, R_2, R_3]
 else if ruleno = \\ P P, W:T \\ 17 then R_1 + pretty.[ R_3, R_4, R_5]
 else if ruleno = \\ P comment W:T \\ 18 then pretty.[ R_1, R_2, R_3, R_4]
 else if ruleno = \\ P P, comment W:T \\ 19 then R_1 + pretty.[ R_3, R_4, R_5, R_6]
 else if ruleno = \\ E NM \\ 20 then R_1
 else if ruleno = \\ E NM(L)\\ 21 then if length.R_3 = 1 ∧ length.text.R_1 = 1 then wrap(3, R_1,".", R_3) else pretty.[ R_1, R_2, list.R_3, R_4]
 else if ruleno = \\ E(E)\\ 22 then R_2
 else if ruleno = \\ E if E then E else D \\ 23 then
    let x1="%%%keyword if "+  removeclose.text.R_2+"%%%keyword then "
    let x=  attribute(x1+ removeclose.text.R_4)
 let t = if width.R_2 + width.R_4 + width.R_6 < 30 then [ x, key.R_5, R_6]
 else if width.R_2 + width.R_4 < 30 then [ x, elseblock.R_6]
 else
  [ attribute( x1+ removeclose.text.block.R_4), elseblock.R_6]
  pretty(t + attribute.";")
 else if ruleno = \\ E E_E \\ 24 then wrap(1, R_1, text.R_2, R_3)
 else if ruleno = \\ E-E \\ 25 then unaryminus.R_2
 else if ruleno = \\ E W.E \\ 26 then wrap(3, R_1, text.R_2, R_3)
 else if ruleno = \\ E E * E \\ 27 then wrap(4, R_1, text.R_2, R_3)
 else if ruleno = \\ E E-E \\ 28 then wrap(5, R_1, text.R_2, R_3)
 else if ruleno = \\ E E = E \\ 29 then wrap(6, R_1, text.R_2, R_3)
 else if ruleno = \\ E E > E \\ 30 then wrap(7, R_1, text.R_2, R_3)
 else if ruleno = \\ E E ∧ E \\ 31 then wrap(8, R_1, text.R_2, R_3)
 else if ruleno = \\ E E ∨ E \\ 32 then wrap(9, R_1, text.R_2, R_3)
 else if ruleno = \\ L E \\ 33 then R_1
 else if ruleno = \\ L L, E \\ 34 then R_1 + R_3
 else if ruleno = \\ E [ L]\\ 35 then pretty.[ R_1, list.R_2, R_3]
 else if ruleno = \\ A W = E \\ 36 then pretty.[ R_1, R_2, R_3]
 else if ruleno = \\ E let A E \\ 37 then \\ checkpara(pretty.[ R_1, R_2], block("
%%%br let assert", R_3))\\
  attribute(" %%%keyword let" + subseq(text.R_2, 1, 2)
  + protect(text.R_2 << 2, text.block(" %%%br let assert", R_3)))
 else if ruleno = \\ E assert E report D E \\ 38 then
 pretty.[ key.R_1, R_2, attribute(" %%%keyword report" + protect(text.R_4, text.block(" %%%br let assert", R_5)))]
 else if ruleno = \\ E I \\ 39 then R_1
 else if ruleno = \\ E I.I \\ 40 then pretty.[ R_1, R_2, R_3]
 else if ruleno = \\ T W \\ 41 then R_1
 else if ruleno = \\ T W.T \\ 42 then pretty.[ R_1, R_2, R_3]
 else if ruleno = \\ E $wordlist \\ 43 then attribute2.[ prettyresult(0, length.text.R_1," %%%{ literal" + escapeformat.text.R_1 + " %%%}")]
 else if ruleno = \\ E comment E \\ 44 then
 let t =" %%%{ comment \\" + escapeformat.text.R_1 << 1 >> 1 + "\\  %%%}"
 let t2 = if width.R_1 + width.R_2 > 30
 ∧ (text.R_2)_1 ≠ " %%%br"_1 then
 t + " %%%br"
 else t
  pretty.[ attribute2.[ prettyresult(0, length.text.R_1, t2)], R_2]
 else if ruleno = \\ NM W \\ 45 then R_1
 else if ruleno = \\ NM W:T \\ 46 then pretty.[ R_1, R_2, R_3]
 else if ruleno = \\ D E \\ 51 then R_1
 else if ruleno = \\ D E ; \\ 52 then R_1
 else if ruleno = \\ F1 W = E \\ 53 then pretty.[ R_1, R_2, R_3]
 else if ruleno = \\ F1 F1, W = E \\ 54 then
 pretty.[ R_1, R_2, R_3, R_4, R_5]
 else if ruleno = \\ F2 F1 \\ 55 then R_1
 else if ruleno = \\ E for F2 do E end(E)\\ 56 then
 if width.R_2 + width.R_4 < 30 then
  pretty.[ key.R_1, list.R_2, attribute(" %%%keyword do" + removeclose.text.R_4 + " %%%keyword end"), R_6, R_7, R_8]
  else
   pretty.[ key.R_1, list.R_2, attribute(" %%%keyword do" + removeclose.text.block.R_4 + " %%%br  %%%keyword end"), R_6, R_7, R_8]
 else
  assert ruleno = \\ E for F2 while(E)E end(E)\\ 57 report"invalid rule number" + toword.ruleno
   pretty.[ key.R_1, list.R_2, attribute(" %%%keyword while(" + text.R_5 + ")" + removeclose.text.R_7
   + " %%%keyword end"), R_9, R_10, R_11]
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
 
 