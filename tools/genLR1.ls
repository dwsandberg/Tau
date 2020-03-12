#!/usr/local/bin/tau

Module genLR1

run genLR1 gentaupretty 

use blockseq.seq.dottedrule

use encoding.state

use graph.word

use otherseq.int

use otherseq.seq.word

use otherseq.word

use seq.action

use seq.arc.word

use seq.dottedrule

use seq.int

use seq.seq.seq.word

use seq.seq.word

use seq.set.dottedrule

use seq.state

use seq.word

use set.arc.word

use set.dottedrule

use set.word

use otherseq.int

use stdlib

type estate is encoding state

type state is record toset:set.dottedrule, index:int

function state(a:set.dottedrule)state state(a, 0)

type dottedrule is record place:int, rule:seq.word

Function addindex(d:state, i:int)state state(toset.d, i)

type action is record stateno:int, lookahead:word, codedaction:int

type grammarinfo is record grammar:seq.seq.word, follow:graph.word, ruleprec:seq.seq.word

function =(a:state, b:state)boolean toset.a = toset.b

function =(a:dottedrule, b:dottedrule)boolean rule.a = rule.b ∧ place.a = place.b

function ?(a:dottedrule, b:dottedrule)ordering rule.a ? rule.b ∧ place.a ? place.b

function hash(p:dottedrule)int hash.rule.p + place.p

function =(a:action, b:action)boolean lookahead.a = lookahead.b ∧ stateno.a = stateno.b

function hash(s:state)int hash.(toseq.toset.s)_1

function backarc(tail:word, head:word)arc.word arc(head, tail)

function follow1(s:seq.word, i:int)arc.word 
 assert i > 1 ∧ i < length.s report s + toword.i 
   arc(s_i, s_(i + 1))

function follow2(rule:seq.word)seq.arc.word 
 @(+, follow1(rule), empty:seq.arc.word, arithseq(length.rule - 2, 1, 2))

function follow(grammar:seq.seq.word)graph.word 
 follow(newgraph.@(+, follow2, empty:seq.arc.word, grammar), grammar)

function follow3(g:graph.word, rule:seq.word)seq.arc.word 
 let a = @(+, arc(last.rule), empty:seq.arc.word, toseq.successors(g, rule_1))
   @(+, backarc(rule_2), a, toseq.predecessors(g, rule_1))

function follow(g:graph.word, grammar:seq.seq.word)graph.word 
 let g2 = @(+, follow3(g), g, grammar)
   if g = g2 then g else follow(g2, grammar)

function ruleno(grammar:seq.seq.word, rule:seq.word)int 
 let ruleno = if rule =""then 0 else findindex(rule, grammar)
  assert ruleno ≤ length.grammar report"rule not found"+ rule 
   ruleno

function state(stateno:int)state if stateno = 0 then state.empty:set.dottedrule else(orderadded.estate)_stateno

function shift(stateno:int, lookahead:word, newstateno:int)action action(stateno, lookahead, newstateno)

function reduce(stateno:int, lookahead:word, ruleno:int)action action(stateno, lookahead,-ruleno)

function getaction(ruleprec:seq.seq.word, grammar:seq.seq.word, state:state, stateno:int, reductions:seq.seq.word, lookahead:word)action 
 let newstate = advance(grammar, toset.state, lookahead)
  let newstateno = if not.isempty.newstate then findindex(estate, state.newstate)else 0 
   if length.reductions = 0 ∧ newstateno ≠ 0 
    then shift(stateno, lookahead, newstateno)
    else if length.reductions = 1 ∧ newstateno = 0 
    then reduce(stateno, lookahead, ruleno(grammar, reductions_1))
    else 
     let lookplace = findindex([ lookahead], ruleprec)
     let yy = 
      if lookplace > length.ruleprec 
      then empty:seq.seq.word 
      else @(+, tosubstate(reductions), empty:seq.seq.word, subseq(ruleprec, 1, lookplace - 1))
      if length.yy = 1 
       then reduce(stateno, lookahead, ruleno(grammar, yy_1))
       else if length.yy = 0 ∧ newstateno ≠ 0 
       then shift(stateno, lookahead, newstateno)
       else 
        let r = if length.yy = 0 then reductions else yy 
         if length.r = 2 ∧ r_1 ="E-E"∧ r_2 ="E E-E"
          then // assert false report"<>"+ lookahead + toword.length.yy + print.r // reduce(stateno, lookahead, ruleno(grammar, r_2))
          else // ERROR ambiguous // action(stateno, lookahead, 0)

function print(a:seq.seq.word)seq.word @(seperator("&br"), identity,"", a)

function printstate(stateno:int)seq.word [ toword.stateno]

function alphabet(grammar:seq.seq.word)seq.word toseq.asset.@(+, identity,"", grammar)

function addaction(alphabet:seq.word, table:seq.int, a:action)seq.int 
 replace(table, findindex(lookahead.a, alphabet)+ length.alphabet * stateno.a, codedaction.a)

function first(a:seq.seq.word)seq.word a_1

function first(a:seq.word)word a_1

function tosubstate(state:seq.seq.word, rule:seq.word)seq.seq.word 
 if rule in state then [ rule]else empty:seq.seq.word

function print(p:dottedrule)seq.word 
 subseq(rule.p, 1, place.p - 1)+"'"+ subseq(rule.p, place.p, length.rule.p)

function print(s:state)seq.word 
 "&br &quot"+ @(seperator("|"), print,"", toseq.toset.s)+"&br &quot"

Function initialstate(grammar:seq.seq.word)set.dottedrule 
 close(grammar, asset.[ dottedrule(2,"G F #")])

function close(g:seq.seq.word, s:set.dottedrule)set.dottedrule 
 let newset = @(∪, close(g), s, toseq.s)
   if s = newset then s else close(g, newset)

function close(g:seq.seq.word, p:dottedrule)set.dottedrule 
 if place.p > length.rule.p then empty:set.dottedrule else asset.@(+, startswith((rule.p)_(place.p)), empty:seq.dottedrule, g)

function startswith(first:word, x:seq.word)seq.dottedrule 
 if x_1 = first then [ dottedrule(2, x)]else empty:seq.dottedrule

function advance(g:seq.seq.word, state:set.dottedrule, next:word)set.dottedrule 
 close(g, asset.@(+, advance(next), empty:seq.dottedrule, toseq.state))

function advance(next:word, p:dottedrule)seq.dottedrule 
 if place.p ≤ length.rule.p ∧(rule.p)_(place.p)= next then [ dottedrule(place.p + 1, rule.p)]else empty:seq.dottedrule

function finished(p:dottedrule)seq.seq.word if place.p = length.rule.p + 1 then [ rule.p]else empty:seq.seq.word

function finished(s:state)seq.seq.word @(+, finished, empty:seq.seq.word, toseq.toset.s)

function shifts(p:dottedrule)seq.word 
 if place.p = length.rule.p + 1 then empty:seq.word else [(rule.p)_(place.p)]

function shifts(s:state)seq.word toseq.asset.@(+, shifts, empty:seq.word, toseq.toset.s)

Function lr1parser(grammarandact:seq.seq.seq.word, ruleprec:seq.seq.word, alphabet:seq.word)seq.word 
 let grammar2 = @(+, first, empty:seq.seq.word, grammarandact)
  let initialstateno = findindex(estate, state.initialstate.grammar2)
  let missingsymbols = asset.alphabet - asset.alphabet.grammar2 
  assert isempty.missingsymbols report"Symbols not included in alphabet"+ toseq.missingsymbols 
   let graminfo = grammarinfo(grammar2, follow.grammar2, ruleprec)
    let actions = closestate(graminfo, 1, empty:seq.action)
    let amb = @(+, isambiguous,"", actions)
     (if length.amb > 0 then"ambiguous actions:"+ amb else"")
      + generatereduce(grammarandact, alphabet)
      +    "&br &br function tokenlist seq.word &quot"+ alphabet +"&quot"
      +"&br &br function startstate int"+ toword.initialstateno 
       +"&br &br noactions"+ toword.length.actions 
     +"&br nosymbols:"
     + toword.length.alphabet 
      +"&br norules"
     + toword.length.grammarandact 
     +"&br nostate"
     + toword.length.orderadded.estate       
       +"&br &br function actiontable seq.int ["
       + @(seperator(","), toword,"", @(addaction(alphabet), identity, dseq.0, actions))
       +"]"
         +"&br &br follow"
     + @(seperator("&br"), print,"", toseq.arcs.follow.graminfo)
       +"&br &br function printstate(stateno:int)seq.word &br ["
       + @(seperator(","), print,"", orderadded.estate)
       +"]_stateno"

function isambiguous(a:action)seq.word 
 if codedaction.a = 0 then"&br"+ toword.stateno.a + lookahead.a else""

function print(a:arc.word)seq.word [ tail.a]+">"+ head.a

function closestate(graminfo:grammarinfo, stateno:int, result:seq.action)seq.action 
 let m = orderadded.estate 
   if stateno > length.m 
    then result 
    else 
     let state = m_stateno 
     let reductions = finished.state 
     let follows = @(∪, successors(follow.graminfo), empty:set.word, @(+, first,"", reductions))
     let newresult = @(+ 
     , getaction(ruleprec.graminfo, grammar.graminfo, state, stateno, reductions)
     , result 
     , toseq(asset.shifts.state ∪ follows))
      closestate(graminfo, stateno + 1, newresult)

Function generatereduce(grammarandact:seq.seq.seq.word, alphabet:seq.word)seq.word 
 "function reduce(stk:stack.stkele, ruleno:int, place:int, input:seq.word)stack.stkele // generated function 
 // &br let rulelen = ["
 + @(seperator(","), rulelength,"", grammarandact)
 +"]_ruleno &br let newstk = pop(stk, rulelen)
 &br let R =reduction(top(stk, rulelen),input,place) 
  &br let newtree ="
 + @(+, reduceline(grammarandact),"", arithseq(length.grammarandact, 1, 1))
 +"&br let leftsidetoken = ["
 + @(seperator(","), leftside(alphabet),"", grammarandact)
 +"]_ruleno &br let actioncode = actiontable_(leftsidetoken + length.tokenlist * stateno.top.newstk)&br assert 
 actioncode > 0 report &quot ???? &quot &br push(newstk, stkele(actioncode, newtree))"

function rulelength(a:seq.seq.word)word toword(length.a_1 - 1)

function leftside(alphabet:seq.word, a:seq.seq.word)word toword.findindex(a_1_1, alphabet)

function replace$(w:word)seq.word if w ="let"_1 then"&br let"else [ w]

function reduceline(grammerandact:seq.seq.seq.word, i:int)seq.word 
 let s = grammerandact_i 
   if i = length.grammerandact 
    then"&br assert ruleno = //"+ s_1 +"//"+ toword.i +"report &quot invalid rule number &quot + toword.ruleno &br"
    + @(+, replace$,"", s_2)
    else"&br if ruleno = //"+ s_1 +"//"+ toword.i +"then"+   @(+, replace$,"", s_2)  
    +"else"

Function gentau2 seq.word 
 // used to generater tau parser for Pass1 of the tau compiler. // 
 lr1parser(taurules2 
 , tauruleprec 
 ,".=():>]-{ } comment, [_^is T if # then else let assert report ∧ ∨ * $wordlist @ A E G F W P N L I K FP")

function tauruleprec seq.seq.word 
 ["E E_E"
 ,"_"
 ,"E comment E"
 ,"E W.E"
 ,"E N.E"
 ,"."
 ,"E-E"
 ,"E E * E"
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
 ,"∨"]
 
 

function taurules2 seq.seq.seq.word 
 [ ["G F #","R_1"]
 , ["F W W(FP)T E","createfunc(R, code.R_2, types.R_4, R_6, R_7)"]
 , ["F W N(FP)T E","createfunc(R, code.R_2, types.R_4, R_6, R_7)"]
 , ["F W W T E"
 ,"createfunc(R, code.R_2, empty:seq.mytype, R_3, R_4)"]
 , ["F W W:T T E"
 ,"let name = [ merge(code.R_2 + &quot:&quot + print.mytype.gettype.R_4)]createfunc(R, name, empty 
:seq.mytype, R_5, R_6)"]
 , ["F W W:T(FP)T E"
 ,"let name = [ merge(code.R_2 + &quot:&quot + print.mytype.gettype.R_4)]createfunc(R, name, types.
 R_6, R_8, R_9)"]
 , ["F W W is W P"
 ,"assert(code.R_4)_1 in &quot record encoding sequence &quot report errormessage(&quot Expected &em 
 record &em encoding or &em sequence after &em is in type definition got:&quot + code.R_4, input, place 
)bindinfo(dict.R, code.R_4 + code.R_2 + code.R_5, types.R_5)"]
 , ["F W T","// use clause // bindinfo(dict.R, gettype.R_2, empty:seq.mytype)"]
 , ["FP P"
 ,"bindinfo(@(addparameter(cardinality.dict.R, input, place), identity, dict.R, types.R_1), &quot &quot, types 
.R_1)"]
 , ["P T","bindinfo(dict.R, &quot &quot, [ mytype(gettype.R_1 + &quot:&quot)])"]
 , ["P P, T","bindinfo(dict.R, &quot &quot, types.R_1 + [ mytype(gettype.R_3 + &quot:&quot)])"]
 , ["P W:T","bindinfo(dict.R, code.R_1 + code.R_3, [ mytype(gettype.R_3 + code.R_1)])"]
 , ["P P, W:T"
 ,"bindinfo(dict.R, code.R_1 + code.R_3 + code.R_5, types.R_1 + [ mytype(gettype.R_5 + code.R_3)])"]
 , ["P comment W:T"
 ,"bindinfo(dict.R, &quot // &quot + code.R_1 + &quot // &quot + code.R_2 + code.R_4, [ mytype(gettype.R_4 + code 
.R_2)])"]
 , ["P P, comment W:T"
 ,"bindinfo(dict.R, &quot // &quot + code.R_3 + &quot // &quot + code.R_1 + code.R_4 + code.R_6, types.R_1 + [ mytype 
(gettype.R_6 + code.R_4)])"]
 , ["E W"
 ,"let id = code.R_1 let f = lookupbysig(dict.R, id_1, empty:seq.mytype, input, place)bindinfo(dict.R, [ mangledname 
.f], [ resulttype.f])"]
 , ["E N(L)","unaryop(R, code.R_1, R_3)"]
 , ["E W(L)","unaryop(R, code.R_1, R_3)"]
 , ["E W:T(L)"
 ,"let name = [ merge(code.R_1 + &quot:&quot + print.(types.R_3)_1)]unaryop(R, name, R_5 
)"]
 , ["E(E)","R_2"]
 , ["E { E }","R_2"]
 , ["E if E then E else E"
 ,"let thenpart = R_4 assert(types.R_2)_1 = mytype.&quot boolean &quot report errormessage(&quot cond of 
 if must be boolean &quot, input, place)assert(types.R_4)=(types.R_6)report errormessage(&quot then 
 and else types are different &quot, input, place)let newcode = code.R_2 + code.R_4 + code.R_6 bindinfo(dict.R 
, newcode + &quot if &quot, types.thenpart)"]
 , ["E E^E","opaction(R)"]
 , ["E E_E","opaction(R)"]
 , ["E-E","unaryop(R, code.R_1, R_2)"]
 , ["E W.E","unaryop(R, code.R_1, R_3)"]
 , ["E N.E","unaryop(R, code.R_1, R_3)"]
 , ["E E * E","opaction(R)"]
 , ["E E-E","opaction(R)"]
 , ["E E = E","opaction(R)"]
 , ["E E > E","opaction(R)"]
 , ["E E ∧ E","opaction(R)"]
 , ["E E ∨ E","opaction(R)"]
 , ["L E","R_1"]
 , ["L L, E","bindinfo(dict.R, code.R_1 + code.R_3, types.R_1 + types.R_3)"]
 , ["E [ L]"
 ,"let types = types(R_2)assert @(&and, =(types_1), true, types)report errormessage(&quot types do not match in 
 build &quot, input, place)bindinfo(dict.R, &quot LIT 0 LIT &quot + toword.(length.types)+ code.R_2 + &quot 
 RECORD &quot + toword.(length.types + 2), [ mytype(towords(types_1)+ &quot seq &quot)])"]
 , ["A let W = E"
 ,"let e = R_4 let name =(code.R_2)_1 assert isempty.lookup(dict.R, name, empty:seq.mytype)report errormessage 
(&quot duplicate symbol:&quot + name, input, place)let newdict = dict.R + symbol(name, mytype(&quot 
 local &quot), empty:seq.mytype,(types.e)_1, &quot &quot)bindinfo(newdict, code.e + &quot define &quot 
 + name, types.e)"]
 , ["E A E","let t = code.R_1 
 let f = lookup(dict.R, last.code.R_1, empty:seq.mytype)assert not(isempty.f)report &quot internal 
 error/could not find local symbol to delete from dict with name &quot + last(code.R_1)bindinfo 
(dict.R_1-f_1, subseq(t, 1, length.t- 2)+ code.R_2 + &quot SET &quot + last.code.R_1, types.R_2)"]
 , ["E assert E report E E"
 ,"assert types(R_2)_1 = mytype.&quot boolean &quot report errormessage(&quot condition in assert must 
 be boolean in:&quot, input, place)assert types(R_4)_1 = mytype.&quot word seq &quot report errormessage 
(&quot report in assert must be seq of word in:&quot, input, place)let newcode = code.R_2 + code.R_5 + code 
.R_4 + &quot assertZbuiltinZwordzseq if &quot bindinfo(dict.R, newcode, types.R_5)"]
 , ["E I","R_1"]
 , ["E I.I"
 ,"let d = decodeword.(code.R_3)_2 bindinfo(dict.R, &quot LIT &quot + [ encodeword(decodeword.(code.R 
_1)_2 + d)]+ &quot LIT &quot + countdigits(d, 1, 0)+ &quot makerealZrealZintZint &quot, [ mytype.&quot 
 real &quot])"]
 , ["T W","isdefined( R, code.R_1)"]
 , ["T W.T","isdefined( R, towords.(types.R_3)_1 + code.R_1)"]
 , ["E W:T"
 ,"let f = lookup(dict.R, merge(code.R_1 + &quot:&quot + print((types.R_3)_1)), empty:seq.mytype)assert not 
.isempty.f report errormessage(&quot cannot find &quot + code.R_1 + &quot:&quot + print.mytype.code 
.R_3, input, place)bindinfo(dict.R, [ mangledname.f_1], [ resulttype.f_1])"]
 , ["E $wordlist"
 ,"let s = code.R_1 bindinfo(dict.R, &quot WORDS &quot + toword.length.s + s, [ mytype.&quot word seq &quot 
])"]
 , ["E comment E"
 ,"let s = code.R_1 bindinfo(dict.R, code.R_2 + &quot COMMENT &quot + toword.length.s + s, types.R_2)"]
 , ["N_","R_1"]
 , ["N-","R_1"]
 , ["N =","R_1"]
 , ["N >","R_1"]
 , ["N *","R_1"]
 , ["N &and ","R_1"]
 , ["N &or ","R_1"]
 , ["K W.E","bindinfo(dict.R, code.R_1 + code.R_3, types.R_3)"]
 , ["K N.E","bindinfo(dict.R, code.R_1 + code.R_3, types.R_3)"]
 , ["K N(L)","bindinfo(dict.R, code.R_1 + code.R_3, types.R_3)"]
 , ["K W(L)","bindinfo(dict.R, code.R_1 + code.R_3, types.R_3)"]
 , ["K N","bindinfo(dict.R, code.R_1, empty:seq.mytype)"]
 , ["K W","bindinfo(dict.R, code.R_1, empty:seq.mytype)"]
 , ["E @(K, K, E, E)","apply(R_3, R_5, R_7, R_9, input, place)"]]
 
 
 
 Function gentaupretty seq.word 
 // used to generater tau parser for Pass1 of the tau compiler. // 
 lr1parser(tauprettyrules 
 , tauruleprec 
 ,".=():>]-{ } comment, [_^is T if # then else let assert report ∧ ∨ * $wordlist @ A E G F W P N L I K FP")

 
 function tauprettyrules  seq.seq.seq.word 
 [ ["G F #","R_1"]
 , ["F W W(FP)T E"," pretty 
  .[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block(R_7)else R_7]
"]
 , ["F W N(FP)T E","F W W(FP)T E"," pretty 
  .[ key.R_1, R_2, R_3, R_4, R_5, R_6, if width.R_4 + width.R_7 > 30 then block(R_7)else R_7]
"]
 , ["F W W T E" ,"pretty.[key.R_1,R_2,R_3,R_4]"]
 , ["F W W:T T E","pretty.[key.R_1,R_2,R_3,R_4,R_5,R_6]"]
 , ["F W W:T(FP)T E","pretty.[key.R_1,R_2,R_3,R_4,R_5,R_6,R_7,R_8,R_9]"]
 , ["F W W is W P","pretty.[key.R_1,R_2,R_3,R_4,list.R_5]"]
 , ["F W T"," // use // pretty.[key.R_1,R_2]"]
 , ["FP P","list.R_1"]
 , ["P T","R_1 "]
 , ["P P, T","R_1+R_3 "]
 , ["P W:T","pretty.[R_1,R_2,R_3]"]
 , ["P P, W:T","R_1+pretty.[R_3,R_4,R_5]"]
 , ["P comment W:T","pretty.[R_1,R_2,R_3,R_4]"]
 , ["P P, comment W:T","R_1+pretty.[R_3,R_4,R_5,R_6]"]
 , ["E W","R_1 "]
 , ["E N(L)",' pretty.[R_1,R_2,list.R_3,R_4] ' ]
 , ["E W(L)","pretty.[R_1,R_2,list.R_3,R_4]"]
 , ["E W:T(L)","pretty.[R_1,R_2,R_3,R_4,list.R_5,R_6]"]
 , ["E(E)","R_2"]
 , ["E { E }","R_2"]
 , ["E if E then E else E","
  if width.R_2 + width.R_4 + width.R_6 < 30 then 
  pretty.[ key.R_1, R_2, key.R_3, R_4, key.R_5, R_6]
  else if width.R_2 + width.R_4 < 30 then 
   pretty.[ key.R_1, R_2, key.R_3,  R_4, elseblock.R_6]
  else pretty.[ keyif, R_2, prettyresult(  &quot &keyword then &br  &quot ), block(R_4), elseblock.R_6] " ]
 , ["E E^E","wrap(1,R_1,text.R_2,R_3)"]
 , ["E E_E","wrap(1,R_1,text.R_2,R_3)"]
 , ["E-E","wrap(2,prettyresult.&quot &quot,text.R_2,R_3)"]
 , ["E W.E","wrap(3,R_1,text.R_2,R_3)"]
 , ["E N.E","wrap(3,R_1,text.R_2,R_3)"]
 , ["E E * E","wrap(4,R_1,text.R_2,R_3)"]
 , ["E E-E","wrap(5,R_1,text.R_2,R_3)"]
 , ["E E = E","wrap(6,R_1,text.R_2,R_3)"]
 , ["E E > E","wrap(7,R_1,text.R_2,R_3)"]
 , ["E E ∧ E","wrap(8,R_1,text.R_2,R_3)"]
 , ["E E ∨ E","wrap(9,R_1,text.R_2,R_3)"]
 , ["L E","R_1"]
 , ["L L, E","R_1+R_3"]
 , ["E [ L]",  "pretty.[R_1,list.R_2,R_3]"]
 , [ "A let W = E" ," pretty.[ keylet, R_2, R_3,R_4]" ]
 , [ "E A E " ,'   pretty.[ R_1, block("let assert", R_2)] ']
 , [ "E assert E report E E " ,'   pretty.[ keyassert, R_2, keyreport, R_4, block("let assert", R_5)] ' ]
 , ["E I","R_1"]
 , ["E I.I","pretty.[R_1,R_2,R_3]"]
 , ["T W","R_1"]
 , ["T W.T","pretty.[R_1,R_2,R_3]"]
 , ["E W:T","pretty.[R_1,R_2,R_3]"]
 , ["E $wordlist","R_1"]
 , ["E comment E",  ' if width.R_1 + width.R_2 > 30 
  ∧ (text.R_2)_1 ≠ "&br"_1 then 
 pretty.[ R_1,prettyresult."&br", R_2]
  else pretty.[ R_1, R_2]  ' ]
 , ["N_","R_1"]
 , ["N-","R_1"]
 , ["N =","R_1"]
 , ["N >","R_1"]
 , ["N *","R_1"]
 , ["N &and ","R_1"]
 , ["N &or ","R_1"]
 , ["K W.E","pretty.[R_1,R_2,R_3]"]
 , ["K N.E","pretty.[R_1,R_2,R_3]"]
 , ["K N(L)","pretty.[ R_1,  R_2, list.R_3,R_4]"]
 , ["K W(L)","pretty.[ R_1,  R_2, list.R_3,R_4]"]
 , ["K N","R_1"]
 , ["K W","R_1"]
 , ["E @(K, K, E, E)","pretty.[ R_1, R_2,   list(R_3+R_5+R_7+R_9), R_10]"]]


