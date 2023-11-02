Module genPEG

use PEG

use PEGgenNoTable

use PEGparse

use PEGrules

use otherseq.int

use seq.int

use set.int

use seq.pegpart

use seq.pegrule

use standard

use otherseq.tableEntry

use seq.tableEntry

use otherseq.word

use otherseq.seq.word

Function generatePEG(rest:seq.word) seq.seq.word
let substitutionsTable = maketable(PEGparse.rest, "dq^(dq), // /, //action /action, //br /br")
let templatedecs = applySubstitutions(substitutionsTable, template)
let j = findindex(rest, 1#")") + 2
for j2 = j while j2#rest ∈ "." do j2 + 2
let j3 = if j2#rest ∈ "{" then j2 + findindex(rest << j2, 1#"}") + 1 else j2
let zz = rest << (j3 - 1),
if 1#zz ∉ "[" then
templatedecs
else
 let gin = PEGparse.zz
 let wordmap = extractValue(rest >> (n.zz + 1), "wordmap")
 let isWords = run(substitutionsTable, "/isWords T /end") = "Match T"
 {Generate table code}
 let addrecover = run(substitutionsTable, "/error seqElementType /end") = "Match word"
 let tbl = makeTbl(gin, addrecover),
  if 1#"notable" ∈ rest >> (n.zz + 1) then
  applySubstitutions(substitutionsTable, notable(gin, tbl, wordmap))
  else
   let tblEle = if isWords then "tableEntry" else "tblEle"
   for table2 = "", i ∈ arithseq(n.tbl, 1, 1)
   do
    let te = i#tbl
    let Recover =
     if not.isWords then
     ""
     else
      for acc = "", w ∈ if not.addrecover then "" else recover.te
      do
       let tmp = applySubs(wordmap, [w]),
        if n.tmp > 1 ∧ 2^tmp ∉ "^" ∧ tmp ∈ ["1#^(dq.[2^tmp])"] then
        acc + 2^tmp
        else acc + "^" + "(^(tmp))",
      ",^(dq.acc)",
     table2
      + "{^(i)}^(tblEle) (^(action.te),^(applySubs(wordmap, [match.te])),^(Sstate.te),
     ^(Fstate.te)^(Recover)),",
    [
     textGrammar.gin
     , applySubs(
      substitutionsTable
      , "function action (partno:int, R:seq.attributeType /common, commonName:commonType /end
      /error, rinfo:resultType /end) attributeType"
     )
      + makeAction.gin
     , "function^(merge."mytable") seq.^(tblEle) [^(table2 >> 1)]"
    ]
     + templatedecs

function makeAction(gin:seq.pegrule) seq.word
for acc = "", partno = 2, r ∈ gin
do
 let x =
  for partno0 = partno, acc0 = acc, p ∈ parts.r
  do
   let tmp =
    if replacement.p ∈ ["/All"] then
    ""
    else "if partno =^(partno0) then^(fixit(replacement.p, NTcount(p, gin) + 1)) else",
   next(partno0 + 1, acc0 + tmp),
  acc0,
 next(x, partno + n.parts.r),
acc >> 1 + "else 1#R"

function fixit(r:seq.word, noNT:int) seq.word
if n.r < 3 then
r
else
 let none = merge.".."
 for acc = "", l2 = none, l1 = none, e ∈ r + ".."
 do
  if l1 ∈ "." ∧ l2 ∈ "$" then
  next(acc + (%(noNT - toint.e) + "^" + "R"), none, none)
  else next(if l2 = none then acc else acc + l2, l1, e),
 acc

Function applySubstitutions(table:PEGtable, intemplate:seq.seq.word) seq.seq.word
for acc = empty:seq.seq.word, p ∈ intemplate
do let tmp = applySubs(table, p), if isempty.tmp then acc else acc + tmp,
acc

function applySubs(wordmap:seq.word, p:seq.word) seq.word replaceWords(p, wordmap)

function applySubs(table:PEGtable, p:seq.word) seq.word
let tmp = run(table, p)
assert 1#tmp ∈ "Match" report "sub problem in genPEG:^(p)^(tmp)",
tmp << 1

function template seq.seq.word
[
 "/wordsAttribute /else function = (seq.word, attributeType) boolean true /end"
 , "function $ (int) attributeType 1#empty:seq.attributeType"
 , "use standard"
 , "use seq.tblEle"
 , "use otherseq.frame"
 , "use stack.frame"
 , "use otherseq.attributeType"
 , "use PEGrules"
 , "/isWords /else type tblEle is action:state, match:seqElementType, Sstate:state, Fstate:
 state /end"
 , "/error function recoveryEnding (rinfo:resultType /nogrammar, mytable:seq.tableEntry /end)
 seq.word
 /br for acc =^(dq.""), frame ∈ reverse.toseq.pop.stk.rinfo do
 /br if action.Sstate.frame /in [T, NT] then acc+recover.(index.Sstate.frame)#
 mytable else acc acc /else function place (r:resultType) int i.top.stk.r /end"
 , "type frame is Sstate:state, Fstate:state, i:int, result:seq.attributeType, faili:
 int, failresult:seq.attributeType"
 , "type resultType is stk:stack.frame /error, input:seq.word, place:int /end /trace,
 trace:seq.word /end"
 , "Function status (a:resultType) word if Sstate.top.stk.a /ne Match then 1#
 ^(dq."Failed") else if place.a = {length of input} faili.top.stk.a then 1#
 ^(dq."Match") else 1#^(dq."MatchPrefix")"
 , "Function result (a:resultType) attributeType 1^result.top.stk.a"
 , "/trace function tracestart (trace:seq.word) seq.word^(dq) $/br Key to column labels S--step no; D--Depth of Stack F--on fail reset I to F; I--
 Location in input; Lower case are values on top of stack <* table
 /row S /cell D /cell f /cell success /cell fail /cell result /cell Result /cell F /cell State /cell
 I /cell Remaining input $carrot (trace) *>
 ^(dq) /end"
 , "/trace function trace (stepno:int, trace0:seq.word, stk:stack.frame, result:seq.
 attributeType, faili:int, state:state, i:int, input:seq.seqElementType) seq.word
 let stkdata = %.n.toseq.stk+if isempty.stk then^(dq) /cell /cell /cell /cell^(dq) else
 ^(dq) /cell $carrot (faili.top.stk) /cell $carrot (Sstate.top.stk) /cell $carrot (Fstate.
 top.stk) /cell $carrot (1^result.top.stk)^(dq), trace0+^(dq)
 /row $carrot (stepno) /cell $carrot (stkdata) /cell $carrot (% (
 ^(dq)^^(dq), result) >> 1) /cell $carrot (faili) /cell $carrot (state) /cell $carrot (i) /cell $carrot
 (subseq (input, i, min (i+20, n.input-1)))^(dq) /end"
 , "function parse (myinput0:seq.seqElementType, /nogrammar table:seq.tblEle, /else /end
 initAttr:attributeType /common, commonName:commonType /end /trace, startStep:int, endStep
 :int /end) resultType
 /br let myinput = packed (myinput0+endMark)
 /br let packedTable = packed./nogrammar table /else mytable /end
 /br for /trace stepno = 1, trace0 =^(dq)^(dq), /end /error rinfo = resultType (empty:stack.frame, myinput, 0 /trace,
 ^(dq)^(dq) /end), /end stk = empty:stack.frame, state = startstate, i = 1, inputi = 1#myinput,
 result = [initAttr], faili = 1, failresult = [initAttr]
 /br while (toint.state > toint.Match
 /br /trace /and stepno /le endStep) do let trace = if stepno < startStep then trace0 else trace (
 stepno, trace0, stk, result, faili, state, i, (myinput)) /else) do /end
 /br let actionState = action.state
 /br if actionState = Fail then {goto Fstate.top.stk, i = faili.top, pop.stk, discard
 result}
 /br let top = top.stk
 /br if toint.action.Fstate.top /ge toint.S' then let newi = i.top next (/trace stepno+
 1, trace, /end /error rinfo, /end pop.stk, nextState.Fstate.top, newi, idxNB (myinput
 , newi), result.top, faili.top, failresult.top) else
 /br next (/trace stepno+1, trace, /end /error rinfo, /end pop.stk, Fstate.top, faili.
 top, idxNB (myinput, faili.top), failresult.top, faili.top, failresult.top)
 /br else if actionState = Success* then {goto Sstate.top.stk, pop.stk, keep result} let
 top = top.stk, next (/trace stepno+1, trace, /end /error rinfo, /end pop.stk, Sstate.
 top, i, inputi, result.top+result, faili.top, failresult.top)
 /br else if actionState = Discard* then
 /br let top = top.stk,
 /br /error let newrinfo = if i > place.rinfo then resultType (stk, myinput, i /trace, trace
 /end) else rinfo /end next (/trace stepno+1, trace, /end /error newrinfo, /end stk,
 nextState.state, i, inputi, result.top, i, result.top)
 /br else if actionState = All then let top = top.stk let att = [toAttribute (1^result, subseq (myinput, i.top, i-1))], next (/trace stepno+1, trace, /end /error
 rinfo, /end pop.stk, Sstate.top, i, inputi, result.top+att, faili.top, failresult
 .top)
 /br else if actionState = Lambda then
 /br /error let newrinfo = if i > place.rinfo then resultType (stk, myinput, i /trace, trace
 /end) else rinfo /end
 /br let att = [action (reduceNo.state, result /common, commonName /end /error, newrinfo /end
 )] next (/trace stepno+1, trace, /end /error newrinfo, /end stk, nextState2.state, i,
 inputi, result+att, faili, failresult)
 /br else if actionState = Reduce then let top = top.stk,
 /br /error let newrinfo = if i > place.rinfo then resultType (stk, myinput, i /trace, trace
 /end) else rinfo /end
 /br let att = [action (reduceNo.state, result /common, commonName /end /error, newrinfo /end
 )] next (/trace stepno+1, trace, /end /error newrinfo, /end pop.stk, Sstate.top, i,
 inputi, result.top+att, faili.top, failresult.top)
 /br else if actionState = Reduce* then /error let newrinfo = if i > place.rinfo then resultType (
 stk, myinput, i /trace, trace /end) else rinfo /end
 /br let att = [action (reduceNo.state, result /common, commonName /end /error, newrinfo /end
 )]
 /br let top = top.stk,
 /br next (/trace stepno+1, trace, /end /error newrinfo, /end stk, nextState.state, i,
 inputi, att, i, att)
 /br else if actionState = !Reduce then let top = top.stk, let ini = idxNB (myinput, faili.
 top) next (/trace stepno+1, trace, /end /error rinfo, /end pop.stk, Fstate.top, faili
 .top, ini, failresult.top, faili.top, failresult.top)
 /br else if actionState = !Fail then let top = top.stk, let ini = idxNB (myinput, i.top)
 next (/trace stepno+1, trace, /end /error rinfo, /end pop.stk, Sstate.top, i.top,
 ini, result.top, faili.top, failresult.top)
 /br else if actionState = T then let te = idxNB (packedTable, index.state) if inputi ≠ match.
 te then {fail} next (/trace stepno+1, trace, /end /error rinfo, /end stk, Fstate.te,
 faili, idxNB (myinput, faili), failresult, faili, failresult) else next (/trace stepno+1
 , trace, /end /error rinfo, /end stk, Sstate.te, i+1, idxNB (myinput, i+1), result,
 faili, failresult) else if actionState = !T then let te = idxNB (packedTable, index.state)
 if inputi = match.te then {fail} next (/trace stepno+1, trace, /end /error rinfo, /end
 stk, Sstate.te, faili, idxNB (myinput, faili), failresult, faili, failresult) else next
 (/trace stepno+1, trace, /end /error rinfo, /end stk, Fstate.te, i, inputi, result,
 faili, failresult)
 /br else if actionState = MatchAny then let te = idxNB (packedTable, index.state), if inputi
 = endMark then {fail} next (/trace stepno+1, trace, /end /error rinfo, /end stk, Fstate.
 te, i, inputi, result, faili, failresult) else let reslt = result+toAttribute (1^result, [inputi]) let ini = idxNB (myinput, i+1), next (/trace stepno+1, trace, /end
 /error rinfo, /end stk, Sstate.te, i+1, ini, reslt, faili, failresult)
 /br else if actionState = T' then
 /br let te = idxNB (packedTable, index.state) if inputi = match.te then
 /br next (/trace stepno+1, trace, /end /error rinfo, /end stk, Sstate.te, i+1, idxNB (
 myinput, i+1), result, faili, failresult)
 /br else next (/trace stepno+1, trace, /end /error rinfo, /end stk, Fstate.te, i, inputi
 , result, faili, failresult)
 /br else {match non Terminal} let te = idxNB (packedTable, index.state) assert action.
 action.te /in [NT, NT*] report
 ^(dq) PROBLEM PEG $carrot (state)^(dq)
 /br let newstk = push (stk, frame (Sstate.te, Fstate.te, i, result, faili, failresult)
 ) let tmp = [toAttribute (1^result, empty:seq.seqElementType)] next (/trace stepno+1, trace, /end /error rinfo,
 /end newstk, nextState.action.te, i, inputi, tmp, i, tmp)
 /br resultType (push (/error stk.rinfo /else stk /end, frame (state, state, /error place.
 rinfo /else i /end, result, n.myinput, result))
 /br /error, input.rinfo, place.rinfo /end /trace, tracestart.trace0 /end)"
] 