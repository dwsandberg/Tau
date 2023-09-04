Module genPEG

use PEG

use PEGrules

use seq.pegpart

use standard

use otherseq.word

use otherseq.seq.word

function extractPEGgrammar(s:seq.word) seq.word
{This grammar uses", dq" to find end of action since a rule such as <* block" Atom (E)" = let
 a = E, E2 *> has a comma in the middle of it. Note that this grammar would still not handle the
 case when E2 starts with a string literal.}
let g2 = maketable."* S str1 dq = N, dq /action /0 //br /1 //action /2
 /br * str1 ! dq any /action /All
 /br * N dq str1 dq /action /0 dq /1 dq
 /br / (N2) /action /0 (/1)
 /br /, ! dq /action /0,
 /br / str2 /action /0 /1
 /br * N2, /action /0,
 /br / N /action /0 /1
 /br * str2 !, ! dq ! (!) any /action /All"
let tmp = run(g2, subseq(s, findindex(s, 1_"[") + 2, n.s - 1) + "," + dq)
assert 1_tmp ∈ "Match" report "genPEG error A",
tmp << 1

Function generatePEG(rest:seq.word) seq.seq.word
let Flags = "error trace recover isWords common"
for
 argrules = ""
 , flags = ""
 , e ∈ break(subseq(rest, 4, findindex(rest, 1_")") - 1), ",", false)
do
 let k = findindex("seqElementType attributeType runresultType common" + Flags, 1_e),
  if k > 4 + n.Flags then
  next(argrules, flags)
  else next(
   if k > 4 then
   argrules
   else
    argrules
    + "/^(k_"seqElementType attributeType runresultType commonType") /action /0"
    + e << 2
   , if k ≥ 4 then
    flags + 1_e
    else if k = 1 ∧ e << 2 = "word" then
    flags + "isWords"
    else flags
  )
for tmp = "", f ∈ Flags
do
 let /f = merge("/" + f),
 tmp + "^(/f) S2 Else /end /action /0^(if f ∈ flags then "/1 /" else "/2 /")"
let subgrammar = "* S2^(tmp) S /action /0 /1
 /br Else /else S /action /1 / /action
 /br * S doublequote /action /0^(dq)
 /br / //br /action /0
 ^(if 1_"isWords" ∈ flags then "/ tblEle /action /0 tableEntry" else "")
 /br / $$$ /action /0^
 ^(argrules)^(if 1_"common" ∈ flags then "" else "/ commonType /action /0 int")
 /br / ! /error ! /trace ! /recover ! /common ! /isWords ! /end ! /else any /action /0 /1"
{assert false report textGrammar.PEGgrammar.subgrammar}
let substitutionsTable = maketable.subgrammar
let temp0 = applySubstitutions(substitutionsTable, template)
let templatedecs =
 if 1_temp0 = "function = (seq.word, seq.word) boolean true" then
 temp0 << 1
 else temp0,
if findindex(rest, 1_"[") > n.rest then
templatedecs
else
 let grammar = extractPEGgrammar.rest
 assert subseq(grammar, 2, 2) = "match2code" report "expected match2code as first rule"
 for count = 2, last = 1_"X", w ∈ grammar << 2
 while not(last ∈ "/br" ∧ w ∉ "/")
 do next(count + 1, w)
 let gin = PEGgrammar(grammar << count),
  maketable22(
   PEGgrammar(grammar << count)
   , PEGgrammar.subseq(grammar, 1, count)
   , substitutionsTable
   , 1_"isWords" ∈ flags
  )
  + templatedecs

use otherseq.tableEntry

use seq.pegrule

function makeAction(gin:seq.pegrule) seq.word
for acc = "", partno = 2, r ∈ gin
do
 let x =
  for partno0 = partno, acc0 = acc, p ∈ parts.r
  do
   let tmp =
    if replacement.p ∈ ["/All", "/Discard"] then
    ""
    else "if partno =^(partno0) then^(replacement.p) else",
   next(partno0 + 1, acc0 + tmp),
  acc0,
 next(x, partno + n.parts.r),
"^(acc >> 1) else 0_R"

use seq.int

use seq.tableEntry

use set.int

use otherseq.int

/use newPretty

function maketable22(
 gin:seq.pegrule
 , matchGrammar:seq.pegrule
 , table:PEGtable
 , isWords:boolean
) seq.seq.word
let matchtbl = maketable.matchGrammar
let actionDefinition = run(
 table
 , "function action (partno:int, R:reduction, place:int, input:seq.seqElementType,
  common:commonType, parsestk:stack.frame) attributeType"
)
assert 1_actionDefinition ∈ "Match" report "sub problem in genPEG"
{Generate table code}
let addrecover = run(table, "/recover seqElementType /end") = "Match word"
let tblEle = if isWords then "tableEntry" else "tblEle"
for x1 = "", e ∈ subseq(gin, 1, 10) do x1 + leftside.e
let x2 =
 1
 _(
  if x1 = "S Header Comment String String' str2 E EL' Or Or'" then
  "newPretty"
  else if x1 = "S Header FPL FPL' FP Type id Comment N str1" then
  "symbolMode"
  else if x1 = "S String String' str2 E EL' Or Or' And And'" then
  "parser"
  else if x1 = "CN CS NSBA NSB N N' S" then
  "formatTest"
  else if x1 = "leftside rightside rightside' part str" then
  "PEG5"
  else if x1 = "E IF EL' Id" then
  "recoverTest"
  else if x1 = "Paragraph Words StandAlone WhiteSpace Word" then
  "PEGbreak"
  else "X"
 )
let tbl = makeTbl(gin, addrecover)
for table2 = "", i ∈ arithseq(n.tbl, 1, 1)
do
 let te = i_tbl
 let Recover =
  if not.isWords then
  ""
  else
   for acc = "", w ∈ if not.addrecover then "" else recover.te
   do
    let tmp = run(matchtbl, [w])
    assert 1_tmp ∈ "Match" report "genPEG error B^(w)",
     if 2^tmp ∉ "^" ∧ "Match 1_^(dq.[2^tmp])" = tmp then
     acc + 2^tmp
     else acc + "^" + "(^(tmp << 1))",
   "," + dq.acc
 let tmp = run(matchtbl, [match.te])
 assert 1_tmp ∈ "Match" report "genPEG error C^(match.te)",
  table2
  + "{^(i)}^(tblEle) (^(action.te),^(tmp << 1),^(Sstate.te),^(Fstate.te)^(Recover)),",
[
 textGrammar.gin
 , actionDefinition << 1 + makeAction.gin
 , "function^(merge."mytable") seq.^(tblEle) [^(table2 >> 1)]"
]

Function applySubstitutions(table:PEGtable, intemplate:seq.seq.word) seq.seq.word
for acc = empty:seq.seq.word, p ∈ intemplate
do
 let tmp = run(table, p)
 assert 1_tmp ∈ "Match" report "sub problem in genPEG:^(p)^(tmp)",
 if n.tmp = 1 then acc else acc + tmp << 1,
acc

function template seq.seq.word
[
 "function = (seq.word, attributeType) boolean true"
 , "function = (seq.word, seqElementType) boolean true"
 , "use standard"
 , "use seq.tblEle"
 , "use otherseq.frame"
 , "use stack.frame"
 , "use otherseq.attributeType"
 , "use PEGrules"
 , "function_(i:int, R:reduction) attributeType (i+1)_toseq.R"
 , "/isWords /else type tblEle is action:state, match:seqElementType, Sstate:state, Fstate:
  state /end"
 , "/recover function recovery (parsestk:stack.frame) seq.word for acc =^(dq.""), frame ∈ toseq.parsestk do if action.Sstate.frame /in [Match, S] then acc+recover.(
  index.Sstate.frame)_mytable else acc acc /end"
 , "type reduction is toseq:seq.attributeType"
 , "type frame is Sstate:state, Fstate:state, i:int, result:seq.attributeType, faili:
  int, failresult:seq.attributeType"
 , "type runresultType is stk:stack.frame /trace, trace:seq.word /end"
 , "Function status (a:runresultType) word if Sstate.top.stk.a /ne Reduce.1 then 1_
  ^(dq."Failed")"
  + "else if i.top.stk.a = {length of input} faili.top.stk.a then 1_^(dq."Match")"
  + "else 1_^(dq."MatchPrefix")"
 , "Function result (a:runresultType) attributeType 1^result.top.stk.a"
 , "/trace function tracestart (trace:seq.word) seq.word^(dq)"
  + "<* table
   /row stk top.stk /cell top.stk
   /row depth S F /cell result /cell result /cell Fail / State /cell idx / remaining input $$$ (trace
   ) *>^(dq)"
  + "/end"
 , "/trace function trace (trace0:seq.word, stk:stack.frame, result:seq.attributeType,
  faili:int, state:state, i:int, input:seq.seqElementType) seq.word let stkdata = %.
  n.toseq.stk+if isempty.stk then doublequote /cell doublequote else doublequote $$$ (faili
  .top.stk) $$$ (Sstate.top.stk) $$$ (Fstate.top.stk) /cell $$$ (1^result.top.stk) doublequote, trace0+doublequote
  /row $$$ (stkdata) /cell $$$ (% (doublequote^doublequote, result) >> 1) /cell $$$ (faili) $$$ (state) /cell $$$ (i) $$$ (subseq (
  input, i, i+20)) doublequote /end"
 , "function parse (myinput0:seq.seqElementType, table:seq.tblEle, initAttr:attributeType
  /common, common:commonType /end) runresultType
  /br let myinput = packed (myinput0+endMark)
  /br let packedTable = packed.table /common /else let common = 0 /end
  /br for /trace trace0 =^(dq)^(dq), /end /error maxi = 0, maxStk = empty:stack.frame, /end stk = empty:stack.frame, state
  = startstate, i = 1, inputi = 1_myinput, result = [initAttr], faili = 1, failresult = [
  initAttr]
  /br while not (state = Reduce.1 /or state = Reduce.0) do
  /br /trace let trace = trace (trace0, stk, result, faili, state, i, (myinput)), /end
  /br let actionState = action.state
  /br if actionState = Fail then {goto Fstate.top.stk, i = faili.top, pop.stk, discard
  result}
  /br let top = top.stk let newstk = pop.stk,
  /br next (/trace trace, /end /error maxi, maxStk, /end newstk, if is!.Sstate.top then
  Sstate.top else Fstate.top, faili.top, idxNB (myinput, faili.top), failresult.top,
  faili.top, failresult.top)
  /br else if actionState = Success* then {goto Sstate.top.stk, pop.stk, keep result} let
  top = top.stk, next (/trace trace, /end /error maxi, maxStk, /end pop.stk, Sstate.top,
  i, inputi, result.top+result, faili.top, failresult.top)
  /br else if actionState = SuccessDiscard* then {goto Sstate.top.stk, pop.stk, keep result
  } let top = top.stk, next (/trace trace, /end /error maxi, maxStk, /end pop.stk, Sstate.
  top, i, inputi, result.top, faili.top, failresult.top)
  /br else if actionState = Discard* then
  /br let top = top.stk, /error
  /br if faili = i then next (/trace trace, /end /error maxi, maxStk, /end pop.stk, Sstate.
  top, i, inputi, result.top, faili.top, failresult.top)
  /br else let newmaxStk = if i ≥ maxi then stk else maxStk /end next (/trace trace, /end /error
  max (maxi, i), newmaxStk, /end stk, nextState.state, i, inputi, result.top, i,
  result.top)
  /br else if actionState = All then let top = top.stk let att = [toAttribute (1^result, subseq (myinput, i.top, i-1))], next (/trace trace, /end /error maxi, maxStk
  , /end pop.stk, Sstate.top, i, inputi, result.top+att, faili.top, failresult.top
  )
  /br else if actionState = Reduce then {Reduce} if nextState.state /ne S.0 then
  /br let att = [action (reduceNo.state, reduction.result, i, myinput, common, stk)]
  /br let top = top.stk, /error let newmaxStk = if i ≥ maxi then stk else maxStk /end
  /br if faili = i then next (/trace trace, /end /error maxi, maxStk, /end pop.stk, Sstate.
  top, i, inputi, result.top+att, faili.top, failresult.top) else next (/trace trace,
  /end /error max (i, maxi), newmaxStk, /end stk, nextState.state, i, inputi, att, i,
  att)
  /br else let top = top.stk,
  /br if is!.Sstate.top then {goto Fstate.top.stk, i = faili.top, pop.stk, discard
  result}
  /br let newstk = pop.stk,
  /br let newi = faili.top let ini = idxNB (myinput, newi) next (/trace trace, /end /error
  maxi, maxStk, /end newstk, Fstate.top, newi, ini, failresult.top, faili.top,
  failresult.top)
  /br else /error
  /br let att = [action (reduceNo.state, reduction.result, i, myinput, common, stk)] if
  i ≥ maxi then
  /br next (/trace trace, /end i, stk, pop.stk, Sstate.top, i, inputi, result.top+att
  , faili.top, failresult.top) else /else
  /br let att = [action (reduceNo.state, reduction.result, i, myinput, common, stk)]
  /end next (/trace trace, /end /error maxi, maxStk, /end pop.stk, Sstate.top, i, inputi,
  result.top+att, faili.top, failresult.top)
  /br else if actionState = Match then let te = idxNB (packedTable, index.state) if inputi ≠
  match.te then {fail} next (/trace trace, /end /error maxi, maxStk, /end stk, Fstate.te,
  faili, idxNB (myinput, faili), failresult, faili, failresult) else next (/trace trace,
  /end /error maxi, maxStk, /end stk, Sstate.te, i+1, idxNB (myinput, i+1), result,
  faili, failresult) else if actionState = !Match then let te = idxNB (packedTable, index.state
  ) if inputi = match.te then {fail} next (/trace trace, /end /error maxi, maxStk, /end stk,
  Sstate.te, faili, idxNB (myinput, faili), failresult, faili, failresult) else next (
  /trace trace, /end /error maxi, maxStk, /end stk, Fstate.te, i, inputi, result, faili,
  failresult)
  /br else if actionState = MatchAny then let te = idxNB (packedTable, index.state), if inputi
  = endMark then {fail} next (/trace trace, /end /error maxi, maxStk, /end stk, Fstate.te,
  i, inputi, result, faili, failresult) else let reslt = if action.Sstate.te = Discard* then
  result else result+toAttribute (1^result, [inputi]) let ini = idxNB (myinput, i+1), next (/trace trace, /end /error maxi
  , maxStk, /end stk, Sstate.te, i+1, ini, reslt, faili, failresult)
  /br else if actionState = MatchNext then
  /br let te = idxNB (packedTable, index.state) if inputi = match.te then
  /br next (/trace trace, /end /error maxi, maxStk, /end stk, Sstate.te, i+1, idxNB (
  myinput, i+1), result, faili, failresult)
  /br else next (/trace trace, /end /error maxi, maxStk, /end stk, Fstate.te, i, inputi,
  result, faili, failresult)
  /br else {match non Terminal} let te = idxNB (packedTable, index.state) assert action.
  action.te = MatchNT report
  ^(dq) PROBLEM PEG $$$ (state)^(dq)
  /br let newstk = push (stk, frame (Sstate.te, Fstate.te, i, result, faili, failresult)
  ) let tmp = [toAttribute (1^result, empty:seq.seqElementType)] next (/trace trace, /end /error maxi, maxStk, /end
  newstk, nextState.action.te, i, inputi, tmp, i, tmp)
  /br runresultType (push (/error maxStk /else stk /end, frame (state, state, /error maxi /else
  i /end, result, n.myinput, result))
  /br /trace, tracestart.trace0 /end)"
] 