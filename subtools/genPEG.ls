Module genPEG

use PEG

use standard

function extractPEGgrammar(s:seq.word) seq.word
{This grammar uses", dq" to find end of action since a rule such as <* block" Atom (E)" = let a = E, E2 *> does has a comma in the middle of it. Note that this grammar would still not handle the case when E2 start with a string literal.}
let g2 = maketable."* S str1 dq = N, dq /action /0 //br /1 //action /2 /br * str1 ! dq any /action /All
 /br * N dq str1 dq /action /0 dq /1 dq
 /br / (N2) /action /0 (/1)
 /br /, ! dq /action /0,
 /br / str2 /action /0 /1
 /br * N2, /action /0,
 /br / N /action /0 /1
 /br * str2 !, ! dq ! (!) any /action /All",
run2(g2, subseq(s, findindex(s, 1_"[") + 2, n.s - 1) + "," + dq)

Function generatePEG(rest:seq.word) seq.seq.word
let substitutionsTable =
 for
  argrules = ""
  , flags = ""
  , e ∈ break(subseq(rest, 4, findindex(rest, 1_")") - 1), ",", false)
 do
  let k = findindex("seqElementType attributeType runresultType common", 1_e),
   if k > 4 then
    if findindex("error trace", 1_e) > 2 then
    next(argrules, flags)
    else next(argrules, flags + 1_e)
   else next(
    argrules
    + "/^(k_"seqElementType attribute2 runresult commonType") /action /0"
    + e << 2
    , if 1_e ∈ "common" then flags + "common" else flags
   )
 let tmp =
  cond("trace /trace", flags)
  + cond("error /error", flags)
  + cond("common /common", flags)
 ,
 maketable(
  "* S2^(tmp) S /action /0 /1
   /br Else /else S /action /1 / /action
   /br * S doublequote /action /0^(dq)
   /br / //br /action /0
   /br / $$$ /action /0^^(argrules)"
  + (if 1_"common" ∈ flags then "" else "/ commonType /action /0 int")
  + "/ ! /error ! /trace ! /common ! /end ! /else any /action /0 /1"
 )
let temp0 = applySubstitutions(substitutionsTable, template)
let temp1 =
 if 1_temp0 = "function = (seq.word, seq.word) boolean true" then
 temp0 << 1
 else temp0
,
if findindex(rest, 1_"[") > n.rest then
temp1
else maketable22(extractPEGgrammar.rest, substitutionsTable) + temp1

function cond(c:seq.word, flags:seq.word) seq.word
"^(1^c) S2 Else /end /action /0^(if 1_c ∈ flags then "/1 /" else "/2 /")"

use otherseq.seq.word

use otherseq.word

use PEGrules

use seq.pegpart

function makeAction(gin:seq.pegrule) seq.word
for acc = "", partno = 2, r ∈ gin
do
 let x =
  for partno0 = partno, acc0 = acc, p ∈ parts.r
  do
   let tmp =
    if replacement.p ∈ ["/All", "/Discard"] then
    ""
    else "if partno =^(partno0) then^(replacement.p) else"
   ,
   next(partno0 + 1, acc0 + tmp)
  ,
  acc0
 ,
 next(x, partno + n.parts.r)
,
"^(acc >> 1) else 0_R"

function maketable22(all:seq.word, table:PEGtable) seq.seq.word
let count =
 for count = 2, last = 1_"X", w ∈ all << 2
 while not(last ∈ "/br" ∧ w ∉ "/")
 do next(count + 1, w),
 count
let matchtbl = maketable.PEGgrammar.subseq(all, 1, count)
let gin = PEGgrammar(all << count)
assert subseq(all, 2, 2) = "match2code" report "expected match2code as first rule"
let actionDefinition = run(
 table
 , "function action (partno:int, R:reduction, place:int, input:seq.seqElementType, common:commonType, parsestk:stack.frame) attribute2"
)
{Generate table code}
let addrecover = run2(table, "/error seqElementType /end") = "word"
let tbl = makeTbl.gin
for table2 = "", te ∈ makeTbl.gin
do
 table2
 + "tblEle (^(action.te),^(run2(matchtbl, [match.te])),^(Sstate.te),^(Fstate.te)"
 + "),"
,
[
 textGrammar.gin
 , actionDefinition + makeAction.gin
 , "function mytable seq.tblEle [^(table2 >> 1)]"
]
 + 
 if addrecover then
  for rtable = "", te2 ∈ recover(tbl, gin)
  do
   let convertedString =
    for acc = "", w ∈ match.te2 do acc + run2(matchtbl, [w]) + ",",
    if isempty.acc then dq."" else "[^(acc >> 1)]"
   ,
   rtable + "recoveryEntry (^(action.te2),^(convertedString),^(Sstate.te2)),"
  ,
  [
   "function recoverTable seq.recoveryEntry [^(rtable >> 1)]"
   , "use seq.recoveryEntry"
   , recoverFunctionText
  ]
 else empty:seq.seq.word

function recoverFunctionText seq.word
for
 acc = ""
 , e ∈ "function recovery (state:state, stk:stack.frame, table:seq.recoveryEntry) seq.word /br if isempty.stk then^(dq."")
  /br else if action.state = S.0 then
  /br let te = (index.state)_table,
  /br if action.te = Match ∨ action.te = MatchNext ∨ action.te = MatchAny then
  /br match.te+recovery (Sstate.te, stk, table)
  /br else
  /br assert action.action.te = actionReduce report^(dq("Not handled 1^" + "(action.te),"))
  /br recovery (Sstate.top.stk, pop.stk, table)
  /br else if action.state = actionReduce then
  /br recovery (Sstate.top.stk, pop.stk, table)
  /br else^(dq("Not handled 2^" + "(state)"))"
do if e ∈ "/br" then acc else acc + e,
acc

use seq.recoveryEntry

Function applySubstitutions(table:PEGtable, intemplate:seq.seq.word) seq.seq.word
for acc = empty:seq.seq.word, p ∈ intemplate
do let tmp = run(table, p), if isempty.tmp then acc else acc + tmp,
acc

function template seq.seq.word
[
 "function = (seq.word, attribute2) boolean true"
 , "function = (seq.word, seqElementType) boolean true"
 , "use standard"
 , "use seq.tblEle"
 , "use otherseq.frame"
 , "use stack.frame"
 , "use otherseq.attribute2"
 , "use PEGrules"
 , "function_(i:int, R:reduction) attribute2 (i+1)_toseq.R"
 , "type tblEle is action:state, match:seqElementType, Sstate:state, Fstate:state"
 , "type reduction is toseq:seq.attribute2"
 , "type frame is Sstate:state, Fstate:state, i:int, result:seq.attribute2, faili:int, failresult:seq.attribute2"
 , "type runresult is stk:stack.frame /trace, trace:seq.word /end"
 , "Function success (a:runresult) boolean Sstate.top.stk.a /ne Fail"
 , "Function result (a:runresult) attribute2 1^result.top.stk.a"
 ,
  "/trace function tracestart (trace:seq.word) seq.word^(dq)"
  + "<* table /row stk top.stk /cell top.stk
   /row depth S F /cell result /cell result /cell Fail / State /cell idx / remaining input $$$ (trace) *>^(dq)"
  + "/end"
 , "/trace function trace (trace0:seq.word, stk:stack.frame, result:seq.attribute2, faili:int, state:state, i:int, input:seq.seqElementType) seq.word let stkdata = %.n.toseq.stk+if isempty.stk then doublequote /cell doublequote else doublequote $$$ (faili.top.stk) $$$ (Sstate.top.stk) $$$ (Fstate.top.stk) /cell $$$ (1^result.top.stk) doublequote, trace0+doublequote
  /row $$$ (stkdata) /cell $$$ (% (doublequote^doublequote, result) >> 1) /cell $$$ (faili) $$$ (state) /cell $$$ (i) $$$ (subseq (input, i, i+20)) doublequote /end"
 ,
  "function parse (myinput:seq.seqElementType, table:seq.tblEle, initAttr:attribute2 /common, common:commonType /end) runresult /br let packedTable = packed.table /common /else let common = 0 /end
   /br for /trace trace0 =^(dq)^(dq), /end /error reduceLen = 0, maxStack = empty:stack.frame, /end stk = empty:stack.frame, state = startstate, i = 1, result = [initAttr], faili = 1, failresult = [initAttr]
   /br while not (index.state = 1 /and action.state = actionReduce /or action.state = Fail /and n.toseq.stk < 2) do
   /br /trace let trace = trace (trace0, stk, result, faili, state, i, (myinput)), /end
   /br let actionState = action.state
   /br if actionState = Fail /or actionState = actionReduce /and not.isempty.stk /and is!.Sstate.top.stk then {goto Fstate.top.stk, i = faili.top, pop.stk, discard result}
   /br let top = top.stk let newstk = pop.stk,
   /br if action.Fstate.top = actionP then next (/trace trace, /end /error reduceLen, maxStack, /end newstk, S.index.Fstate.top, i.top, result.top, faili.top, failresult.top) else
   /br next (/trace trace, /end /error reduceLen, maxStack, /end newstk, if is!.Sstate.top /and state = Fail then Sstate.top else Fstate.top, faili.top, failresult.top, faili.top, failresult.top)
   /br else if actionState = Success* then {goto Sstate.top.stk, pop.stk, keep result} let top = top.stk, next (/trace trace, /end /error reduceLen, maxStack, /end pop.stk, Sstate.top, i, result.top+result, faili.top, failresult.top)
   /br else if actionState = actionDiscard* then next (/trace trace, /end /error reduceLen, maxStack, /end stk, S.index.state, i, result, i, result)
   /br else if actionState = All then let top = top.stk let reduction = [toAttribute (1^result, subseq (myinput, i.top, i-1))], next (/trace trace, /end /error reduceLen, maxStack, /end pop.stk, Sstate.top, i, result.top+reduction, faili.top, failresult.top)
   /br else if actionState = actionReduce then {actionReduce} let top = top.stk, /error if i ≥ reduceLen then
   /br let reduction = [action (index.state, reduction.result, i, myinput, common, stk)] next (/trace trace, /end {reduceLen} i, {maxStack} stk, pop.stk, Sstate.top, i, result.top+reduction, faili.top, failresult.top) else
   /br let reduction = [action (index.state, reduction.result,-reduceLen, myinput, common, maxStack)] /else
   /br let reduction = [action (index.state, reduction.result, i, myinput, common, stk)] /end next (/trace trace, /end /error reduceLen, maxStack, /end pop.stk, Sstate.top, i, result.top+reduction, faili.top, failresult.top)
   /br else let iz = index.state let te = idxNB (packedTable, iz) let actionTe = action.action.te
   /br if actionTe = S.0 then {match non Terminal} let newstk = push (stk, frame (Sstate.te, Fstate.te, i, result, faili, failresult)) let tmp = [toAttribute (1^result, empty:seq.seqElementType)] next (/trace trace, /end /error reduceLen, maxStack, /end newstk, action.te, i, tmp, i, tmp)
   /br else if actionTe = actionReduce then
   /br let reduction = [action (index.action.te, reduction.result, i, myinput, common, stk)]
   /br let top = top.stk, /error let newreducelen = if i ≥ reduceLen then i else reduceLen let newMaxStack = if i ≥ reduceLen then stk else maxStack /end
   /br if faili = i then next (/trace trace, /end /error newreducelen, newMaxStack, /end pop.stk, Sstate.top, i, result.top+reduction, faili.top, failresult.top) else next (/trace trace, /end /error newreducelen, newMaxStack, /end stk, Sstate.te, i, reduction, i, reduction)
   /br else if actionTe = Match then
   /br if i > n.myinput ∨ i_myinput ≠ match.te then
   /br {fail} next (/trace trace, /end /error reduceLen, maxStack, /end stk, Fstate.te, faili, failresult, faili, failresult)
   /br else next (/trace trace, /end /error reduceLen, maxStack, /end stk, Sstate.te, i+1, result, faili, failresult)
   /br else if actionTe = MatchNext then
   /br if i > n.myinput ∨ i_myinput ≠ match.te then
   /br {fail} next (/trace trace, /end /error reduceLen, maxStack, /end stk, Fstate.te, i, result, faili, failresult)
   /br else next (/trace trace, /end /error reduceLen, maxStack, /end stk, Sstate.te, i+1, result, faili, failresult)
   /br else if actionTe = !Match then
   /br if i ≤ n.myinput ∧ i_myinput = match.te then {fail} next (/trace trace, /end /error reduceLen, maxStack, /end stk, Fstate.te, faili, failresult, faili, failresult) else next (/trace trace, /end /error reduceLen, maxStack, /end stk, Sstate.te, i, result, faili, failresult)
   /br else assert actionTe = MatchAny report^(dq) PROBLEM PEG^(dq)
   /br if i > n.myinput then {fail} next (/trace trace, /end /error reduceLen, maxStack, /end stk, Fstate.te, i, result, faili, failresult) else let newresult = if action.Sstate.te = actionDiscard* then result else result+toAttribute (1^"
  + "result, [i_myinput]) next (/trace trace, /end /error reduceLen, maxStack, /end stk, Sstate.te, i+1, newresult, faili, failresult)"
  + "/br runresult (push (/error maxStack /else stk /end, frame (state, state, /error reduceLen /else i /end, result, i, result))
   /br /trace, tracestart.trace0 /end)"
] 