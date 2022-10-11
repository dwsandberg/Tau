Module format

use UTF8

use bits

use seq.byte

use seq.seq.char

use standard

use stack.seq.word

use stack.word

Export type:UTF8{From UTF8}

Export towords(UTF8) seq.word {From textio}

Function getheader(s:seq.word) seq.word
let istype = subseq(s, 1, 3) = "Export type:"
let start = 0
let startname = -1
let extendname = -2
let findend = -3
let extendtype = -4
let extendtype2 = -5
let incomment = -6
let unknown = -7
let theend = 
 for state = 0, idx = 1, ele ∈ s
 while state ≤ 0
 do
  next(if state > 0 then state
  else if state = start then startname
  else if state = startname then extendname
  else if state = extendname then
   if ele ∈ ":." then startname
   else if istype then idx - 1 else if ele ∈ "(" then findend else extendtype
  else if state = findend then if ele ∈ ")" then extendtype2 else findend
  else if state = extendtype then
   if ele ∈ "." then extendtype2
   else if ele ∈ "//" then incomment else {done} idx - 1
  else if state = extendtype2 then extendtype
  else if state = incomment then if ele ∈ "//" then extendtype else incomment
  else unknown
  , idx + 1
  )
 /for (if state < 1 then length.s else state)
if istype then
 let tt = subseq(s, 4, theend)
 subseq(s, 1, theend) + "(" + tt + ")" + tt + "stub"
else subseq(s, 1, theend) + "stub"

type pnpstate is lastbreak:int, result:seq.word, matchthis:word, instring:boolean

Function prettynoparse(s:seq.word) seq.word
{format function without first parsing it}
result.for acc = pnpstate(0, "", "//"_1, false), @e ∈ s do advancepnp(acc, @e) /for (acc)

function advancepnp(state:pnpstate, this:word) pnpstate
let lastbreak = lastbreak.state
let result = result.state
let matchthis = matchthis.state
let instring = instring.state
let newinstring = if instring then this ≠ matchthis else this = "//"_1 ∨ this = dq_1
let newmatchthis = if instring then matchthis else this
let c = 
 if newinstring then 0
 else if this ∈ "if then else let assert function Function type" then 1
 else if this ∈ "report" then 2
 else if lastbreak > 20 ∧ this ∈ ")]" ∨ lastbreak > 40 ∧ this ∈ "," then
  3
 else if lastbreak > 20 ∧ this ∈ "[" then 4 else 5
let newresult = 
 if instring then
  if this = matchthis then result + this + "/end" else result + this
 else if c = 0 then
  result + if this ∈ dq then "/fmt literal" else "/br /fmt comment" /if + this
 else if c = 1 then
  if lastbreak > 20 then result + "/br" else result /if + "/keyword" + this
 else if c = 2 then result + "/keyword" + this
 else if c = 3 then result + this + "/br"
 else if c = 4 then result + "/br" + this else result + this
let newlastbreak = if c ∈ [3, 4] then 0 else lastbreak + 1
pnpstate(newlastbreak, newresult, newmatchthis, newinstring)

_____________________________

Function htmlheader seq.word
{the format of the meta tag is carefully crafted to get math unicode characters to display correctly}
"<!doctype html> <meta charset = $(dq."UTF-8") >
 /br <style > <!--span.avoidwrap {display:inline-block ;} span.keyword {color:blue ;
 }
 /br span.keywords {color:blue ;} span.literal {color:red ;} span.comment {color:green
 ;}
 /br span.block {padding:0px 0px 0px 0px ; margin:0px 0px 0px 20px ; display:block ;}
 /br--> </style>
 /br"

___________________

/function+(result:UTF8, toadd:seq.word) UTF8 if isempty.toadd then result else let nospace
= isempty.toseqbyte.result ∨ toint.last.toseqbyte.result ∈ [10, 32, 34, 40, 41, 43,
45, 46, 58, 61, 91, 93, 94, 95, 123, 125] result+toUTF8 (toadd, false, nospace)

Function HTMLformat(a:seq.word) UTF8
let bs = encodeword.[char.8]
let LF = encodeword.[char.10]
let none = merge."+NONE"
let match = merge."+MaTcH"
let pendingbreak = merge."+pendingBreak"
for state = 0
, result = empty:seq.word
, stk = empty:stack.seq.word
, last = none
, this ∈ a + space
do
 if last = match then
  if this = "/fmt"_1 then
   next(state, result + [this], push(stk, [this]), match)
  else if this = "/end"_1 then
   if not.isempty.stk ∧ top.stk = "/fmt" then
    next(0, result + [this], pop.stk, match)
   else next(state, result, stk, none)
  else if state > 0 ∧ this = dq_1 then
   if state = 2 then next(1, result + this, stk, last)
   else next(2, result + this + encodeword.[char.8], stk, last)
  else next(state, result + [this], stk, last)
 else if last = none then next(state, result, stk, this)
 else if last = "/keyword"_1 then
  next(state
  , result + "<span class = keyword>" + this + bs + "</span>"
  , stk
  , none
  )
 else if last = "/em"_1 then
  next(state, result + ("<em>" + this + "</em>"), stk, none)
 else if last = "/strong"_1 then
  next(state, result + ("<strong>" + this + "</strong>"), stk, none)
 else if last = "/p"_1 then next(state, result + LF + "<p>", stk, this)
 else if last = "/row"_1 then
  if not.isempty.stk ∧ top.stk = "</caption>" then
   next(state, result + LF + (top.stk + "<tr><td>"), pop.stk, this)
  else next(state, result + LF + "<tr><td>", stk, this)
 else if last = "/cell"_1 then next(state, result + LF + "<td>", stk, this)
 else if last = "/br"_1 then
  if this ≠ "/fmt"_1 then
   next(state, result + LF + "<br>" + space, stk, this)
  else next(state, result, stk, pendingbreak)
 else if last = "/fmt"_1 ∨ last = pendingbreak then
  if this = "block"_1 then
   {if break is just before block suppress break}
   next(state
   , result + ("<span class = block>" + space)
   , push(stk, "</span>")
   , none
   )
  else
   let pb = if last = pendingbreak then result + LF + ("<br>" + space) else result
   if this = "none"_1 then next(1, result, stk, match)
   else if this = "/section"_1 then
    next(state, pb + LF + ("<h2>" + space), push(stk, "</h2>"), none)
   else if this = "table"_1 then
    next(state
    , pb + ("<table>" + space + "<caption>")
    , push(push(stk, "</table>"), "</caption>")
    , none
    )
   else
    next(state
    , pb + ("<span class =" + this + ">")
    , push(stk, "</span>")
    , none
    )
 else if last = "/end"_1 ∧ not.isempty.stk then
  let toadd = top.stk + space
  next(state
  , result + toadd
  , pop.stk
  , if this = first."/br" then none else this
  )
 else next(state, result + last, stk, this)
/for (toUTF8.if last = none then result else result + [last])

Function textformat(a:seq.word) UTF8
let none = merge."+NONE"
let match = merge."+MaTcH"
let pendingbreak = merge."+pendingBreak"
for state = 0
, needsLF = false
, result = empty:seq.word
, stk = empty:stack.word
, last = none
, this ∈ a + space
do
 if last = match then
  if this = "/fmt"_1 then
   next(state, needsLF, result + [this], push(stk, this), match)
  else if this = "/end"_1 then
   if not.isempty.stk ∧ top.stk = "/fmt"_1 then
    next(state, needsLF, result + [this], pop.stk, match)
   else next(state, needsLF, result, stk, none)
  else if state > 0 ∧ this = dq_1 then
   if state = 2 then next(1, needsLF, result + this, stk, last)
   else next(2, needsLF, result + this + encodeword.[char.8], stk, last)
  else next(state, needsLF, result + this, stk, last)
 else if last = none then next(state, needsLF, result, stk, this)
 else if last = "/br"_1 then
  if this = "/br"_1 then next(state, needsLF, result, stk, this)
  else
   next(state, needsLF, result + encodeword.[char.10] + toseq.stk, stk, this)
 else if last = "/fmt"_1 then
  if this = "block"_1 then
   if needsLF then
    next(state
    , needsLF
    , result + encodeword.[char.10] + space + toseq.stk
    , push(stk, space)
    , none
    )
   else next(state, needsLF, result, push(stk, space), none)
  else if this = "none"_1 then next(state, needsLF, result, stk, match)
  else next(state, needsLF, result, push(stk, space), none)
 else if last = "/end"_1 ∧ not.isempty.stk then
  next(state, needsLF, result, pop.stk, this)
 else if last ∈ "/keyword /em /strong" then next(state, needsLF, result, stk, this)
 else if last = "/p"_1 then
  next(state
  , true
  , result + encodeword.[char.10] + encodeword.[char.10]
  , stk
  , this
  )
 else if last = space then next(state, needsLF, result + [space], stk, this)
 else next(state, true, result + [last], stk, this)
/for (toUTF8.if last = none then result else result + [last]) 