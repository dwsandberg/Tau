Module format

use UTF8

use standard

use otherseq.word

use stack.seq.word

use stack.word

Export type:UTF8 {From UTF8}

Export towords(UTF8) seq.word {From textio}

Function htmlheader UTF8
{the format of the meta tag is carefully crafted to get math unicode characters to display correctly}
toUTF8."<!doctype html> <meta charset =^(dq."UTF-8") ><style>"
 + toUTF8."<!--span.avoidwrap {display:inline-block ;} span.keyword {color:blue ;}"
 + toUTF8."span.literal {color:red ;} span.comment {color:green ;}"
 + toUTF8."span.block {padding:0px 0px 0px 0px ; margin:0px 0px 0px 20px ; display:block ;}"
 + toUTF8."--> </style>"

___________________

function escape(w:seq.word) word encodeword([char.0] + decodeword.1_w)

Function HTMLformat(a:seq.word) UTF8
{OPTION XPROFILE}
let LF = {encodeword.[char.10]} ""
let none = merge."+NONE"
let nobreak = 5
let pendingbreak = 4
let escape = 6
for
 acc = emptyUTF8
 , state = 0
 , result = empty:seq.word
 , stk = empty:stack.seq.word
 , last = none
 , this ∈ a + space
do
 if last = none then
 next(acc, state, result, stk, this)
 else if last = escapeformat then
 next(acc, if state = escape then 0 else escape, result + last, stk, this)
 else if state = escape then
 next(acc, escape, result + last, stk, this)
 else if last = 1_"*>" then
  if not.isempty.stk then
   if subseq(top.stk, 1, 1) = "nobreak" then
   next(acc, nobreak, result + top.stk << 1, pop.stk, this)
   else next(acc, 0, result + top.stk, pop.stk, this)
  else next(acc, 0, result, stk, none)
 else if last = 1_"/keyword" then
 next(
  acc
  , state
  , result + "^(escape."<span") class = keyword>" + this + "/nosp" + escape."</span>"
  , stk
  , none
 )
 else if last = 1_"/em" then
 next(acc, state, result + [escape."<em>", this, escape."</em>"], stk, none)
 else if last = 1_"/strong" then
 next(acc, state, result + escape."<strong>" + this + escape."</strong>", stk, none)
 else if last = 1_"/p" then
 next(acc, state, result + LF + escape."<p>", stk, this)
 else if last = 1_"/row" then
  if not.isempty.stk ∧ top.stk = [escape."</caption>"] then
  next(acc, state, result + LF + (top.stk + escape."<tr>" + escape."<td>"), pop.stk, this)
  else next(acc, state, result + LF + escape."<tr>" + escape."<td>", stk, this)
 else if last = 1_"/cell" then
 next(acc, state, result + LF + escape."<td>", stk, this)
 else if last = 1_"/br" then
  if this = 1_"<*" then
  next(acc, pendingbreak, result, stk, this)
  else next(
   acc
   , if state = nobreak then 0 else state
   , if state = nobreak then result else result + LF + escape."<br>" + space
   , stk
   , this
  )
 else if last = 1_"<*" then
  let pb = if state = pendingbreak then result + LF + [escape."<br>", space] else result,
   if this = 1_"section" then
   next(acc, state, pb + LF + [escape."<h2>", space], push(stk, [escape."</h2>"]), none)
   else if this = 1_"table" then
   next(
    acc
    , state
    , pb + [escape."<table>", space, escape."<caption>"]
    , push(push(stk, [escape."</table>"]), [escape."</caption>"])
    , none
   )
   else next(
    acc
    , state
    , pb + "^(escape."<span") class =^(this) >"
    , push(stk, [escape."</span>"])
    , none
   )
 else next(acc, state, result + last, stk, this)
,
acc + toUTF83(if last = none then result else result + [last], true)

Export escapeformat word {From UTF8}

Function textformat(a:seq.word) UTF8
let LF = encodeword.[char.10]
let none = merge."+NONE"
let pendingLine = 3
let escape = 4
for
 acc = emptyUTF8
 , indent = 0
 , state = 0
 , result = empty:seq.word
 , stk = empty:stack.word
 , last = none
 , this ∈ a + space
do
 if last = none then
 next(acc, indent, state, result, stk, this)
 else if last = escapeformat then
 next(acc, indent, if state = escape then 0 else escape, result + last, stk, this)
 else if state = escape then
 next(acc, indent, escape, result + last, stk, this)
 else if last = 1_"*>" then
  if not.isempty.stk then
   if top.stk ∈ "block" then
   next(acc, indent - 1, pendingLine, result, pop.stk, this)
   else next(acc, indent - 1, 0, result, pop.stk, this)
  else next(acc, indent, 0, result, stk, none)
 else if last = 1_"/br" then
 next(
  acc
  , indent
  , 0
  , (if state = pendingLine then result + LF else result) + LF + constantseq(indent, space)
  , stk
  , this
 )
 else if last = 1_"<*" ∧ this = 1_"block" then
 next(acc, indent + 1, 0, result + LF + constantseq(indent + 1, space), push(stk, this), none)
 else if last = 1_"/p" then
 next(acc, 0, 0, result + LF + LF, stk, this)
 else
  let result0 = if state = pendingLine then result + LF + constantseq(indent, space) else result
  let newstate = if state = pendingLine then 0 else state,
   if last = 1_"<*" then
   next(acc, indent + 1, newstate, result0, push(stk, this), none)
   else if last ∈ "/keyword /em /strong /cell" then
   next(acc, indent, newstate, result0, stk, this)
   else if last = 1_"/row" then
   next(acc, indent, newstate, result0 + LF, stk, this)
   else next(acc, indent, newstate, result0 + last, stk, this)
,
acc + toUTF83(if last = none then result else result + last, false) 