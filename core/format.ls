Module format

use UTF8

use bits

use seq.byte

use seq.seq.char

use standard

use stack.seq.word

use stack.word

Export type:UTF8 {From UTF8}

Export towords(UTF8) seq.word {From textio}

Function htmlheader UTF8
{the format of the meta tag is carefully crafted to get math unicode characters to display correctly}
toUTF8."<!doctype html> <meta charset = $(dq."UTF-8") > <style >"
+ toUTF8."<!--span.avoidwrap {display:inline-block ;} span.keyword {color:blue ;}"
+ toUTF8."span.literal {color:red ;} span.comment {color:green ;}"
+ toUTF8."span.block {padding:0px 0px 0px 0px ; margin:0px 0px 0px 20px ; display:block ;}"
+ toUTF8."--> </style>"

___________________

Function tag(w:seq.word) seq.word [encodeword([char.0] + decodeword.first.w)]

Function HTMLformat(a:seq.word) UTF8
{OPTION PROFILE}
let bs = encodeword.[char.8]
let LF = encodeword.[char.10]
let none = merge."+NONE"
let nobreak = 5
let pendingbreak = 4
let firstdq = 1
let seconddq = 2
for acc = emptyUTF8
, state = 0
, result = empty:seq.word
, stk = empty:stack.seq.word
, last = none
, this ∈ a + space
do
 {???? adding" assert false report" here"+%.this" causes invalid record}
 if last = none then next(acc, state, result, stk, this)
 else if last = "/end"_1 then
  if not.isempty.stk then
   if state ∈ [seconddq, firstdq] then
    next(acc + toUTF8.result, 0, top.stk, pop.stk, this)
   else if subseq(top.stk, 1, 1) = "nobreak" then
    next(acc, nobreak, result + top.stk << 1 + "<!╌nobreak╌>", pop.stk, this)
   else next(acc, 0, result + top.stk, pop.stk, this)
  else next(acc, 0, result, stk, none)
 else if state ∈ [seconddq, firstdq] then
  if last = dq_1 then
   if state = seconddq then next(acc, firstdq, result + last, stk, this)
   else next(acc, seconddq, result + last + encodeword.[char.8], stk, this)
  else if last = "/br"_1 then next(acc, state, result + LF, stk, this)
  else next(acc, state, result + last, stk, this)
 else if last = "/keyword"_1 then
  next(acc
  , state
  , result + "$(tag."<span") class = keyword>" + this + bs + tag."</span>"
  , stk
  , none
  )
 else if last = "/em"_1 then
  next(acc, state, result + (tag."<em>" + this + tag."</em>"), stk, none)
 else if last = "/strong"_1 then
  next(acc
  , state
  , result + (tag."<strong>" + this + tag."</strong>")
  , stk
  , none
  )
 else if last = "/sw"_1 then
  next(acc, state, result + encodeword([char.0] + decodeword.this), stk, none)
 else if last = "/so"_1 then
  next(acc
  , state
  , result + encodeword([char.0] + decodeword.this) + encodeword.[char.8]
  , stk
  , none
  )
 else if last = "/sc"_1 then
  next(acc
  , state
  , result + encodeword.[char.8] + encodeword([char.0] + decodeword.this)
  , stk
  , none
  )
 else if last = "/sn"_1 then
  next(acc
  , state
  , result + encodeword.[char.8] + encodeword([char.0] + decodeword.this)
  + encodeword.[char.8]
  , stk
  , none
  )
 else if last = "/p"_1 then next(acc, state, result + LF + tag."<p>", stk, this)
 else if last = "/row"_1 then
  if not.isempty.stk ∧ top.stk = tag."</caption>" then
   next(acc
   , state
   , result + LF + (top.stk + tag."<tr>" + tag."<td>")
   , pop.stk
   , this
   )
  else next(acc, state, result + LF + tag."<tr>" + tag."<td>", stk, this)
 else if last = "/cell"_1 then
  next(acc, state, result + LF + tag."<td>", stk, this)
 else if last = "/br"_1 then
  if this = "/fmt"_1 then next(acc, pendingbreak, result, stk, this)
  else
   next(acc
   , if state = nobreak then 0 else state
   , if state = nobreak then result else result + LF + tag."<br>" + space
   , stk
   , this
   )
 else if last = "/fmt"_1 then
  if this = "block"_1 then
   {if break is just before block suppress break}
   next(acc
   , 0
   , result + (tag."<span" + "class = block>" + space)
   , push(stk, "nobreak $(tag."</span>")")
   , none
   )
  else
   let pb = if state = pendingbreak then result + LF + (tag."<br>" + space) else result
   if this = "none"_1 then
    next(acc + toUTF8(result, true), firstdq, empty:seq.word, push(stk, ""), none)
   else if this = "section"_1 then
    next(acc
    , state
    , pb + LF + (tag."<h2>" + space)
    , push(stk, tag."</h2>")
    , none
    )
   else if this = "table"_1 then
    next(acc
    , state
    , pb + (tag."<table>" + space + tag."<caption>")
    , push(push(stk, tag."</table>"), tag."</caption>")
    , none
    )
   else
    next(acc
    , state
    , pb + "$(tag."<span") class = $(this) >"
    , push(stk, tag."</span>")
    , none
    )
 else next(acc, state, result + last, stk, this)
/for (acc + toUTF8(if last = none then result else result + [last], false))

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
  else next(state, needsLF, result + encodeword.[char.10] + toseq.stk, stk, this)
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
  next(state, true, result + encodeword.[char.10] + encodeword.[char.10], stk, this)
 else if last = space then next(state, needsLF, result + [space], stk, this)
 else next(state, true, result + [last], stk, this)
/for (toUTF8.if last = none then result else result + [last]) 