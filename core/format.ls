Module format

use UTF8

use standard

use otherseq.word

use stack.seq.word

use stack.word

Export type:UTF8 {From UTF8}

Export towords(UTF8) seq.word {From textio}

Function htmlheader UTF8
{the format of the meta tag is carefully crafted to get math unicode characters to display
 correctly}
toUTF8."<!doctype html> <meta charset = $(dq."UTF-8") ><style>"
+ toUTF8."<!--span.avoidwrap {display:inline-block ;} span.keyword {color:blue ;}"
+ toUTF8."span.literal {color:red ;} span.comment {color:green ;}"
+ toUTF8."span.block {padding:0px 0px 0px 0px ; margin:0px 0px 0px 20px ; display:block ;}"
+ toUTF8."--> </style>"

___________________

function escape(w:seq.word) word escape.first.w

function escape(w:word) word encodeword([char.0] + decodeword.w)

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
 if last = none then
  next(acc, state, result, stk, this)
 else if last = "*>"_1 then
  if not.isempty.stk then
   if state ∈ [seconddq, firstdq] then
    next(acc + toUTF8.result, 0, top.stk, pop.stk, this)
   else if subseq(top.stk, 1, 1) = "nobreak" then
    next(acc, nobreak, result + top.stk << 1, pop.stk, this)
   else
    next(acc, 0, result + top.stk, pop.stk, this)
  else
   next(acc, 0, result, stk, none)
 else if state ∈ [seconddq, firstdq] then
  if last = dq_1 then
   if state = seconddq then
    next(acc, firstdq, result + last, stk, this)
   else
    next(acc, seconddq, result + last + bs, stk, this)
  else if last = "/br"_1 then
   next(acc, state, result + LF, stk, this)
  else
   next(acc, state, result + last, stk, this)
 else if last = "/keyword"_1 then
  next(acc
   , state
   , result + "$(escape."<span") class = keyword>" + this + bs
   + escape."</span>"
   , stk
   , none)
 else if last = "/em"_1 then
  next(acc, state, result + [escape."<em>", this, escape."</em>"], stk, none)
 else if last = "/strong"_1 then
  next(acc
   , state
   , result + escape."<strong>" + this + escape."</strong>"
   , stk
   , none)
 else if last = "/sw"_1 then
  next(acc, state, result + escape.this, stk, none)
 else if last = "/so"_1 then
  next(acc, state, result + escape.this + bs, stk, none)
 else if last = "/sc"_1 then
  next(acc, state, result + bs + escape.this, stk, none)
 else if last = "/sn"_1 then
  next(acc, state, result + bs + escape.this + bs, stk, none)
 else if last = "/p"_1 then
  next(acc, state, result + LF + escape."<p>", stk, this)
 else if last = "/row"_1 then
  if not.isempty.stk ∧ top.stk = [escape."</caption>"] then
   next(acc
    , state
    , result + LF + (top.stk + escape."<tr>" + escape."<td>")
    , pop.stk
    , this)
  else
   next(acc, state, result + LF + escape."<tr>" + escape."<td>", stk, this)
 else if last = "/cell"_1 then
  next(acc, state, result + LF + escape."<td>", stk, this)
 else if last = "/br"_1 then
  if this = "<*"_1 then
   next(acc, pendingbreak, result, stk, this)
  else
   next(acc
    , if state = nobreak then 0 else state
    , if state = nobreak then result else result + LF + escape."<br>" + space
    , stk
    , this)
 else if last = "<*"_1 then
  let pb = if state = pendingbreak then result + [LF, escape."<br>", space] else result
  if this = "none"_1 then
   next(acc + toUTF8(result, true), firstdq, empty:seq.word, push(stk, ""), none)
  else if this = "section"_1 then
   next(acc
    , state
    , pb + [LF, escape."<h2>", space]
    , push(stk, [escape."</h2>"])
    , none)
  else if this = "table"_1 then
   next(acc
    , state
    , pb + [escape."<table>", space, escape."<caption>"]
    , push(push(stk, [escape."</table>"]), [escape."</caption>"])
    , none)
  else
   next(acc
    , state
    , pb + "$(escape."<span") class = $(this) >"
    , push(stk, [escape."</span>"])
    , none)
 else
  next(acc, state, result + last, stk, this)
/for (acc + toUTF8(if last = none then result else result + [last], false))

Function textformat(a:seq.word) UTF8
let bs = encodeword.[char.8]
let LF = encodeword.[char.10]
let none = merge."+NONE"
let firstdq = 1
let seconddq = 2
let pendingLine = 3
for indent = 0
 , state = 0
 , result = empty:seq.word
 , stk = empty:stack.word
 , last = none
 , this ∈ a + space
do
 if last = none then
  next(indent, state, result, stk, this)
 else if last = "*>"_1 then
  if not.isempty.stk then
   if state ∈ [seconddq, firstdq] then
    next(indent - 1, 0, result, pop.stk, this)
   else if top.stk ∈ "block" then
    next(indent - 1, pendingLine, result, pop.stk, this)
   else
    next(indent - 1, 0, result, pop.stk, this)
  else
   next(indent, 0, result, stk, none)
 else if state ∈ [seconddq, firstdq] then
  if last = dq_1 then
   if state = seconddq then
    next(indent, firstdq, result + last, stk, this)
   else
    next(indent, seconddq, result + last + bs, stk, this)
  else if last = "/br"_1 then
   next(indent, state, result + LF, stk, this)
  else
   next(indent, state, result + last, stk, this)
 else if last = "/br"_1 then
  next(indent
   , 0
   , if state = pendingLine then result + LF else result /if + LF
   + constantseq(indent, space)
   , stk
   , this)
 else if last = "<*"_1 ∧ this = "block"_1 then
  next(indent + 1
   , 0
   , result + LF + constantseq(indent + 1, space)
   , push(stk, this)
   , none)
 else if last = "/p"_1 then
  next(0, 0, result + LF + LF, stk, this)
 else
  let result0 = if state = pendingLine then result + LF + constantseq(indent, space) else result
  let newstate = if state = pendingLine then 0 else state
  if last = "<*"_1 then
   if this = "none"_1 then
    next(indent + 1, firstdq, result0, push(stk, this), none)
   else
    next(indent + 1, newstate, result0, push(stk, this), none)
  else if last ∈ "/keyword /em /strong /cell" then
   next(indent, newstate, result0, stk, this)
  else if last = "/sw"_1 then
   next(indent, newstate, result0 + escape.this, stk, none)
  else if last = "/so"_1 then
   next(indent, newstate, result0 + escape.this + bs, stk, none)
  else if last = "/sc"_1 then
   next(indent, newstate, result0 + bs + escape.this, stk, none)
  else if last = "/sn"_1 then
   next(indent, newstate, result0 + [bs, escape.this, bs], stk, none)
  else if last = "/row"_1 then
   next(indent, newstate, result0 + LF, stk, this)
  else
   next(indent, newstate, result0 + last, stk, this)
/for (toUTF8(if last = none then result else result + last, false)) 