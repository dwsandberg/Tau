Module format4

use UTF8

use bits

use stack.blkstk

use seq1.byte

use seq.byte

use seq.char

use standard

type blkstk is result:UTF8, kind:word

Function textFormat4(s:seq.word) UTF8
{OPTION INLINE
/br nospace means add no space before word}
let newway = false,
if isempty.s then emptyUTF8
else
 for
  prefix = [char.10]
  , stk = empty:stack.blkstk
  , cmd = true
  , result = emptyUTF8
  , Space = false
  , this = s sub 1
  , w ∈ s << 1 + "?"
 do
  let chars = decodeword.this,
  if n.chars = 1 then
   let ch = chars sub 1,
   if ch ∈ (decodeword.merge."+-.:" + char.10 + char.32) then {no Space before or after} next(prefix, stk, cmd, result + chars, false, w)
   else if ch ∈ decodeword.merge.",]}):(dq)" then {no Space before but Space after} next(prefix, stk, cmd, result + chars, true, w)
   else if ch ∈ decodeword.merge."([{" then
    {Space before but no Space after}
    next(
     prefix
     , stk
     , cmd
     , if not.Space then result + chars else result + char.32 + chars
     , false
     , w
    )
   else next(prefix, stk, cmd, if not.Space then result + ch else result + char.32 + ch, true, w)
  else if n.chars = 2 then
   if this ∈ ". : " then {no Space before or after} next(prefix, stk, cmd, result + chars, false, w)
   else if not.cmd then
    let chars2 = if not.Space then result + chars else result + char.32 + chars,
    next(prefix, stk, cmd, chars2, true, w)
   else if this ∈ "/p" then next(prefix, stk, cmd, paragraph.result, false, w)
   else if this ∈ "*>" ∧ not.isempty.stk then
    if kind.top.stk ∈ "block" then
     let R0 = toseqbyte.result.top.stk
     let R1 = toseqbyte.result << n.toseqbyte.result.top.stk,
     let z =
      if isempty.R1 then result
      else if newway then UTF8(toseqbyte.result >> endbreak.toseqbyte.result) + prefix >> 1
      else block(R0, R1),
     next(prefix >> 1, pop.stk, cmd, z, false, w)
    else next(prefix, pop.stk, cmd, result, Space, w)
   else if this ∈ "<*" then
    if w ∈ "table block" then
     let new =
      if w ∈ "block" ∧ newway then if not.haslinebreak.toseqbyte.result then result + prefix + char.32 else result
      else result,
     next(
      if w ∈ "block" then prefix + char.32 else prefix
      , push(stk, blkstk(result, w))
      , cmd
      , new
      , false
      , "/cell" sub 1
     )
    else
     next(
      prefix
      , push(stk, blkstk(result, w))
      , cmd
      , if Space then result + char.32 else result
      , false
      , "/cell" sub 1
     )
   else
    let chars2 = if not.Space then result + chars else result + char.32 + chars,
    next(prefix, stk, cmd, chars2, true, w)
  else if this = escapeformat then next(prefix, stk, not.cmd, result, Space, w)
  else if not.cmd then
   let chars2 = if not.Space then result + chars else result + char.32 + chars,
   next(prefix, stk, cmd, chars2, true, w)
  else if this ∈ "/keyword /em /strong /cell" then next(prefix, stk, cmd, result, Space, w)
  else if this ∈ "/sp" then
   if not.isempty.toseqbyte.result ∧ last.toseqbyte.result = tobyte.32 then next(prefix, stk, cmd, result, false, w)
   else next(prefix, stk, cmd, result + char.32, false, w)
  else if this ∈ "/br" then
   if newway then
    if not.haslinebreak.toseqbyte.result then
     let z = result + if w ∈ "/sp" then prefix + char.32 else prefix,
     next(prefix, stk, cmd, z, false, w)
    else next(prefix, stk, cmd, result, false, w)
   else
    let z = UTF8.linebreak.toseqbyte.result,
    next(prefix, stk, cmd, z, false, w)
  else if this ∈ "/tag" then next(prefix, stk, cmd, result + decodeword.w, false, "/cell" sub 1)
  else
   let chars2 = if not.Space then result + chars else result + char.32 + chars,
   next(prefix, stk, cmd, chars2, true, w),
 result + char.32

function block(R0:seq.byte, R1:seq.byte) UTF8
let body = if last.R1 = tobyte.10 then R1 >> 1 else R1
let init =
 linebreak.R0
  + (if subseq(body, 1, 1) = [tobyte.32] then empty:seq.byte else [tobyte.32])
for acc = init, b ∈ body
do if b = tobyte.10 then acc + b + tobyte.32 else acc + b,
UTF8.linebreak.acc

function haslinebreak(b:seq.byte) boolean endbreak.b > 0

function endbreak(b:seq.byte) int
for a = tobyte.32, count = 0, e ∈ reverse.b
while a = tobyte.32
do next(e, count + 1),
if a ≠ tobyte.10 then 0 else count

function paragraph(ain:UTF8) UTF8
let a = toseqbyte.ain,
ain + if not.haslinebreak.a then [char.10, char.10] else [char.10]

function linebreak(a:seq.byte) seq.byte
if not.haslinebreak.a then a + [tobyte.10] else a 
