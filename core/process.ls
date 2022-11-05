Module process.T

use seq.T

use UTF8

use bits

use otherseq.byte

use standard

Export type:process.T

Export body2(process.T) T

Export header(a:process.T) UTF8

type process is abortedx:boolean, msg:seq.word, header:UTF8, body1:seq.T, body2:T

Builtin aborted(process.T) boolean

Function message(p:process.T) seq.word
if aborted.p then
 if isempty.msg.p then
  let h = toseqbyte.header.p
  towords.UTF8.subseq(h, 1, findindex(h, tobyte.10))
 else
  msg.p
else
 "normal exit"

Function result(p:process.T) T
assert not.aborted.p report "no result of aborted process"
first.body1.p

Function merge(a:process.T, b:T, c:T) process.T
process(abortedx.a, msg.a, header.a, [b], c) 