Module backparse

use standard

use symbol

use otherseq.symbol

Function backparse3(s:seq.symbol, ii:int, includeDefine:boolean) int
let i = addDefine(s, ii)
assert i > 0 report "back parse 1a:^(s)^(stacktrace)",
if isblock.i#s then
matchblock(s, i - 1, 0)
else
 for k = i, j ∈ constantseq(nopara.i#s, 1) do backparse3(s, k - 1, includeDefine)
 let z = if includeDefine then addDefine(s, k) else k
 {assert includeDefine /or ii /ne 4 report" KL2^(i)^(ii)^(z)::"+%.subseq (s, 1, ii)}
 z

function matchblock(s:seq.symbol, i:int, nest:int) int
let sym = i#s,
if isblock.sym then
matchblock(s, i - 1, nest + 1)
else if isstartorloop.sym then
 if nest = 0 then
  if isloopblock.sym then
  for k = i, j ∈ constantseq(nopara.sym, 1) do backparse3(s, k - 1, false), k
  else addDefine(s, i)
 else matchblock(s, i - 1, nest - 1)
else matchblock(s, i - 1, nest)

function addDefine(s:seq.symbol, i:int) int
if i > 1 ∧ isdefine.(i - 1)#s then addDefine(s, backparse3(s, i - 2, false)) else i 