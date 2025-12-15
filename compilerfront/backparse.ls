Module backparse

use standard

use seq1.symbol

use symbol1

Function backparse3(s:seq.symbol, ii:int, includeDefine:boolean) int
let i = if true then addDefine(s, ii) else ii
assert i > 0 report "back parse 1a::(s):(stacktrace)"
let kind = kind.s sub i,
if kind = kendblock then matchblock(s, i - 1, 0)
else
 let i1 = if kind = kjmp then i - value.s sub i else i
 for k = i1, j ∈ constantseq(nopara.s sub i1, 1) do backparse3(s, k - 1, includeDefine),
 if includeDefine then addDefine(s, k) else k

function matchblock(s:seq.symbol, i:int, nest:int) int
let sym = s sub i
let kind = kind.sym
let newnest =
 if kind ∈ [kloop, kstart] then nest - 1
 else if kind = kendblock then nest + 1
 else nest,
if nest = 0 then
 if kind = kloop then
  for k = i, j ∈ constantseq(nopara.sym, 1) do backparse3(s, k - 1, false),
  k
 else if kind = kstart then addDefine(s, i)
 else matchblock(s, i - 1, newnest)
else matchblock(s, i - 1, newnest)

function addDefine(s:seq.symbol, i:int) int
if i > 1 ∧ kind.s sub (i - 1) = kdefine then addDefine(s, backparse3(s, i - 2, false))
else i 