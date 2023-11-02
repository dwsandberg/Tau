Module textio

use UTF8

use seq.UTF8

use bits

use otherseq.byte

use seq.int

use standard

use seq.word

use seq.seq.word

Function breaklines(a:UTF8) seq.UTF8 breaklines(toseqbyte.a, 2, 1, empty:seq.UTF8)

Function breaklines(a:seq.byte) seq.UTF8 breaklines(a, 2, 1, empty:seq.UTF8)

function breaklines(a:seq.byte, i:int, last:int, result:seq.UTF8) seq.UTF8
if i > n.a then
result
else if toint.i#a = 10 then
breaklines(
 a
 , i + 1
 , i + 1
 , result + UTF8.subseq(a, last, i - if toint.(i - 1)#a = 13 then 2 else 1)
)
else breaklines(a, i + 1, last, result)

Function breakcommas(a:UTF8) seq.UTF8
for
 acc = empty:seq.UTF8
 , @e ∈ break(tobyte.toint.char1.",", [tobyte.toint.char1.dq], toseqbyte.a)
do acc + UTF8.@e,
acc

Function breakparagraph(input:seq.byte) seq.seq.word
{breaks file into seq of paragraphs}
let Kother = 0
let Kstandalone = 3
let Kspace = 1
let Klf = 2
let M = 1024
let classify = [
 1
 , 2
 , 3
 , 4
 , 5
 , 6
 , 7
 , 8
 , 9
 , Klf * M
 , 11
 , 12
 , Kspace * M
 , 14
 , 15
 , 16
 , 17
 , 18
 , 19
 , 20
 , 21
 , 22
 , 23
 , 24
 , 25
 , 26
 , 27
 , 28
 , 29
 , 30
 , 31
 , Kspace * M
 , 33
 , Kstandalone * M + 5
 , Kstandalone * M + 15
 , 36
 , 37
 , 38
 , 39
 , Kstandalone * M + 6
 , Kstandalone * M + 7
 , 42
 , Kstandalone * M + 8
 , Kstandalone * M + 9
 , Kstandalone * M + 10
 , Kstandalone * M + 1
 , 47
 , 48
 , 49
 , 50
 , 51
 , 52
 , 53
 , 54
 , 55
 , 56
 , 57
 , Kstandalone * M + 3
 , 59
 , 60
 , Kstandalone * M + 11
 , 62
 , 63
 , 64
 , 65
 , 66
 , 67
 , 68
 , 69
 , 70
 , 71
 , 72
 , 73
 , 74
 , 75
 , 76
 , 77
 , 78
 , 79
 , 80
 , 81
 , 82
 , 83
 , 84
 , 85
 , 86
 , 87
 , 88
 , 89
 , 90
 , Kstandalone * M + 12
 , 92
 , Kstandalone * M + 13
 , Kstandalone * M + 14
 , 95
 , 96
 , 97
 , 98
 , 99
 , 100
 , 101
 , 102
 , 103
 , 104
 , 105
 , 106
 , 107
 , 108
 , 109
 , 110
 , 111
 , 112
 , 113
 , 114
 , 115
 , 116
 , 117
 , 118
 , 119
 , 120
 , 121
 , 122
 , Kstandalone * M + 16
 , 124
 , Kstandalone * M + 17
 , 126
 , 127
]
for
 result = empty:seq.seq.word
 , words = empty:seq.word
 , bytes = empty:seq.byte
 , thisclass = Kspace * M
 , this = tobyte.32
 , b ∈ input + [tobyte.10, tobyte.10]
do
 let nextclass =
  if not.between(toint.b, 1, n.classify) then
  toint.b
  else let t = toint.b {t#classify} idxNB(classify, t)
 let KEY = tobits.thisclass >> 8 ∨ tobits.nextclass >> 10,
  if KEY = KEY(Klf, Kspace) then
  next(result, words, bytes, thisclass, this)
  else if KEY = KEY(Klf, Klf) then
  next(
   if isempty.words then result else result + words
   , empty:seq.word
   , empty:seq.byte
   , nextclass
   , b
  )
  else if KEY = KEY(Kother, Kother) then
  next(result, words, bytes + this, nextclass, b)
  else if KEY = KEY(Kother, Klf) ∨ KEY = KEY(Kother, Kspace) ∨ KEY = KEY(Kother, Kstandalone) then
  next(result, words + encodeword.decodeUTF8.UTF8(bytes + this), empty:seq.byte, nextclass, b)
  else if KEY = KEY(Kstandalone, Kspace) then
   let j = thisclass - Kstandalone * M
   let k = if j < 4 ∧ b = tobyte.32 then j + 1 else j,
   next(
    result
    , words + idxNB(".. :: ^(dq) ()+,-= []^#{}", k)
    , empty:seq.byte
    , nextclass
    , b
   )
  else if
   KEY = KEY(Kstandalone, Kother)
    ∨ KEY = KEY(Kstandalone, Klf)
    ∨ KEY = KEY(Kstandalone, Kstandalone)
  then
   let k = thisclass - Kstandalone * M,
   next(
    result
    , words + idxNB(".. :: ^(dq) ()+,-= []^#{}", k)
    , empty:seq.byte
    , nextclass
    , b
   )
  else next(result, words, bytes, nextclass, b),
result

function KEY(a:int, b:int) bits tobits(a * 4 + b)

Function towords(a:UTF8) seq.word
{assumes no paragraph breaks in a}
let b = breakparagraph.toseqbyte.a,
if isempty.b then empty:seq.word else 1#b 