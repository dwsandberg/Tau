Module genEnumeration

use bits

use standard

use otherseq.word

use sparseseq.word

function isempty(s:seq.word, b:seq.word) seq.word if isempty.s then b else s

Function generateEnum(yy:seq.word) seq.seq.word
let zz = break(1_",", subseq(yy, findindex(yy, 1_"[") + 1, n.yy - 1))
for auto = empty:seq.seq.word, z ∈ zz
do
 let p = subseq(z, 2, n.z - 1)
 {???? add check to for first work in existingType newTYpe and other checks}
  auto
  + enumerate(
   extractValue(p, [1_p])
   , extractValue(p, "values")
   , 1_p ∈ "existingType"
   , isempty(extractValue(p, "decodeName"), "decode")
  )
,
auto

function enumerate(
 type:seq.word
 , codes0:seq.word
 , existingtype:boolean
 , decodename:seq.word
) seq.seq.word
let codes =
 if existingtype then
  for acc = sparseseq.1_"?", state = 1, code = 1_codes0, w ∈ codes0 << 1
  do
   if state = 1 then
   next(replaceS(acc, toint.w + 1, [code]), 0, code)
   else next(acc, 1, w)
  for txt = "", e ∈ acc do txt + e,
  txt
 else codes0
,
(
 if existingtype then
 empty:seq.seq.word
 else [
  "type^(type) is toint:int"
  , "Export toint (^(type)) int"
  , "Export^(type) (i:int)^(type)"
  , "Export type:^(type)"
  , "Function = (a:^(type), b:^(type)) boolean toint.a = toint.b"
 ]
)
 + 
 for acc = empty:seq.seq.word, list = "let discard = [", i ∈ arithseq(n.codes, 1, 1)
 do
  if i_codes = 1_"?" then
  next(acc, list)
  else next(
   let cvt =
    if existingtype then
    if type = "int" then "" else [merge."to^(type)"] + "."
    else type + "."
   ,
   acc + "Function^(i_codes)^(type)^(cvt)^(i - 1)"
   , list + i_codes + ","
  )
 ,
  acc
  + (
   "Function^(decodename) (code:^(type)) seq.word^(list >> 1)] let i =^(if type = "int" then "" else "toint.")"
   + "code, if between (i+1, 1,"
   + toword.n.codes
   + ") then let r = [(i+1)_^(dq.codes)],"
   + "if r ≠^(dq."?") then r else^(dq(type + "."))+toword.i else^(dq(type + "."))"
   + "+toword.i"
  )

function genEnum seq.seq.word
[
 "newType = e1 values = h3 h4 h5"
 , "newType = e2 values = r5 r6"
 , "existingType = int decodeName = d1 values = r3 3 r7 9"
 , "existingType = byte decodeName = ops values = op1 45 op2 97"
 , "existingType = byte decodeName = twodecode values = two0 0 two1 2 two2 4 two3 8 two4 0x10 two5 0x20"
]

<<<< Below is auto generated code >>>>

type e1 is toint:int

Export toint(e1) int

Export e1(i:int) e1

Export type:e1

Function =(a:e1, b:e1) boolean toint.a = toint.b

Function h3 e1 e1.0

Function h4 e1 e1.1

Function h5 e1 e1.2

Function decode(code:e1) seq.word
let discard = [h3, h4, h5]
let i = toint.code,
if between(i + 1, 1, 3) then
let r = [(i + 1)_"h3 h4 h5"], if r ≠ "?" then r else "e1." + toword.i
else "e1." + toword.i

type e2 is toint:int

Export toint(e2) int

Export e2(i:int) e2

Export type:e2

Function =(a:e2, b:e2) boolean toint.a = toint.b

Function r5 e2 e2.0

Function r6 e2 e2.1

Function decode(code:e2) seq.word
let discard = [r5, r6]
let i = toint.code,
if between(i + 1, 1, 2) then
let r = [(i + 1)_"r5 r6"], if r ≠ "?" then r else "e2." + toword.i
else "e2." + toword.i

Function r3 int 3

Function r7 int 9

Function d1(code:int) seq.word
let discard = [r3, r7]
let i = code,
if between(i + 1, 1, 10) then
let r = [(i + 1)_"? ? ? r3 ? ? ? ? ? r7"], if r ≠ "?" then r else "int." + toword.i
else "int." + toword.i

Function op1 byte tobyte.45

Function op2 byte tobyte.97

Function ops(code:byte) seq.word
let discard = [op1, op2]
let i = toint.code,
if between(i + 1, 1, 98) then
 let r = [
  (i + 1)
  _"? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? op1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? op2"
 ],
 if r ≠ "?" then r else "byte." + toword.i
else "byte." + toword.i

Function two0 byte tobyte.0

Function two1 byte tobyte.2

Function two2 byte tobyte.4

Function two3 byte tobyte.8

Function two4 byte tobyte.16

Function two5 byte tobyte.32

Function twodecode(code:byte) seq.word
let discard = [two0, two1, two2, two3, two4, two5]
let i = toint.code,
if between(i + 1, 1, 33) then
 let r = [(i + 1)_"two0 ? two1 ? two2 ? ? ? two3 ? ? ? ? ? ? ? two4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? two5"],
 if r ≠ "?" then r else "byte." + toword.i
else "byte." + toword.i 