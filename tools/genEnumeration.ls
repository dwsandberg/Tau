Module genEnumeration

use bits

use standard

use set.valuename

use seq1.word

function >1(a:valuename, b:valuename) ordering value.a >1 value.b

function isempty(s:seq.word, b:seq.word) seq.word if isempty.s then b else s

Function generateEnum(yy:seq.word) seq.seq.word
let zz = break("," sub 1, subseq(yy, findindex(yy, "[" sub 1) + 1, n.yy - 1))
for auto = empty:seq.seq.word, z ∈ zz
do
 let p = subseq(z, 2, n.z - 1)
 let values = extractValue(p, "names")
 let nameValue = extractValue(p, "nameValue")
 let existingType = extractValue(p, "existingType")
 let newType = extractValue(p, "newType")
 assert(isempty.existingType ∨ isempty.newType) ∧ not.isempty(newType + existingType) report "genEnum: Either existingType: or newType: must specify a type name in:(p)",
 assert not.isempty.values ∨ not.isempty.nameValue report "genEnum: names: or nameValue: must not be empty:(p)",
 auto
 + enumerate(
  newType + existingType
  , values
  , not.isempty.existingType
  , isempty(extractValue(p, "decodeName"), "decode")
  , if not.isempty.existingType ∧ isempty.nameValue then values else nameValue
 ),
auto

type valuename is value:int, name:word

function %(a:valuename) seq.word ":(name.a):(value.a)"

function enumerate(
type:seq.word
, names:seq.word
, existingtype:boolean
, decodename:seq.word
, nameValue:seq.word
) seq.seq.word
let pairs =
 if isempty.nameValue then
  for acc = empty:set.valuename, value = 0, e ∈ names
  do
   if e ∈ "?" then next(acc, value + 1)
   else next(acc + valuename(value, e), value + 1),
  acc
 else
  for acc = empty:set.valuename, isname = true, last = "?" sub 1, e ∈ nameValue
  do
   if isname then next(acc, false, e)
   else next(acc + valuename(toint.e, last), true, e),
  acc
let lowValue = value.pairs sub 1
let highValue = value.(toseq.pairs) sub n.pairs
let cvt =
 if existingtype then if type = "int" then "" else [merge."to:(type)"] + "."
 else type + "."
for acc = empty:seq.seq.word, list = "let discard =[", e ∈ toseq.pairs
do next(acc + "Function:(name.e):(type):(cvt):(value.e)", list + name.e + ",")
let bodypart =
 if n.pairs > 4
 ∧ (highValue - lowValue < 40 ∨ 100 * n.pairs / (highValue - lowValue + 1) > 95) then
  for codes5 = empty:seq.word, last = value.pairs sub 1 - 1, e ∈ toseq.pairs
  do next(codes5 + constantseq(value.e - last - 1, "?" sub 1) + name.e, value.e)
  let tmp = 1 - lowValue,
  let tmp1 =
   if tmp = 0 then "i"else if tmp > 0 then "(i+:(tmp))" else "(i-:(-tmp))",
  "if between(i,:(lowValue),:(highValue))then let r =[:(dq.codes5)sub:(tmp1)], if r ≠:(dq."?")then r else:(dq(type + "."))+toword.i else"
 else
  for txt = "", e ∈ toseq.pairs do txt + "if i =:(value.e)then:(dq.[name.e])else",
  txt
let decodefunc =
 "Function:(decodename)(code::(type))seq.word:(list >> 1)]let i =:(if type = "int" then "" else "toint.")code,:(bodypart):(dq(type + "."))+toword.i",
(if existingtype then empty:seq.seq.word
else
 [
  "type:(type)is toint:int"
  , "Export toint(:(type))int"
  , "Export:(type)(i:int):(type)"
  , "Export type::(type)"
  , "Function =(a::(type), b::(type))boolean toint.a = toint.b"
 ]
)
 + acc
 + decodefunc

function genEnum seq.seq.word
[
 "newType: e1 names: h3 h4 h5"
 , "newType: e2 names: r5 r6"
 , "existingType: int decodeName: d1 nameValue: r3 3 r7 9"
 , "existingType: byte decodeName: ops nameValue: op1 45 op2 97"
 , "existingType: byte decodeName: twodecode nameValue: two0 0 two1 2 two2 4 two3 8 two4 0x10 two5 0x20"
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
if i = 0 then "h3"
else if i = 1 then "h4"
else if i = 2 then "h5"
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
if i = 0 then "r5"else if i = 1 then "r6" else "e2." + toword.i

Function r3 int 3

Function r7 int 9

Function d1(code:int) seq.word
let discard = [r3, r7]
let i = code,
if i = 3 then "r3"else if i = 9 then "r7" else "int." + toword.i

Function op1 byte tobyte.45

Function op2 byte tobyte.97

Function ops(code:byte) seq.word
let discard = [op1, op2]
let i = toint.code,
if i = 45 then "op1"else if i = 97 then "op2" else "byte." + toword.i

Function two0 byte tobyte.0

Function two1 byte tobyte.2

Function two2 byte tobyte.4

Function two3 byte tobyte.8

Function two4 byte tobyte.16

Function two5 byte tobyte.32

Function twodecode(code:byte) seq.word
let discard = [two0, two1, two2, two3, two4, two5]
let i = toint.code,
if between(i, 0, 32) then
 let r =
  [
   "two0 ? two1 ? two2 ? ? ? two3 ? ? ? ? ? ? ? two4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? two5"
   sub (i + 1)
  ],
 if r ≠ "?" then r else "byte." + toword.i
else "byte." + toword.i 