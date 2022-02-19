module parseargs

use standard

use seq.seq.word

use process.seq.seq.word

function testX seq.word
testY("-a 3 4 5-c", "a c", "word words", "Syntax:..-a word-..")
+ testY("-a-c", "a c", "word words", "Syntax:..-a word-..")
+ testY("a b c", "", "", "-main a b c")
+ testY("-c", "", "", "Unknown arg-c")
+ testY("-c", "c", "words", "-c")
+ testY("-c", "c", "word", "Syntax:..-c word..")
+ testY("-d 3 4 5", "d", "word", "-d 3 |-main 4 5")
+ testY("-c 3 4 5", "c", "words", "-c 3 4 5")
+ testY("-c a b", "c", "word", "-c a |-main b")
+ testY("-c-a a b", "c a", "boolean word", "-c |-a a |-main b")
+ testY("-a a-c b", "c a", "boolean word", "-a a |-c |-main b")

function testY(a:seq.word, b:seq.word, c:seq.word, r:seq.word)seq.word
let p = process.parseargs(a, b, c)
let z = 
 if aborted.p then message.p
 else
  for txt = "", pa ∈ result.p do txt + "|" + pa /for(txt << 1)
if z = r then""else" /br" + z + "expected" + r

Function parseargs(otherargs:seq.word, validargs:seq.word, argtypes:seq.word)seq.seq.word
let b = break(otherargs, "-", true)
let b2 = 
 if isempty.last.b ∨ first.last.b ∉ "-"then["-main" + first.b]
 else
  assert length.last.b > 1 ∧ first.last.b ∈ "-" ∧ (last.b)_2 ∈ validargs
  report"Unknown arg" + last.b
  let t = argtypes_findindex((last.b)_2, validargs)
  if t = first."words"then b << 1
  else if t = first."word"then
   assert length.last.b > 2 report"Syntax:.." + subseq(last.b, 1, 2) + "word.."
   let i = 3
   subseq(b, 2, length.b - 1) + subseq(last.b, 1, i) + ("-main" + last.b << i)
  else
   let i = 2
   subseq(b, 2, length.b - 1) + subseq(last.b, 1, i) + ("-main" + last.b << i)
let discard = 
 for acc = "", p ∈ b2 >> 1 do
  let i = findindex(p_2, validargs)
  assert i ≤ length.validargs report"Unknown flag" + p
  assert argtypes_i ≠ first."boolean" ∨ length.p = 2
  report"Syntax:..-" + p_2 + "-.."
  assert argtypes_i ≠ first."word" ∨ length.p = 3
  report"Syntax:..-" + p_2 + "word-.."
  assert p_2 ∉ acc report"duplicate arg" + p
  acc + p_2
 /for(acc)
let i = findindex(first."main", validargs)
if(last.b2)_2 ∈ "main" ∧ i ≤ length.argtypes ∧ argtypes_i ∈ "word"then
 assert not.isempty.otherargs report"must have main arg" + otherargs
 b2 >> 1 + subseq(last.b2, 1, 3)
else b2

Function getarg(b:seq.seq.word, name:word)seq.word
for acc = empty:seq.seq.word, p ∈ b while isempty.acc do if p_2 = name then[p << 2]else acc /for(if isempty.acc then""else acc_1 /if)

Function getarg:boolean(b:seq.seq.word, name:word)boolean
for acc = empty:seq.seq.word, p ∈ b while isempty.acc do if p_2 = name then[p << 2]else acc /for(not.isempty.acc) 