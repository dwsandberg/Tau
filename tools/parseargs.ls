module parseargs

use standard

use seq.seq.word

use process.seq.seq.word

Function testX seq.word
let t = 
 testY("-a 3 4 5-c", "a c", "word words", "Syntax:..-a word-..")
 + testY("-a-c", "a c", "word words", "Syntax:..-a word-..")
 + testY("a b c", "main", "words", "-main a b c")
 + testY("-c", "", "", "Unknown option-c")
 + testY("-c", "c", "words", "-c")
 + testY("-c", "c", "word", "Syntax:..-c word-..")
 + testY("-d 3 4 5", "d main", "word words", "-d 3 |-main 4 5")
 + testY("-c 3 4 5", "c", "words", "-c 3 4 5")
 + testY("-c a b", "c main", "word word", "-c a |-main b")
 + testY("-c-a a b"
 , "c a main"
 , "boolean word words"
 , "-c |-a a |-main b"
 )
 + testY("-a a-c b"
 , "c a main"
 , "boolean word words"
 , "-a a |-c |-main b"
 )
 + testY("a-p b", "main p", "word word", "-main a |-p b")
if isempty.t then"PASS"else"FAIL" + t

function testY(a:seq.word, b:seq.word, c:seq.word, r:seq.word)seq.word
let p = process.parseargs(a, b, c)
let z = 
 if aborted.p then message.p
 else
  for txt = "", pa ∈ result.p do txt + "|" + pa /for(txt << 1)
if z = r then""else" /br" + z + "expected" + r

Function parseargs(otherargs:seq.word, validargs:seq.word, argtypes:seq.word)seq.seq.word
let b0 = 
 break(subseq(otherargs, 1, findindex(first."#", otherargs) - 1), "-", true)
let b2 = 
 if isempty.last.b0 ∨ first.last.b0 ∉ "-"then["-main" + last.b0]
 else
  {there is at least one option. if first.b0 is not an option make it a-main option}
  let b = 
   if isempty.first.b0 then b0 << 1
   else if first.first.b0 ∉ "-"then["-main" + first.b0] + b0 << 1 else b0
  if length.last.b < 2 ∨ first.last.b ∉ "-" ∨ (last.b)_2 ∉ validargs then
   {last option is not a vaild option}b
  else
   let t = argtypes_findindex((last.b)_2, validargs)
   if t = first."words"then b
   else
    let i = if t = first."word"then 3 else 2
    let main = last.b << i
    b >> 1 + subseq(last.b, 1, i)
    + if isempty.main then empty:seq.seq.word else["-main" + main]
let discard = 
 for acc = "", p ∈ b2 do
  let i = findindex(p_2, validargs)
  assert i ≤ length.validargs report"Unknown option" + p
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