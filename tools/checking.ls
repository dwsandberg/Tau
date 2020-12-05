Module checking

use seq.boolean

use stdlib

function check2(l:seq.boolean, i:int)seq.word if l_i then""else [ toword.i]

Function check(y:seq.boolean, testname:seq.word)seq.word
 let x = arithseq(length.y, 1, 1)@@ +("", check2(y, @e))
  if x = ""then"PASS" + testname
  else" &{ literal FAILED  &} test" + x + "in" + testname