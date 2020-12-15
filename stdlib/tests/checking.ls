Module checking

use seq.boolean

use standard


Function check(y:seq.boolean, testname:seq.word)seq.word
 let x = y @ +("",  if y_@i then""else [ toword.@i])
  if x = ""then"PASS" + testname
  else" &{ literal FAILED  &} test" + x + "in" + testname