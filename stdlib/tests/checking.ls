Module checking

use seq.boolean

use standard


Function check(y:seq.boolean, testname:seq.word)seq.word
 let x =  for ( e &in y , acc="",i,false)   acc+if y_i then""else [ toword.i] 
  if x = ""then"PASS" + testname
  else" &{ literal FAILED  &} test" + x + "in" + testname