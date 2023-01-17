Module checking

use seq.boolean

use standard

Function check(y:seq.boolean, testname:seq.word) seq.word
let x = 
 for acc = "", i = 1, e ∈ y do
  next(acc + if y_i then "" else [toword.i], i + 1)
 /do acc
,
if x = "" then "PASS $(testname)" else "<* literal FAILED *> test $(x) in $(testname)" 