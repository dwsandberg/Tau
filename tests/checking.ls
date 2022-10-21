Module checking

use standard

use seq.boolean

Function check(y:seq.boolean, testname:seq.word) seq.word
let x = 
 for acc = "", i = 1, e ∈ y do next(acc + if y_i then "" else [toword.i], i + 1) /for (acc)
if x = "" then "PASS $(testname)"
else "/fmt literal FAILED /end test $(x) in $(testname)" 