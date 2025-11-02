Module checking

use seq.boolean

use standard

use seq.seq.word

Function check(y:seq.boolean, testname:seq.word) seq.word
for acc = "", i = 1, e ∈ y
do next(acc + (if y sub i then "" else [toword.i]), i + 1),
if acc = "" then "PASS:(testname)"
else "<* literal FAILED *> test:(acc) in:(testname)" 
