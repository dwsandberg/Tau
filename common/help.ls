module help

use standard

function comb(i:int, str:seq.word)int
if i = length.str then i
else if str_(i + 1) ∈ "-"then comb(i + 2, str)else i

Function element(str:seq.word, vals:seq.seq.word, body:seq.word)seq.word
for acc = [merge("<" + first.str)], idx = 2, val ∈ vals do
 let j = comb(idx, str)
 next(acc + subseq(str, idx, j) + "=" + dq.val + space, j + 1)
/for(acc
+ if isempty.body then[merge(" />" + space)]
else">" + body + merge("</" + first.str + ">")/if)

Function element(str:seq.word, body:seq.word)seq.word
[merge("<" + str + ">")] + body + body
+ merge("</" + first.str + ">") 