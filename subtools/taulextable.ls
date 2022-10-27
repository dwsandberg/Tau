Module taulextable

use standard

use otherseq.seq.word

use otherseq.word

use set.word

type lexaction1 is w:word, tokenno:int, label:word

function tolexaction(next:word, terminals:seq.word) lexaction1
{user supplied procedure to convert a word into a lex action}
{assumes W for word; I for Integer}
if next ∈ dq then lexaction1(next, findindex(terminals, "$wordlist"_1), next)
else if next = merge."/ le" then
 lexaction1(next, findindex(terminals, ">"_1), "≤"_1)
else if next = merge."/ ge" then
 lexaction1(next, findindex(terminals, ">"_1), "≥"_1)
else if next = merge."/ ne" then
 lexaction1(next, findindex(terminals, ">"_1), "≠"_1)
else if next = merge."/ and" then
 lexaction1(next, findindex(terminals, "∧"_1), "∧"_1)
else if next = merge."/ or" then
 lexaction1(next, findindex(terminals, "∨"_1), "∨"_1)
else if next = merge."/ cup" then
 lexaction1(next, findindex(terminals, "*"_1), "∪"_1)
else if next = merge."/ cap" then
 lexaction1(next, findindex(terminals, "*"_1), "∩"_1)
else if next = merge."/ nin" then
 lexaction1(next, findindex(terminals, "-"_1), "∉"_1)
else if next = merge."/ in" then
 lexaction1(next, findindex(terminals, "-"_1), "∈"_1)
else if next = merge."/ xor" then
 lexaction1(next, findindex(terminals, "-"_1), "⊻"_1)
else
 let token = 
  if next ∈ "< > >1 >2 ≤ ≠ ≥" then ">"_1
  else if next ∈ "+-∈ ∉" then "-"_1
  else if next ∈ "* / mod ∪ ∩ \ >> <<" then "*"_1
  else if next ∈ "_^" then "_"_1
  else if next ∈ "⊻" then "∨"_1
  else if next ∈ terminals then next
  else if checkinteger.next ∈ "WORD" then "W"_1 else "I"_1
 let idx = findindex(terminals, token)
 let action = if idx > length.terminals then findindex(terminals, "W"_1) else idx
 lexaction1(next, action, next)

Function lextable(terminals:seq.word) seq.seq.word
{* generate the lextable for the Tau compiler. }
let mostfrequentwords = 
 dq
 + "\, ().:+_seq = a int if-then else Function let word 0 i T] [2 use function mytype empty inst"
let wordstoinclude = 
 mostfrequentwords + terminals
 + "= < > >2 >1 >> << in+-* / mod \_^/in ∈ /ne ≠ /or ∨ /nin ∉ /cup ∪ /and ∧ /cap ∩ /ge ≥ /le ≤ /xor
  ⊻"
let t = 
 for acc = empty:seq.seq.word, w ∈ toseq.asset.wordstoinclude do
  if w ∈ {terminals that are not reserved} "comment wl $wordlist" then acc
  else
   let l = tolexaction(w, terminals)
   let word = 
    if w.l ∈ "/for /if /" then dq.[w.l] + "_1"
    else if (decodeword.w.l)_1 = (decodeword."/"_1)_1 then
     "merge.$(dq("/" + encodeword.subseq(decodeword.w.l, 2, 100)))"
    else if w.l = dq_1 then "dq_1" else dq.[w.l] + "_1"
   let label = if label.l = dq_1 then "dq" else dq.[label.l]
   acc + "token ($(word), $(tokenno.l), attribute:T ($(label)))"
 /for (%(",", alphasort.acc) >> 1)
["function lextable:T seq.token.T {generated by genlex module in tools} [$(t)]"
, "function Wtoken:T int {generated by genlex module in tools} $(findindex(terminals, "W"_1))"
, "function Itoken:T int {generated by genlex module in tools} $(findindex(terminals, "I"_1))"
] 