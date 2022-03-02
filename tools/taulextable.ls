Module taulextable

use UTF8

use standard

use seq.char

use seq.lexaction1

use otherseq.word

use set.word

use seq.seq.word

type lexaction1 is w:word, tokenno:int, label:word

Function hasdigit(w:word)boolean
let l = tointseq.decodeword.w
between(l_1, 48, 57) ∨ l_1 = toint.hyphenchar ∧ length.l > 1 ∧ between(l_2, 48, 57)

function terminals seq.word".=():>]-for * comment, [_/if is I if # then else let assert report ∧ ∨ $wordlist while /for W do"

function tolexaction(next:word)lexaction1
{user supplied procedure to convert a word into a lex action}
{assumes W for word I for Integer and comments map to 'comment'}
if next ∈ (dq + singlequote)then lexaction1(next, findindex("$wordlist"_1, terminals), next)
else if next = merge("/" + "le")then
 lexaction1(next, findindex(">"_1, terminals), "≤"_1)
else if next = merge("/" + "ge")then
 lexaction1(next, findindex(">"_1, terminals), "≥"_1)
else if next = merge("/" + "ne")then
 lexaction1(next, findindex(">"_1, terminals), "≠"_1)
else if next = merge("/" + "and")then
 lexaction1(next, findindex("∧"_1, terminals), "∧"_1)
else if next = merge("/" + "or")then
 lexaction1(next, findindex("∨"_1, terminals), "∨"_1)
else if next = merge("/" + "cup")then
 lexaction1(next, findindex("*"_1, terminals), "∪"_1)
else if next = merge("/" + "cap")then
 lexaction1(next, findindex("*"_1, terminals), "∩"_1)
else if next = merge("/" + "nin")then
 lexaction1(next, findindex("-"_1, terminals), "∉"_1)
else if next = merge("/" + "in")then
 lexaction1(next, findindex("-"_1, terminals), "∈"_1)
else if next = "comment"_1 then
 lexaction1("}"_1, findindex("comment"_1, terminals), "}"_1)
else
 let token = 
  if next ∈ "< > ? ≤ ≠ ≥"then">"_1
  else if next ∈ "+-∈ ∉"then"-"_1
  else if next ∈ "* / mod ∪ ∩ \ >> <<"then"*"_1
  else if next ∈ "_^"then"_"_1
  else if next ∈ terminals then next
  else if hasdigit.next then"I"_1 else"W"_1
 let idx = findindex(token, terminals)
 let action = if idx > length.terminals then findindex("W"_1, terminals)else idx
 lexaction1(next, action, next)

Function totext(l:lexaction1)seq.word
let w = 
 if w.l ∈ "/for /if /"then dq.[w.l] + dq+"_1 "
 else if(decodeword.w.l)_1 = (decodeword."/"_1)_1 then
  "merge(" + "/" + "+"
  + dq.[encodeword.subseq(decodeword.w.l, 2, 100)]
  + ")"
 else if w.l = dq_1 then singlequote + w.l + "'_1"else dq.[w.l] + "_1"
let label = if label.l = dq_1 then singlequote + label.l + singlequote else dq.[label.l]
"token(" + w + ", " + toword.tokenno.l + ", attribute:T(" + label
+ "))"

Function getlextable seq.word
{generate the lextable for the Tau compiler. }
let mostfrequentwords = dq + "\, ().:+_seq=a int if-then else Function let word 0 i T][2 use function mytype empty inst"
let wordstoinclude = 
 mostfrequentwords + terminals + "=< > ? ≤ ≠ ≥ >> << in+-∈ * / mod \ ∪ ∩_^'"
 + prepreplacements("", "", "le ≤ ge ≥ ne ≠ and ∧ or ∨ cup ∪ cap ∩ in ∈ nin ∉", 1)
let actionlist = 
 for acc = empty:seq.lexaction1, @e ∈ toseq.asset.wordstoinclude do acc + tolexaction.@e /for(acc)
let t = for acc = empty:seq.seq.word, @e ∈ actionlist do acc + totext.@e /for(acc)
" /br  /br function Wtoken:T int{generated by genlex module in tools}"
+ toword.findindex("W"_1, terminals)
+ " /br  /br function Itoken:T int{generated by genlex module in tools}"
+ toword.findindex("I"_1, terminals)
+ " /br  /br function lextable:T seq.token.T  /br{generated by genlex module in tools} /br["
+ for acc = "", @e ∈ alphasort.t do acc + @e + " /br, "/for(acc >> 1)
+ "]"

function prepreplacements(old:seq.word, new:seq.word, pairs:seq.word, i:int)seq.word
{the pair elements in pair are one after the other. The first element will be merged with a"&".The result is the first elements 
sorted followed by the second elements rearranged to match the sort. }
if i > length.pairs then old + new
else
 let val = merge("/" + pairs_i)
 let j = binarysearch(old, val)
 prepreplacements(subseq(old, 1, -j - 1) + [val] + subseq(old, -j, length.old)
 , subseq(new, 1, -j - 1) + [pairs_(i + 1)] + subseq(new, -j, length.new)
 , pairs
 , i + 2
 ) 