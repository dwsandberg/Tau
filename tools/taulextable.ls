#!/usr/local/bin/tau

Module taulextable

#!/usr/local/bin/tau


run taulextable getlextable



use oseq.word


use seq.char


use seq.lexaction1

use seq.seq.word



use set.word

use stdlib


use UTF8

type lexaction1 is record w:word, tokenno:int, label:word

Function hasdigit(w:word)boolean 
 let l = tointseq.decodeword.w 
  between(l_1, 48, 57)∨ l_1 = toint.hyphenchar ∧ length.l > 1 ∧ between(l_2, 48, 57)


function tokenlist seq.word 
 // tokenlist is from parser generator // 
 ".=():>]-{ } comment, [_^is T if # then else let assert report ∧ ∨ * $wordlist @ A E G F W P N L I K FP"

function actionlist seq.lexaction1 
 // most frequently used words in programs // 
 let mostfrequentwords ="// &quot,(). :+_seq = a int if-then else Function let word 0 i T][ 2 use function mytype @ empty inst"
  let wordstoinclude = mostfrequentwords + tokenlist +"= < > ? ≤ ≠ ≥ >> << in +-∈ ∋ * / mod ∪ ∩_^"+ prepreplacements("","","le ≤ ge ≥ ne ≠ and ∧ or ∨ cup ∪ cap ∩ in ∈ contains ∋", 1)
   @(+, tolexaction, empty:seq.lexaction1, toseq.asset.wordstoinclude)

function tolexaction(next:word)lexaction1 
 // user supplied procedure to convert a word into a lex action // 
 if next in"&quot //"
  then lexaction1(next, 0, next)
  else if next = merge("&"+"le")
  then lexaction1(next, findindex(">"_1, tokenlist),"≤"_1)
  else if next = merge("&"+"ge")
  then lexaction1(next, findindex(">"_1, tokenlist),"≥"_1)
  else if next = merge("&"+"ne")
  then lexaction1(next, findindex(">"_1, tokenlist),"≠"_1)
  else if next = merge("&"+"and")
  then lexaction1(next, findindex("∧"_1, tokenlist),"∧"_1)
  else if next = merge("&"+"or")
  then lexaction1(next, findindex("∨"_1, tokenlist),"∨"_1)
  else if next = merge("&"+"cup")
  then lexaction1(next, findindex("*"_1, tokenlist),"∪"_1)
  else if next = merge("&"+"cap")
  then lexaction1(next, findindex("*"_1, tokenlist),"∩"_1)
  else if next = merge("&"+"contains")
  then lexaction1(next, findindex("-"_1, tokenlist),"∋"_1)
  else if next = merge("&"+"in")
  then lexaction1(next, findindex("-"_1, tokenlist),"∈"_1)
  else 
   let token = 
    if next in". ,():"
    then next 
    else if next in"< > ? ≤ ≠ ≥ >> <<"
    then">"_1 
    else if next in"in +-∈ ∋"
    then"-"_1 
    else if next in"* / mod ∪ ∩"
    then"*"_1 
    else if next in"_^"
    then"_"_1 
    else if next in".)]= {:},([ ∧ ∨ # if then else let assert report @ is"
    then next 
    else if hasdigit.next then"I"_1 else"W"_1 
    lexaction1(next, findindex(token, tokenlist), next)

Function totext(l:lexaction1)seq.word 
 let w = 
   if(decodeword.w.l)_1 =(decodeword."&"_1)_1 
   then"merge(&quot & &quot + &quot"+ encodeword.subseq(decodeword.w.l, 2, 100)+"&quot)"
   else("&quot"+ if w.l ="&quot"_1 then merge("&"+"quot")else w.l)+"&quot_1"
  let label = if label.l ="&quot"_1 then merge("&"+"quot")else label.l 
   "lexaction("+ w +","+ toword.tokenno.l +", &quot"+ label +"&quot_1)"

Function getlextable seq.word 
 // generate the lextable for the Tau compiler. // 
    "&br &br function Wtoken int // generated by genlex module in tools //"+ toword.findindex("W"_1, tokenlist)
   +"&br &br function Itoken int // generated by genlex module in tools //"
   + toword.findindex("I"_1, tokenlist)
   +"&br &br function commenttoken int // generated by genlex module in tools //"
   + toword.findindex("comment"_1, tokenlist)
   +"&br &br function stringtoken int // generated by genlex module in tools //"
   + toword.findindex("$wordlist"_1, tokenlist)
   +"&br &br function lextable seq.lexaction // generated by genlex module in tools // ["
   + @(seperator("&br , ")
   , totext 
   ,"",
  actionlist  )
   +"]"




function prepreplacements(old:seq.word, new:seq.word, pairs:seq.word, i:int)seq.word 
 // the pair elements in pair are one after the other. The first element will be merged with a"&".The result is the first elements sorted followed by the second elements rearranged to match the sort. // 
 if i > length.pairs 
  then old + new 
  else 
   let val = merge("&"+ pairs_i)
   let j = binarysearch(old, val)
    prepreplacements(subseq(old, 1,-j - 1)+ [ val]+ subseq(old,-j, length.old)
    , subseq(new, 1,-j - 1)+ [ pairs_(i + 1)]+ subseq(new,-j, length.new)
    , pairs 
    , i + 2)



